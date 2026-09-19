import CompCert4Lean.Backend.Inlining
import CompCert4Lean.Backend.Inliningspec
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps

/-! Correctness surface for RTL function inlining. -/

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zZero : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev rtlLinker : Linker program :=
  @Linker_prog fundef Unit (@Linker_fundef function) Linker_unit
private abbrev rtlLinkorder (p q : program) : Prop :=
  @linkorder program rtlLinker p q

def match_prog (cfg : InliningConfig) (prog tprog : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (@Linker_fundef function) Linker_unit
    (fun cunit f tf => transf_fundef (funenv_program cfg cunit) f = OK tf)
    (fun x y : Unit => x = y) prog tprog

def agree_regs (F : Val.meminj) (ctx : context) (rs rs' : regset) : Prop :=
  (∀ r, Ple r ctx.mreg → Val.inject F (Regmap.get r rs) (Regmap.get (sreg ctx r) rs')) ∧
  (∀ r, Plt ctx.mreg r → Regmap.get r rs = Vundef)

def val_reg_charact (F : Val.meminj) (ctx : context) (rs' : regset)
    (v : val) (r : reg) : Prop :=
  (Plt ctx.mreg r ∧ v = Vundef) ∨
  (Ple r ctx.mreg ∧ Val.inject F v (Regmap.get (sreg ctx r) rs'))

def loc_private (F : Val.meminj) (m m' : mem) (sp : block) (ofs : Z) : Prop :=
  Mem.perm m' sp ofs .Cur .Freeable ∧
    (∀ b delta, F b = some (sp, delta) →
      ¬ Mem.perm m b (zSub ofs delta) .Max .Nonempty)

def range_private (F : Val.meminj) (m m' : mem) (sp : block) (lo hi : Z) : Prop :=
  ∀ ofs, zLe lo ofs ∧ zLt ofs hi → loc_private F m m' sp ofs

inductive match_globalenvs (prog : program) (F : Val.meminj) (bound : block) : Prop where
  | mk_match_globalenvs
      (DOMAIN : ∀ b, Plt b bound → F b = some (b, zZero))
      (IMAGE : ∀ b1 b2 delta, F b1 = some (b2, delta) → Plt b2 bound → b1 = b2)
      (SYMBOLS : ∀ id b, Genv.find_symbol (Genv.globalenv prog) id = some b → Plt b bound)
      (FUNCTIONS : ∀ b fd, Genv.find_funct_ptr (Genv.globalenv prog) b = some fd → Plt b bound)
      (VARINFOS : ∀ b gv, Genv.find_var_info (Genv.globalenv prog) b = some gv → Plt b bound) :
      match_globalenvs prog F bound

export match_globalenvs (mk_match_globalenvs)

mutual
inductive match_stacks (prog : program) (F : Val.meminj) (m m' : mem) :
    List stackframe → List stackframe → block → Prop where
  | match_stacks_nil : ∀ bound1 bound,
      match_globalenvs prog F bound1 → Ple bound1 bound →
      match_stacks prog F m m' [] [] bound
  | match_stacks_cons : ∀ res f sp pc rs stk f' sp' rs' stk' bound fenv ctx,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
      agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      range_private F m m' sp' (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty → zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      Ple res ctx.mreg → Plt sp' bound →
      match_stacks prog F m m'
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk') bound
  | match_stacks_untailcall : ∀ stk res f' sp' rpc rs' stk' bound ctx,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      range_private F m m' sp' ctx.dstk f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty → zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      ctx.retinfo = some (rpc, res) → Plt sp' bound →
      match_stacks prog F m m' stk
        (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk') bound

inductive match_stacks_inside (prog : program) (F : Val.meminj) (m m' : mem) :
    List stackframe → List stackframe → function → context → block → regset → Prop where
  | match_stacks_inside_base : ∀ stk stk' f' ctx sp' rs',
      match_stacks prog F m m' stk stk' sp' → ctx.retinfo = none → ctx.dstk = zZero →
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined : ∀ res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx',
      match_stacks_inside prog F m m' stk stk' f' ctx' sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx' f f'.fn_code →
      agree_regs F ctx' rs rs' → F sp = some (sp', ctx'.dstk) →
      range_private F m m' sp' (zAdd ctx'.dstk ctx'.mstk) ctx.dstk →
      Ple res ctx'.mreg → ctx.retinfo = some (spc ctx' pc, sreg ctx' res) →
      context_below ctx' ctx → context_stack_call ctx' ctx →
      match_stacks_inside prog F m m'
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk) stk' f' ctx sp' rs'
end

export match_stacks (match_stacks_nil match_stacks_cons match_stacks_untailcall)
export match_stacks_inside (match_stacks_inside_base match_stacks_inside_inlined)

def match_stacks_indStatement : Prop :=
  ∀ (prog : program) (F : Val.meminj) (m m' : mem)
    (P : List stackframe → List stackframe → block → Prop),
    (∀ bound1 bound,
      match_globalenvs prog F bound1 → Ple bound1 bound → P [] [] bound) →
    (∀ res f sp pc rs stk f' sp' rs' stk' bound fenv ctx,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
      agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      range_private F m m' sp' (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty →
        zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      Ple res ctx.mreg → Plt sp' bound →
      P
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk')
        bound) →
    (∀ stk res f' sp' rpc rs' stk' bound ctx,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      range_private F m m' sp' ctx.dstk f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty →
        zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      ctx.retinfo = some (rpc, res) → Plt sp' bound →
      P stk (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk') bound) →
    ∀ l l0 b, match_stacks prog F m m' l l0 b → P l l0 b

def match_stacks_inside_indStatement : Prop :=
  ∀ (prog : program) (F : Val.meminj) (m m' : mem)
    (P : List stackframe → List stackframe → function → context → block → regset → Prop),
    (∀ stk stk' f' ctx sp' rs',
      match_stacks prog F m m' stk stk' sp' →
      ctx.retinfo = none → ctx.dstk = zZero →
      P stk stk' f' ctx sp' rs') →
    (∀ res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx',
      match_stacks_inside prog F m m' stk stk' f' ctx' sp' rs' →
      P stk stk' f' ctx' sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx' f f'.fn_code →
      agree_regs F ctx' rs rs' → F sp = some (sp', ctx'.dstk) →
      range_private F m m' sp' (zAdd ctx'.dstk ctx'.mstk) ctx.dstk →
      Ple res ctx'.mreg → ctx.retinfo = some (spc ctx' pc, sreg ctx' res) →
      context_below ctx' ctx → context_stack_call ctx' ctx →
      P (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk) stk' f' ctx sp' rs') →
    ∀ l l0 f c b r,
      match_stacks_inside prog F m m' l l0 f c b r → P l l0 f c b r

inductive match_states (cfg : InliningConfig) (prog : program) : RTL.state → RTL.state → Prop where
  | match_regular_states : ∀ stk f sp pc rs m stk' f' sp' rs' m' F fenv ctx,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
      agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      Mem.inject F m m' → Mem.valid_block m' sp' →
      range_private F m m' sp' (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty → zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      match_states cfg prog (State stk f (Vptr sp Ptrofs.zero) pc rs m)
        (State stk' f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m')

  | match_call_states : ∀ stk fd args m stk' fd' args' m' cunit F,
      match_stacks prog F m m' stk stk' m'.nextblock →
      rtlLinkorder cunit prog →
      transf_fundef (funenv_program cfg cunit) fd = OK fd' →
      Val.inject_list F args args' →
      Mem.inject F m m' →
      match_states cfg prog (Callstate stk fd args m)
        (Callstate stk' fd' args' m')

  | match_call_regular_states : ∀ stk f vargs m stk' f' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
      context_below ctx' ctx →
      PTree.get pc' f'.fn_code = some (Inop pc1') →
      tr_moves f'.fn_code pc1' (sregs ctx' rargs) (sregs ctx f.fn_params)
        (spc ctx f.fn_entrypoint) →
      list_forall2 (val_reg_charact F ctx' rs') vargs rargs →
      Mem.inject F m m' →
      Mem.valid_block m' sp' →
      range_private F m m' sp' ctx.dstk f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty →
        zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      match_states cfg prog (Callstate stk (Internal f) vargs m)
        (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m')

  | match_return_states : ∀ stk v m stk' v' m' F,
      match_stacks prog F m m' stk stk' m'.nextblock →
      Val.inject F v v' →
      Mem.inject F m m' →
      match_states cfg prog (Returnstate stk v m)
        (Returnstate stk' v' m')

  | match_return_regular_states : ∀ stk v m stk' f' sp' rs' m' F ctx pc' or rinfo,
      match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
      ctx.retinfo = some rinfo →
      PTree.get pc' f'.fn_code = some (inline_return ctx or rinfo) →
      (match or with
        | some r => Val.inject F v (Regmap.get (sreg ctx r) rs')
        | none => v = Vundef) →
      Mem.inject F m m' →
      Mem.valid_block m' sp' →
      range_private F m m' sp' ctx.dstk f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty →
        zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      match_states cfg prog (Returnstate stk v m)
        (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m')

export match_states
  (match_regular_states match_call_states match_call_regular_states
    match_return_states match_return_regular_states)

def measure : RTL.state → Nat
  | State _ _ _ _ _ _ => 1
  | Callstate _ _ _ _ => 0
  | Returnstate _ _ _ => 0

/-! Later-proof statement descriptors. -/

def Plt_Ple_decStatement : Type :=
  ∀ p q : positive, Support.Sumbool (Plt p q) (Ple q p)

def agree_regs_incrStatement : Prop :=
  ∀ F ctx rs1 rs2 F', agree_regs F ctx rs1 rs2 → inject_incr F F' → agree_regs F' ctx rs1 rs2

def agree_regs_initStatement : Prop :=
  ∀ F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs

def agree_regs_init_regsStatement : Prop :=
  ∀ F ctx rl vl vl', Val.inject_list F vl vl' →
    (∀ r, r ∈ rl → Ple r ctx.mreg) →
    agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl))

def agree_regs_invariantStatement : Prop :=
  ∀ F ctx rs rs1 rs2, agree_regs F ctx rs rs1 →
    (∀ r, Ple ctx.dreg r → Plt r (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) →
      Regmap.get r rs2 = Regmap.get r rs1) →
    agree_regs F ctx rs rs2

def agree_set_regStatement : Prop :=
  ∀ F ctx rs rs' r v v', agree_regs F ctx rs rs' → Val.inject F v v' → Ple r ctx.mreg →
    agree_regs F ctx (Regmap.set r v rs) (Regmap.set (sreg ctx r) v' rs')

def agree_set_reg_undefStatement : Prop :=
  ∀ F ctx rs rs' r v', agree_regs F ctx rs rs' →
    agree_regs F ctx (Regmap.set r Vundef rs) (Regmap.set (sreg ctx r) v' rs')

def agree_set_reg_undef'Statement : Prop :=
  ∀ F ctx rs rs' r, agree_regs F ctx rs rs' → agree_regs F ctx (Regmap.set r Vundef rs) rs'

def agree_val_regStatement : Prop :=
  ∀ F ctx rs rs' r, agree_regs F ctx rs rs' →
    Val.inject F (Regmap.get r rs) (Regmap.get (sreg ctx r) rs')

def agree_val_reg_genStatement : Prop :=
  ∀ F ctx rs rs' r, agree_regs F ctx rs rs' →
    val_reg_charact F ctx rs' (Regmap.get r rs) r

def agree_val_regsStatement : Prop :=
  ∀ F ctx rs rs' rl, agree_regs F ctx rs rs' →
    Val.inject_list F (rl.map (fun r => Regmap.get r rs))
      (List.map (fun r => Regmap.get (sreg ctx r) rs') rl)

def agree_val_regs_genStatement : Prop :=
  ∀ F ctx rs rs' rl, agree_regs F ctx rs rs' →
    list_forall2 (val_reg_charact F ctx rs') (rl.map (fun r => Regmap.get r rs)) rl

def align_unchangedStatement : Prop :=
  ∀ n amount : Z, zLt zZero amount → ZArith.BinInt.Z.divide amount n → align n amount = n

def context_below_ltStatement : Prop :=
  ∀ ctx1 ctx2 r, context_below ctx1 ctx2 → Ple r ctx1.mreg →
    Plt (sreg ctx1 r) ctx2.dreg
def find_function_agreeStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ ros rs fd F ctx rs' bound,
      find_function (Genv.globalenv prog) ros rs = some fd →
      agree_regs F ctx rs rs' → match_globalenvs prog F bound →
      ∃ cu fd', find_function (Genv.globalenv tprog) (sros ctx ros) rs' = some fd' ∧
        transf_fundef (funenv_program cfg cu) fd = OK fd' ∧ rtlLinkorder cu prog

def find_inlined_functionStatement : Prop :=
  ∀ (prog : program) (fenv : funenv) (id : ident)
    (rs : regset) (fd : fundef) (f : function),
    fenv_compat prog fenv →
    find_function (Genv.globalenv prog) (.inr id) rs = some fd →
    PTree.get id fenv = some f → fd = Internal f

def function_ptr_translatedStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ b f, Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu f', Genv.find_funct_ptr (Genv.globalenv tprog) b = some f' ∧
        transf_fundef (funenv_program cfg cu) f = OK f' ∧ rtlLinkorder cu prog

def functions_translatedStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ v f, Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ cu f', Genv.find_funct (Genv.globalenv tprog) v = some f' ∧
        transf_fundef (funenv_program cfg cu) f = OK f' ∧ rtlLinkorder cu prog

def match_globalenvs_preserves_globalsStatement : Prop :=
  ∀ prog F bound, match_globalenvs prog F bound →
    CompCert4Lean.Common.Events.meminj_preserves_globals fundef Unit
      (Genv.globalenv prog) F

def match_stacks_boundStatement : Prop :=
  ∀ prog F m m' stk stk' bound bound1,
    match_stacks prog F m m' stk stk' bound → Ple bound bound1 →
      match_stacks prog F m m' stk stk' bound1

def match_stacks_emptyStatement : Prop :=
  ∀ prog F m m' stk stk' bound,
    match_stacks prog F m m' stk stk' bound → stk = [] → stk' = []

def match_stacks_extcallStatement : Prop :=
  ∀ prog F1 F2 m1 m2 m1' m2',
    (∀ b ofs p, Mem.valid_block m1 b → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    (∀ b ofs p, Mem.valid_block m1' b → Mem.perm m2' b ofs .Max p →
      Mem.perm m1' b ofs .Max p) →
    Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2' →
    Mem.inject F1 m1 m1' →
    inject_incr F1 F2 →
    inject_separated F1 F2 m1 m1' →
    ∀ stk stk' bound,
      match_stacks prog F1 m1 m1' stk stk' bound →
      Ple bound m1'.nextblock →
      match_stacks prog F2 m2 m2' stk stk' bound

def match_stacks_globalenvsStatement : Prop :=
  ∀ prog F m m' stk stk' bound,
    match_stacks prog F m m' stk stk' bound → ∃ b, match_globalenvs prog F b
def match_stacks_inside_alloc_leftStatement : Prop :=
  ∀ prog F m m' stk stk' f' ctx sp' rs',
    match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
    ∀ sz m1 b F1 delta,
      Mem.alloc m zZero sz = (m1, b) → inject_incr F F1 →
      F1 b = some (sp', delta) →
      (∀ b1, b1 ≠ b → F1 b1 = F b1) →
      zLe ctx.dstk delta →
      match_stacks_inside prog F1 m1 m' stk stk' f' ctx sp' rs'

def match_stacks_inside_emptyStatement : Prop :=
  ∀ prog F m m' stk stk' f ctx sp rs,
    match_stacks_inside prog F m m' stk stk' f ctx sp rs →
    stk = [] → stk' = [] ∧ ctx.retinfo = none

def match_stacks_inside_extcallStatement : Prop :=
  ∀ prog F1 F2 m1 m2 m1' m2',
    (∀ b ofs p, Mem.valid_block m1 b → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    (∀ b ofs p, Mem.valid_block m1' b → Mem.perm m2' b ofs .Max p →
      Mem.perm m1' b ofs .Max p) →
    Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2' →
    Mem.inject F1 m1 m1' →
    inject_incr F1 F2 →
    inject_separated F1 F2 m1 m1' →
    ∀ stk stk' f' ctx sp' rs',
      match_stacks_inside prog F1 m1 m1' stk stk' f' ctx sp' rs' →
      Plt sp' m1'.nextblock →
      match_stacks_inside prog F2 m2 m2' stk stk' f' ctx sp' rs'

def match_stacks_inside_globalenvsStatement : Prop :=
  ∀ prog F m m' stk stk' f ctx sp rs,
    match_stacks_inside prog F m m' stk stk' f ctx sp rs →
    ∃ b, match_globalenvs prog F b

def match_stacks_inside_globalsStatement : Prop :=
  ∀ prog F m m' stk stk' f ctx sp rs,
    match_stacks_inside prog F m m' stk stk' f ctx sp rs →
    CompCert4Lean.Common.Events.meminj_preserves_globals fundef Unit
      (Genv.globalenv prog) F

def match_stacks_inside_inlined_tailcallStatement : Prop :=
  ∀ prog fenv F m m' stk stk' f' ctx sp rs ctx' f,
    match_stacks_inside prog F m m' stk stk' f' ctx sp rs →
    context_below ctx ctx' → context_stack_tailcall ctx f ctx' →
    ctx'.retinfo = ctx.retinfo →
    range_private F m m' sp ctx.dstk f'.fn_stacksize →
    tr_funbody fenv f'.fn_stacksize ctx' f f'.fn_code →
    match_stacks_inside prog F m m' stk stk' f' ctx' sp rs

def match_stacks_inside_invariantStatement : Prop :=
  ∀ prog F m m' F1 m1 m1',
    inject_incr F F1 →
    ∀ stk stk' f' ctx sp rs1,
      match_stacks_inside prog F m m' stk stk' f' ctx sp rs1 →
      ∀ rs2,
        (∀ r, Plt r ctx.dreg → Regmap.get r rs2 = Regmap.get r rs1) →
        (∀ b1 b2 delta, F1 b1 = some (b2, delta) → Ple b2 sp →
          F b1 = some (b2, delta)) →
        (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → Ple b2 sp →
          Mem.perm m1 b1 ofs .Max .Nonempty → Mem.perm m b1 ofs .Max .Nonempty) →
        (∀ b ofs, Ple b sp → Mem.perm m' b ofs .Cur .Freeable →
          Mem.perm m1' b ofs .Cur .Freeable) →
        (∀ b ofs k p, Ple b sp → Mem.perm m1' b ofs k p →
          Mem.perm m' b ofs k p) →
        match_stacks_inside prog F1 m1 m1' stk stk' f' ctx sp rs2

def match_stacks_inside_set_regStatement : Prop :=
  ∀ prog F m m' stk stk' f ctx sp rs r v,
    match_stacks_inside prog F m m' stk stk' f ctx sp rs →
    match_stacks_inside prog F m m' stk stk' f ctx sp (Regmap.set (sreg ctx r) v rs)

def match_stacks_inside_set_resStatement : Prop :=
  ∀ prog F m m' stk stk' f ctx sp rs res v,
    match_stacks_inside prog F m m' stk stk' f ctx sp rs →
    match_stacks_inside prog F m m' stk stk' f ctx sp
      (regmap_setres (sbuiltinres ctx res) v rs)

def match_stacks_inside_storeStatement : Prop :=
  ∀ prog F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1',
    match_stacks_inside prog F m m' stk stk' f' ctx sp' rs' →
    Mem.store chunk m b ofs v = some m1 → Mem.store chunk' m' b' ofs' v' = some m1' →
    match_stacks_inside prog F m1 m1' stk stk' f' ctx sp' rs'

def match_stacks_invariantStatement : Prop :=
  ∀ prog F m m' F1 m1 m1',
    inject_incr F F1 →
    ∀ stk stk' bound,
      match_stacks prog F m m' stk stk' bound →
      ∀ (INJ : ∀ b1 b2 delta, F1 b1 = some (b2, delta) → Plt b2 bound →
        F b1 = some (b2, delta))
        (PERM1 : ∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → Plt b2 bound →
          Mem.perm m1 b1 ofs .Max .Nonempty → Mem.perm m b1 ofs .Max .Nonempty)
        (PERM2 : ∀ b ofs, Plt b bound → Mem.perm m' b ofs .Cur .Freeable →
          Mem.perm m1' b ofs .Cur .Freeable)
        (PERM3 : ∀ b ofs k p, Plt b bound → Mem.perm m1' b ofs k p →
          Mem.perm m' b ofs k p),
        match_stacks prog F1 m1 m1' stk stk' bound

def min_alignment_soundStatement : Prop :=
  ∀ sz n, ZArith.BinInt.Z.divide (min_alignment sz) n → Mem.inj_offset_aligned n sz

def range_private_alloc_leftStatement : Prop :=
  ∀ F m m' sp' base hi sz m1 sp F1,
    range_private F m m' sp' base hi → Mem.alloc m zZero sz = (m1, sp) →
    F1 sp = some (sp', base) → (∀ b, b ≠ sp → F1 b = F b) →
    range_private F1 m1 m' sp' (zAdd base (ZArith.BinInt.Z.max sz zZero)) hi

def range_private_extcallStatement : Prop :=
  ∀ F F' m1 m2 m1' m2' sp base hi,
    range_private F m1 m1' sp base hi →
    (∀ b ofs p, Mem.valid_block m1 b → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' →
    Mem.inject F m1 m1' → inject_incr F F' →
    inject_separated F F' m1 m1' → Mem.valid_block m1' sp →
    range_private F' m2 m2' sp base hi

def range_private_free_leftStatement : Prop :=
  ∀ F m m' sp base sz hi b m1,
    range_private F m m' sp (zAdd base (ZArith.BinInt.Z.max sz zZero)) hi →
    Mem.free m b zZero sz = some m1 → F b = some (sp, base) → Mem.inject F m m' →
    range_private F m1 m' sp base hi

def range_private_invariantStatement : Prop :=
  ∀ F m m' sp lo hi F1 m1 m1', range_private F m m' sp lo hi →
    (∀ b delta ofs, F1 b = some (sp, delta) →
      Mem.perm m1 b ofs .Max .Nonempty →
      (zLe lo (zAdd ofs delta) ∧ zLt (zAdd ofs delta) hi) →
      F b = some (sp, delta) ∧ Mem.perm m b ofs .Max .Nonempty) →
    (∀ ofs, Mem.perm m' sp ofs .Cur .Freeable →
      Mem.perm m1' sp ofs .Cur .Freeable) →
    range_private F1 m1 m1' sp lo hi

def range_private_permsStatement : Prop :=
  ∀ F m m' sp lo hi, range_private F m m' sp lo hi →
    Mem.range_perm m' sp lo hi .Cur .Freeable

def senv_preservedStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog)) (Genv.to_senv (Genv.globalenv tprog))

def sig_function_translatedStatement : Prop :=
  ∀ cfg cunit f f', transf_fundef (funenv_program cfg cunit) f = OK f' → funsig f' = funsig f

def sreg_below_diffStatement : Prop :=
  ∀ ctx r r', Plt r' ctx.dreg → sreg ctx r ≠ r'

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (cfg : InliningConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ (S1 : RTL.state) (t : trace) (S2 : RTL.state),
      step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) S1 t S2 →
      ∀ S1', match_states cfg prog S1 S1' →
        (∃ S2', plus (step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi) (Genv.globalenv tprog) S1' t S2' ∧
          match_states cfg prog S2 S2') ∨
        (measure S2 < measure S1 ∧ t = E0 ∧ match_states cfg prog S2 S1')

def symbols_preservedStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ s, Genv.find_symbol (Genv.globalenv tprog) s = Genv.find_symbol (Genv.globalenv prog) s

def tr_builtin_argStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ F bound ctx rs rs' sp sp' m m' a v,
      match_globalenvs prog F bound → agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      Mem.inject F m m' →
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        (Vptr sp Ptrofs.zero) m a v →
      ∃ v', eval_builtin_arg (Genv.to_senv (Genv.globalenv tprog)) (fun r => Regmap.get r rs')
        (Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v' ∧ Val.inject F v v'

def tr_builtin_argsStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ F bound ctx rs rs' sp sp' m m' al vl,
      match_globalenvs prog F bound → agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      Mem.inject F m m' →
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        (Vptr sp Ptrofs.zero) m al vl →
      ∃ vl', eval_builtin_args (Genv.to_senv (Genv.globalenv tprog)) (fun r => Regmap.get r rs')
        (Vptr sp' Ptrofs.zero) m' (al.map (sbuiltinarg ctx)) vl' ∧ Val.inject_list F vl vl'

def tr_funbody_invStatement : Prop :=
  ∀ fenv sz ctx (f : function) c pc i, tr_funbody fenv sz ctx f c →
    PTree.get pc f.fn_code = some i →
    tr_instr fenv sz ctx pc i c

def tr_moves_init_regsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : program) F (stk : List stackframe) (f : function) (sp : val) (m : mem)
    ctx1 ctx2,
    context_below ctx1 ctx2 →
    ∀ rdsts rsrcs vl pc1 pc2 rs1,
      tr_moves f.fn_code pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 →
      (∀ r, r ∈ rdsts → Ple r ctx2.mreg) →
      list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs →
      ∃ rs2,
        star (step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
          (Genv.globalenv tprog) (State stk f sp pc1 rs1 m) E0
          (State stk f sp pc2 rs2 m) ∧
        agree_regs F ctx2 (init_regs vl rdsts) rs2 ∧
        (∀ r, Plt r ctx2.dreg → Regmap.get r rs2 = Regmap.get r rs1)

def transf_final_statesStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog : program),
    ∀ st1 st2 r, match_states cfg prog st1 st2 → final_state st1 r → final_state st2 r

def transf_initial_statesStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ st1, initial_state prog st1 → ∃ st2, initial_state tprog st2 ∧ match_states cfg prog st1 st2

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (cfg : InliningConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    forward_simulation
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

def transf_program_matchStatement : Prop :=
  ∀ cfg prog tprog, transf_program cfg prog = OK tprog → match_prog cfg prog tprog

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.RTL

private theorem transf_globdefs_match
    {A B V : Type} [LA : Linker A] [LV : Linker V]
    (transf_fun : A → res B) (p : program A V)
    (match_fundef : program A V → A → B → Prop)
    (hmatch : ∀ f tf, transf_fun f = .OK tf → match_fundef p f tf) :
    ∀ (l : List (ident × globdef A V)) (defs : List (ident × globdef B V)),
      transf_globdefs (fun _ f => transf_fun f) (fun _ v => .OK v) l = .OK defs →
      list_forall2
        (match_ident_globdef match_fundef Eq p)
        l defs := by
  intro l
  induction l with
  | nil =>
      intro defs hdefs
      simp [transf_globdefs] at hdefs
      subst defs
      exact list_forall2_nil _
  | cons hd tl ih =>
      intro defs hdefs
      cases hd with
      | mk id gd =>
          cases gd with
          | Gfun f =>
              cases htf : transf_fun f with
              | Error msg => simp [transf_globdefs, htf] at hdefs
              | OK tf =>
                  cases htail : transf_globdefs
                      (fun _ f => transf_fun f) (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, htf, htail] at hdefs
                  | OK defsTail =>
                      simp [transf_globdefs, htf, htail] at hdefs
                      subst defs
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · apply match_globdef.match_globdef_fun (ctx' := p)
                          · exact linkorder_refl _
                          · exact hmatch f tf htf
                      · exact ih defsTail htail
          | Gvar v =>
              cases v with
              | mk info init readonly volatile =>
                  cases htail : transf_globdefs
                      (fun _ f => transf_fun f) (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, transf_globvar, htail] at hdefs
                  | OK defsTail =>
                      simp [transf_globdefs, transf_globvar, htail] at hdefs
                      subst defs
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · apply match_globdef.match_globdef_var
                          exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                      · exact ih defsTail htail

private theorem match_transform_partial_program_local
    {A B V : Type} [LA : Linker A] [LV : Linker V]
    (transf_fun : A → res B) (p : program A V) (tp : program B V)
    (match_fundef : program A V → A → B → Prop)
    (hmatch : ∀ f tf, transf_fun f = .OK tf → match_fundef p f tf) :
    transform_partial_program transf_fun p = .OK tp →
      match_program match_fundef Eq p tp := by
  intro h
  unfold transform_partial_program transform_partial_program2 at h
  unfold match_program match_program_gen
  cases hdefs : transf_globdefs (fun _ f => transf_fun f) (fun _ v => .OK v) p.prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp [hdefs] at h
      subst tp
      constructor
      · exact transf_globdefs_match transf_fun p match_fundef hmatch p.prog_defs defs hdefs
      · exact ⟨rfl, rfl⟩

theorem transf_program_match : transf_program_matchStatement := by
  intro cfg prog tprog h
  unfold CompCert4Lean.Backend.Inlining.transf_program at h
  unfold match_prog
  exact @match_transform_partial_program_local
    fundef fundef Unit
    (Linker_fundef function) Linker_unit
    (transf_fundef (funenv_program cfg prog)) prog tprog
    (fun cunit f tf => transf_fundef (funenv_program cfg cunit) f = .OK tf)
    (by intro f tf htf; exact htf) h

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.RTL

private theorem inlining_ptree_get_set0_same {A : Type} (i : positive) (x : A) :
    PTree.get' i (PTree.set0 i x) = some x := by
  induction i <;> simp [PTree.get', PTree.set0, *]

private theorem inlining_ptree_get_set'_same {A : Type} (i : positive) (x : A)
    (m : PTree.tree' A) :
    PTree.get' i (PTree.set' i x m) = some x := by
  induction i generalizing m <;> cases m <;>
    simp [PTree.get', PTree.set', inlining_ptree_get_set0_same, *]

private theorem inlining_ptree_get_set_same {A : Type} (i : positive) (x : A)
    (m : PTree.t A) :
    PTree.get i (PTree.set i x m) = some x := by
  cases m <;>
    simp [PTree.get, PTree.set, inlining_ptree_get_set0_same,
      inlining_ptree_get_set'_same]

private theorem inlining_ptree_get_set0_other {A : Type} (i j : positive) (x : A)
    (h : i ≠ j) : PTree.get' i (PTree.set0 j x) = none := by
  induction j generalizing i with
  | xH => cases i <;> simp_all [PTree.get', PTree.set0]
  | xI j ih => cases i <;> simp_all [PTree.get', PTree.set0]
  | xO j ih => cases i <;> simp_all [PTree.get', PTree.set0]

private theorem inlining_ptree_get_set'_other {A : Type} (i j : positive) (x : A)
    (m : PTree.tree' A) (h : i ≠ j) :
    PTree.get' i (PTree.set' j x m) = PTree.get' i m := by
  induction j generalizing i m with
  | xH => cases i <;> cases m <;> simp_all [PTree.get', PTree.set']
  | xI j ih =>
      cases i <;> cases m <;>
        simp_all [PTree.get', PTree.set', inlining_ptree_get_set0_other]
  | xO j ih =>
      cases i <;> cases m <;>
        simp_all [PTree.get', PTree.set', inlining_ptree_get_set0_other]

private theorem inlining_ptree_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PTree.t A) (h : i ≠ j) :
    PTree.get i (PTree.set j x m) = PTree.get i m := by
  cases m <;>
    simp [PTree.get, PTree.set, inlining_ptree_get_set0_other,
      inlining_ptree_get_set'_other, h]

private theorem inlining_symbols_add_globals
    {A B V : Type} (ge : Genv.t A V) (tge : Genv.t B V)
    (hnext : tge.genv_next = ge.genv_next)
    (hsym : ∀ s, Genv.find_symbol tge s = Genv.find_symbol ge s) :
    ∀ (l : List (ident × globdef A V)) (tl : List (ident × globdef B V)),
      list_forall2 (fun x y => x.1 = y.1) l tl →
      ∀ s, Genv.find_symbol (Genv.add_globals tge tl) s =
        Genv.find_symbol (Genv.add_globals ge l) s := by
  intro l tl hlist
  induction hlist generalizing ge tge with
  | nil =>
      simpa [Genv.add_globals] using hsym
  | cons x y hxy htail ih =>
      cases x with
      | mk id gd =>
          cases y with
          | mk tid tgd =>
              have hid : id = tid := hxy
              subst tid
              have hnext' :
                  (Genv.add_global tge (id, tgd)).genv_next =
                    (Genv.add_global ge (id, gd)).genv_next := by
                change PArith.BinPos.Pos.succ tge.genv_next =
                  PArith.BinPos.Pos.succ ge.genv_next
                exact congrArg _ hnext
              have hsym' : ∀ s,
                  Genv.find_symbol (Genv.add_global tge (id, tgd)) s =
                    Genv.find_symbol (Genv.add_global ge (id, gd)) s := by
                intro s
                by_cases hs : s = id
                · subst s
                  change PTree.get id (PTree.set id tge.genv_next tge.genv_symb) =
                    PTree.get id (PTree.set id ge.genv_next ge.genv_symb)
                  exact (inlining_ptree_get_set_same id tge.genv_next tge.genv_symb).trans
                    ((congrArg some hnext).trans
                      (inlining_ptree_get_set_same id ge.genv_next ge.genv_symb).symm)
                · change PTree.get s (PTree.set id tge.genv_next tge.genv_symb) =
                    PTree.get s (PTree.set id ge.genv_next ge.genv_symb)
                  exact (inlining_ptree_get_set_other s id tge.genv_next tge.genv_symb hs).trans
                    ((hsym s).trans
                      (inlining_ptree_get_set_other s id ge.genv_next ge.genv_symb hs).symm)
              simpa [Genv.add_globals] using ih
                (Genv.add_global ge (id, gd)) (Genv.add_global tge (id, tgd)) hnext' hsym'

private theorem inlining_list_forall2_fst
    {I A B : Type} {R : (I × A) → (I × B) → Prop}
    {l : List (I × A)} {tl : List (I × B)}
    (h : list_forall2 R l tl)
    (hfst : ∀ x y, R x y → x.1 = y.1) :
    list_forall2 (fun x y => x.1 = y.1) l tl := by
  induction h with
  | nil => exact list_forall2.nil _
  | cons x y hxy htail ih => exact list_forall2.cons x y (hfst x y hxy) ih

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg prog tprog hmatch s
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases hmatch with ⟨hdefs, hmain, hpublic⟩
  have hdefs' := inlining_list_forall2_fst hdefs (fun x y hxy => hxy.1)
  unfold Genv.globalenv
  apply inlining_symbols_add_globals
    (Genv.empty_genv RTL.fundef Unit prog.prog_public)
    (Genv.empty_genv RTL.fundef Unit tprog.prog_public)
  · rfl
  · intro id
    simp [Genv.empty_genv, hpublic]
  · exact hdefs'

end CompCert4Lean.Backend.Inliningproof

/-
namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inlining_find_def_add_global_same {F V : Type}
    (ge : Genv.t F V) (id : ident) (gd : globdef F V) :
    Genv.find_def (Genv.add_global ge (id, gd)) ge.genv_next = some gd := by
  unfold Genv.find_def Genv.add_global
  exact inlining_ptree_get_set_same ge.genv_next gd ge.genv_defs

private theorem inlining_find_def_add_global_other {F V : Type}
    (ge : Genv.t F V) (id : ident) (gd : globdef F V)
    (b : CompCert4Lean.Common.Values.block)
    (h : b ≠ ge.genv_next) :
    Genv.find_def (Genv.add_global ge (id, gd)) b = Genv.find_def ge b := by
  unfold Genv.find_def Genv.add_global
  exact inlining_ptree_get_set_other b ge.genv_next gd ge.genv_defs h

private theorem inlining_function_ptrs_add_globals
    {C A B V : Type} [LC : Linker C]
    (match_fun : C → A → B → Prop) (match_var : V → V → Prop) (ctx : C)
    (ge : Genv.t A V) (tge : Genv.t B V)
    (hnext : tge.genv_next = ge.genv_next)
    (hptr : ∀ b f, Genv.find_funct_ptr ge b = some f →
      ∃ cu tf, Genv.find_funct_ptr tge b = some tf ∧
        match_fun cu f tf ∧ linkorder cu ctx) :
    ∀ (l : List (ident × globdef A V)) (tl : List (ident × globdef B V)),
      list_forall2 (match_ident_globdef match_fun match_var ctx) l tl →
      ∀ b f, Genv.find_funct_ptr (Genv.add_globals ge l) b = some f →
        ∃ cu tf, Genv.find_funct_ptr (Genv.add_globals tge tl) b = some tf ∧
          match_fun cu f tf ∧ linkorder cu ctx := by
  intro l tl hlist
  induction hlist generalizing ge tge hptr with
  | nil =>
      simpa [Genv.add_globals] using hptr
  | cons x y hxy htail ih =>
      cases x with
      | mk id gd =>
          cases y with
          | mk tid tgd =>
              have hid : id = tid := hxy.1
              subst tid
              have hnext' :
                  (Genv.add_global tge (id, tgd)).genv_next =
                    (Genv.add_global ge (id, gd)).genv_next := by
                change PArith.BinPos.Pos.succ tge.genv_next =
                  PArith.BinPos.Pos.succ ge.genv_next
                exact congrArg _ hnext
              intro b f hfind
              by_cases hb : b = ge.genv_next
              · subst b
                cases gd with
                | Gfun f0 =>
                    cases tgd with
                    | Gfun tf0 =>
                        have hnow :
                            Genv.find_funct_ptr (Genv.add_global ge (id, Gfun f0))
                              ge.genv_next = some f := by
                          simpa [Genv.add_globals] using hfind
                        unfold Genv.find_funct_ptr at hnow
                        rw [inlining_find_def_add_global_same] at hnow
                        have hf : f0 = f := Option.some.inj (by simpa using hnow)
                        subst f
                        cases hxy.2 with
                        | match_globdef_fun cu _ _ hlink hfun =>
                            refine ⟨cu, tf0, ?_, hfun, hlink⟩
                            have ht :
                                Genv.find_funct_ptr (Genv.add_global tge (id, Gfun tf0))
                                  tge.genv_next = some tf0 := by
                              unfold Genv.find_funct_ptr
                              rw [inlining_find_def_add_global_same]
                              rfl
                            simpa only [hnext] using ht
                    | Gvar tv => cases hxy.2
                | Gvar v =>
                    have hnow :
                        Genv.find_funct_ptr (Genv.add_global ge (id, Gvar v))
                          ge.genv_next = some f := by
                      simpa [Genv.add_globals] using hfind
                    unfold Genv.find_funct_ptr at hnow
                    rw [inlining_find_def_add_global_same] at hnow
                    simp at hnow
              · have hbt : b ≠ tge.genv_next := by simpa only [hnext] using hb
                have hfind' : Genv.find_funct_ptr ge b = some f := by
                  unfold Genv.find_funct_ptr at hfind ⊢
                  rw [inlining_find_def_add_global_other] at hfind
                  exact hfind
                have hptr' : ∀ b f,
                    Genv.find_funct_ptr (Genv.add_global ge (id, gd)) b = some f →
                      ∃ cu tf, Genv.find_funct_ptr (Genv.add_global tge (id, tgd)) b = some tf ∧
                        match_fun cu f tf ∧ linkorder cu ctx := by
                  intro b' f' h'
                  have hb' : b' ≠ ge.genv_next := by
                    intro hbeq
                    subst b'
                    cases gd <;>
                      simp [Genv.find_funct_ptr, inlining_find_def_add_global_same] at h'
                  have hbt' : b' ≠ tge.genv_next := by simpa only [hnext] using hb'
                  have hbase : Genv.find_funct_ptr ge b' = some f' := by
                    unfold Genv.find_funct_ptr at h' ⊢
                    rw [inlining_find_def_add_global_other] at h'
                    exact h'
                  rcases hptr b' f' hbase with ⟨cu, tf, htf, hfun, hlink⟩
                  refine ⟨cu, tf, ?_, hfun, hlink⟩
                  unfold Genv.find_funct_ptr at htf ⊢
                  rw [inlining_find_def_add_global_other]
                  exact htf
                apply ih (Genv.add_global ge (id, gd))
                  (Genv.add_global tge (id, tgd)) hnext' hptr' b f
                simpa [Genv.add_globals] using hfind

theorem function_ptr_translated : function_ptr_translatedStatement := by
  letI : Linker RTL.program := by
    exact @Linker_prog RTL.fundef Unit (Linker_fundef RTL.function) Linker_unit
  intro cfg prog tprog hmatch b f hfind
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases hmatch with ⟨hdefs, hmain, hpublic⟩
  unfold Genv.globalenv
  apply inlining_function_ptrs_add_globals
    (fun cu f tf => transf_fundef (funenv_program cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog
    (Genv.empty_genv RTL.fundef Unit prog.prog_public)
    (Genv.empty_genv RTL.fundef Unit tprog.prog_public)
  · rfl
  · intro b f h
    simp [Genv.find_funct_ptr, Genv.find_def, Genv.empty_genv] at h
  · exact hdefs
  · exact hfind

end CompCert4Lean.Backend.Inliningproof
-/

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inlining_senv_symbol_add_global
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ id' id ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ id' id ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem inlining_senv_match_genvs_add_global
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (g1 g2 : globdef fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact inlining_senv_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation (globdef fundef Unit)
      b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation (globdef fundef Unit)
      b ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hg
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem inlining_senv_match_genvs_add_globals
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (xs ys : List (ident × globdef fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 ge2 : Genv.t fundef Unit) (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid ∧ R ag bg at hab
      rcases hab with ⟨rfl, hab⟩
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      simpa using (inlining_senv_match_genvs_add_global R ge1 ge2 aid ag bg hm hab)

private theorem inlining_senv_add_globals_public
    (ge : Genv.t fundef Unit) (gl : List (ident × globdef fundef Unit)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons idg gl ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge idg)

private theorem inlining_senv_globalenvs_match
    (cfg : InliningConfig) (prog tprog : program)
    (hm : match_prog cfg prog tprog) :
    Genv.match_genvs
      (@match_globdef (program fundef Unit) fundef Unit fundef Unit
        (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
        (fun (cunit : program fundef Unit) f tf =>
          transf_fundef (funenv_program cfg cunit) f = .OK tf)
        (fun x y : Unit => x = y) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  let R : globdef fundef Unit → globdef fundef Unit → Prop :=
    @match_globdef (program fundef Unit) fundef Unit fundef Unit
      (@Linker_prog fundef Unit (@Linker_fundef function) Linker_unit)
      (fun (cunit : program fundef Unit) f tf =>
        transf_fundef (funenv_program cfg cunit) f = .OK tf)
      (fun x y : Unit => x = y) prog
  unfold match_prog match_program match_program_gen at hm
  have hempty : Genv.match_genvs R
      (Genv.empty_genv fundef Unit prog.prog_public)
      (Genv.empty_genv fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist_of : ∀ (xs ys : List (ident × globdef fundef Unit)),
      list_forall2 (@match_ident_globdef (program fundef Unit) fundef Unit fundef Unit
        (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
        (fun (cunit : program fundef Unit) f tf =>
          transf_fundef (funenv_program cfg cunit) f = .OK tf)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · constructor
          · exact hab.1
          · simpa [R] using hab.2
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  exact inlining_senv_match_genvs_add_globals R prog.prog_defs tprog.prog_defs
    hlist _ _ hempty

theorem senv_preserved : senv_preservedStatement := by
  intro cfg prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    exact symbols_preserved cfg prog tprog hm id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact inlining_senv_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact inlining_senv_add_globals_public _ _
    unfold Genv.public_symbol
    rw [symbols_preserved cfg prog tprog hm id]
    unfold match_prog match_program match_program_gen at hm
    rw [ht, hp, hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    have hg := inlining_senv_globalenvs_match cfg prog tprog hm
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inlining_function_ptr_translated_local
    (cfg : InliningConfig) (prog tprog : program)
    (hm : match_prog cfg prog tprog) :
    ∀ b f, Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu f', Genv.find_funct_ptr (Genv.globalenv tprog) b = some f' ∧
        transf_fundef (funenv_program cfg cu) f = .OK f' ∧ rtlLinkorder cu prog := by
  intro b f hfind
  have hg := inlining_senv_globalenvs_match cfg prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases hsrc : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [hsrc] at hfind
  | some gd =>
      cases gd with
      | Gfun f0 =>
          simp [hsrc] at hfind
          subst f0
          have hrel := hg.mge_defs b
          rw [hsrc] at hrel
          cases htgt : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none => rw [htgt] at hrel; cases hrel
          | some tgd =>
              rw [htgt] at hrel
              cases tgd with
              | Gfun tf =>
                  cases hrel with
                  | some _ _ hfun =>
                      cases hfun with
                      | match_globdef_fun cu _ _ horder htrans =>
                          refine ⟨cu, tf, ?_, htrans, horder⟩
                          simp [Genv.find_funct_ptr, Genv.find_def, htgt]
              | Gvar v =>
                  cases hrel with
                  | some _ _ hfun => cases hfun
      | Gvar v => simp [hsrc] at hfind

theorem functions_translated : functions_translatedStatement := by
  intro cfg prog tprog hm v f hfind
  cases v with
  | Vptr b ofs =>
      by_cases heq : CompCert4Lean.Lib.Integers.Ptrofs.eq ofs
          CompCert4Lean.Lib.Integers.Ptrofs.zero = true
      · unfold Genv.find_funct at hfind ⊢
        simp [heq] at hfind ⊢
        have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some f := hfind
        obtain ⟨cu, tf, hptrt, htrans, horder⟩ :=
          inlining_function_ptr_translated_local cfg prog tprog hm b f hptr
        exact ⟨cu, tf, hptrt, htrans, horder⟩
      · unfold Genv.find_funct at hfind
        simp [heq] at hfind
  | Vundef => simp [Genv.find_funct] at hfind
  | Vint n => simp [Genv.find_funct] at hfind
  | Vlong n => simp [Genv.find_funct] at hfind
  | Vfloat n => simp [Genv.find_funct] at hfind
  | Vsingle n => simp [Genv.find_funct] at hfind

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro cfg prog tprog hm b f hfind
  exact inlining_function_ptr_translated_local cfg prog tprog hm b f hfind

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib

def Plt_Ple_dec : Plt_Ple_decStatement := fun p q =>
  if h : posToNat p < posToNat q then
    .left h
  else
    .right (Nat.le_of_not_gt h)

theorem sreg_below_diff : sreg_below_diffStatement := by
  intro ctx r r' hlt heq
  have habove := CompCert4Lean.Backend.Inliningspec.shiftpos_above r ctx.dreg
  unfold sreg at heq
  rw [heq] at habove
  exact (Nat.not_lt_of_ge habove) hlt

theorem context_below_lt : context_below_ltStatement := by
  intro ctx1 ctx2 r hbelow hr
  unfold context_below at hbelow
  unfold Ple PArith.BinPos.Pos.le at hr
  unfold Plt PArith.BinPos.Pos.lt
  unfold sreg
  have hshift := CompCert4Lean.Backend.Inliningspec.shiftpos_below r ctx1.dreg
  have hadd : posToNat (PArith.BinPos.Pos.add r ctx1.dreg) =
      posToNat r + posToNat ctx1.dreg := by
    simpa [PArith.BinPos.Pos.add] using posToNat_posOfNat (by
      have hrpos := posToNat_positive r
      have hdpos := posToNat_positive ctx1.dreg
      omega : 0 < posToNat r + posToNat ctx1.dreg)
  have hadd' : posToNat (PArith.BinPos.Pos.add ctx1.dreg ctx1.mreg) =
      posToNat ctx1.dreg + posToNat ctx1.mreg := by
    simpa [PArith.BinPos.Pos.add] using posToNat_posOfNat (by
      have hdpos := posToNat_positive ctx1.dreg
      have hmpos := posToNat_positive ctx1.mreg
      omega : 0 < posToNat ctx1.dreg + posToNat ctx1.mreg)
  change posToNat (PArith.BinPos.Pos.add ctx1.dreg ctx1.mreg) ≤ posToNat ctx2.dreg at hbelow
  change posToNat r ≤ posToNat ctx1.mreg at hr
  change posToNat (shiftpos r ctx1.dreg) <
    posToNat (PArith.BinPos.Pos.add r ctx1.dreg) at hshift
  change posToNat (shiftpos r ctx1.dreg) < posToNat ctx2.dreg
  rw [hadd] at hshift
  rw [hadd'] at hbelow
  have hd1 : 0 < posToNat ctx1.dreg := posToNat_positive ctx1.dreg
  have hm1 : 0 < posToNat ctx1.mreg := posToNat_positive ctx1.mreg
  have hd2 : 0 < posToNat ctx2.dreg := posToNat_positive ctx2.dreg
  omega

theorem sig_function_translated : sig_function_translatedStatement := by
  intro cfg cunit f f' h
  cases f with
  | Internal fn =>
      have hsig : ∀ (fn fn' : function),
          CompCert4Lean.Backend.Inlining.transf_function
              (funenv_program cfg cunit) fn = .OK fn' →
            fn'.fn_sig = fn.fn_sig := by
        intro fn fn' htr
        unfold CompCert4Lean.Backend.Inlining.transf_function at htr
        split at htr
        · split at htr
          · cases htr
            rfl
          · simp at htr
      unfold CompCert4Lean.Backend.Inlining.transf_fundef
        CompCert4Lean.Common.AST.transf_partial_fundef at h
      cases htr : CompCert4Lean.Backend.Inlining.transf_function
          (funenv_program cfg cunit) fn with
      | Error msg => simp [htr] at h
      | OK out =>
          simp [htr] at h
          cases h
          exact hsig fn out htr
  | External ef =>
      cases f' with
      | Internal fn' =>
          unfold CompCert4Lean.Backend.Inlining.transf_fundef
            CompCert4Lean.Common.AST.transf_partial_fundef at h
          cases h
      | External ef' =>
          unfold CompCert4Lean.Backend.Inlining.transf_fundef
            CompCert4Lean.Common.AST.transf_partial_fundef at h
          cases h
          rfl

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem agree_val_reg_gen : agree_val_reg_genStatement := by
  intro F ctx rs rs' r hregs
  rcases hregs with ⟨hbelow, habove⟩
  cases Plt_Ple_dec ctx.mreg r with
  | left hlt =>
      exact Or.inl ⟨hlt, habove r hlt⟩
  | right hle =>
      exact Or.inr ⟨hle, hbelow r hle⟩

theorem agree_val_regs_gen : agree_val_regs_genStatement := by
  intro F ctx rs rs' rl hregs
  induction rl with
  | nil =>
      exact list_forall2.nil _
  | cons r rl ih =>
      apply list_forall2.cons
      · exact agree_val_reg_gen F ctx rs rs' r hregs
      · exact ih

theorem agree_val_reg : agree_val_regStatement := by
  intro F ctx rs rs' r hregs
  have hchar := agree_val_reg_gen F ctx rs rs' r hregs
  rcases hchar with ⟨hlt, heq⟩ | ⟨hle, hinj⟩
  · rw [heq]
    exact Val.val_inject_undef _ _
  · exact hinj

theorem agree_val_regs : agree_val_regsStatement := by
  intro F ctx rs rs' rl hregs
  induction rl with
  | nil =>
      exact Val.inject_list_nil _
  | cons r rl ih =>
      apply Val.inject_list_cons
      · exact agree_val_reg F ctx rs rs' r hregs
      · exact ih

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem agree_set_reg : agree_set_regStatement := by
  intro F ctx rs rs' r v v' hag hv hr
  unfold agree_regs at *
  rcases hag with ⟨hbelow, habove⟩
  constructor
  · intro r0 hr0
    rw [@CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
      (r0 : CompCert4Lean.Backend.Registers.reg)
      (r : CompCert4Lean.Backend.Registers.reg) v rs,
      @CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
        (sreg ctx r0 : CompCert4Lean.Backend.Registers.reg)
        (sreg ctx r : CompCert4Lean.Backend.Registers.reg) v' rs']
    cases peq r0 r with
    | left h =>
        subst r0
        cases hsr : peq (sreg ctx r) (sreg ctx r) with
        | left _ => simpa [hsr] using hv
        | right hne => exact False.elim (hne rfl)
    | right h =>
        have hshift : sreg ctx r0 ≠ sreg ctx r := by
          exact CompCert4Lean.Backend.Inliningspec.shiftpos_diff r0 r ctx.dreg h
        cases hsr : peq (sreg ctx r0) (sreg ctx r) with
        | left hEq => exact False.elim (hshift hEq)
        | right _ => simpa [hsr] using hbelow r0 hr0
  · intro r0 hr0
    rw [@CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
      (r0 : CompCert4Lean.Backend.Registers.reg)
      (r : CompCert4Lean.Backend.Registers.reg) v rs]
    cases peq r0 r with
    | left h =>
        subst r0
        have hfalse : False := by
          have hbad : Plt ctx.mreg ctx.mreg :=
            Plt_Ple_trans _ _ _ hr0 hr
          exact Plt_strict _ hbad
        exact hfalse.elim
    | right h =>
        simp [h]
        exact habove r0 hr0

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem agree_set_reg_undef : agree_set_reg_undefStatement := by
  intro F ctx rs rs' r v' hag
  unfold agree_regs at *
  rcases hag with ⟨hbelow, habove⟩
  constructor
  · intro r0 hr0
    rw [@CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
      (r0 : CompCert4Lean.Backend.Registers.reg)
      (r : CompCert4Lean.Backend.Registers.reg) Vundef rs,
      @CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
        (sreg ctx r0 : CompCert4Lean.Backend.Registers.reg)
        (sreg ctx r : CompCert4Lean.Backend.Registers.reg) v' rs']
    cases peq r0 r with
    | left h =>
        subst r0
        cases hsr : peq (sreg ctx r) (sreg ctx r) with
        | left _ => exact Val.val_inject_undef _ _
        | right hne => exact False.elim (hne rfl)
    | right h =>
        have hshift : sreg ctx r0 ≠ sreg ctx r := by
          exact CompCert4Lean.Backend.Inliningspec.shiftpos_diff r0 r ctx.dreg h
        cases hsr : peq (sreg ctx r0) (sreg ctx r) with
        | left hEq => exact False.elim (hshift hEq)
        | right _ => simpa [hsr] using hbelow r0 hr0
  · intro r0 hr0
    rw [@CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
      (r0 : CompCert4Lean.Backend.Registers.reg)
      (r : CompCert4Lean.Backend.Registers.reg) Vundef rs]
    cases peq r0 r with
    | left h =>
        subst r0
        cases hsr : peq r r with
        | left _ => rfl
        | right hne => exact False.elim (hne rfl)
    | right h =>
        simpa [h] using habove r0 hr0

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem agree_set_reg_undef' : agree_set_reg_undef'Statement := by
  intro F ctx rs rs' r hag
  unfold agree_regs at *
  rcases hag with ⟨hbelow, habove⟩
  constructor
  · intro r0 hr0
    rw [@CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
      (r0 : CompCert4Lean.Backend.Registers.reg)
      (r : CompCert4Lean.Backend.Registers.reg) Vundef rs]
    cases peq r0 r with
    | left h =>
        subst r0
        cases hsr : peq r r with
        | left _ => exact Val.val_inject_undef _ _
        | right hne => exact False.elim (hne rfl)
    | right h =>
        simpa [h] using hbelow r0 hr0
  · intro r0 hr0
    rw [@CompCert4Lean.Backend.Registers.Regmap.gsspec_proof val
      (r0 : CompCert4Lean.Backend.Registers.reg)
      (r : CompCert4Lean.Backend.Registers.reg) Vundef rs]
    cases peq r0 r with
    | left h =>
        subst r0
        cases hsr : peq r r with
        | left _ => rfl
        | right hne => exact False.elim (hne rfl)
    | right h =>
        simpa [h] using habove r0 hr0

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem agree_regs_invariant : agree_regs_invariantStatement := by
  intro F ctx rs rs1 rs2 hag hsame
  unfold agree_regs at *
  rcases hag with ⟨hbelow, habove⟩
  constructor
  · intro r0 hr0
    have hupper : Plt (sreg ctx r0) (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) := by
      have hshift := CompCert4Lean.Backend.Inliningspec.shiftpos_below r0 ctx.dreg
      have hadd1 : posToNat (PArith.BinPos.Pos.add r0 ctx.dreg) =
          posToNat r0 + posToNat ctx.dreg := by
        simpa [PArith.BinPos.Pos.add] using posToNat_posOfNat (by
          have hrpos := posToNat_positive r0
          have hdpos := posToNat_positive ctx.dreg
          omega : 0 < posToNat r0 + posToNat ctx.dreg)
      have hadd2 : posToNat (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) =
          posToNat ctx.dreg + posToNat ctx.mreg := by
        simpa [PArith.BinPos.Pos.add] using posToNat_posOfNat (by
          have hdpos := posToNat_positive ctx.dreg
          have hmpos := posToNat_positive ctx.mreg
          omega : 0 < posToNat ctx.dreg + posToNat ctx.mreg)
      unfold Plt at hshift ⊢
      change posToNat (shiftpos r0 ctx.dreg) <
        posToNat (PArith.BinPos.Pos.add r0 ctx.dreg) at hshift
      change posToNat (shiftpos r0 ctx.dreg) <
        posToNat (PArith.BinPos.Pos.add ctx.dreg ctx.mreg)
      rw [hadd1] at hshift
      rw [hadd2]
      change posToNat r0 ≤ posToNat ctx.mreg at hr0
      omega
    have hEq := hsame (sreg ctx r0)
      (CompCert4Lean.Backend.Inliningspec.shiftpos_above r0 ctx.dreg) hupper
    rw [hEq]
    exact hbelow r0 hr0
  · intro r0 hr0
    exact habove r0 hr0

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem agree_regs_init : agree_regs_initStatement := by
  intro F ctx rs
  unfold agree_regs
  constructor
  · intro r hr
    rw [@Regmap.gi_proof val (r : CompCert4Lean.Backend.Registers.reg) Vundef]
    exact Val.val_inject_undef F _
  · intro r hr
    rw [@Regmap.gi_proof val (r : CompCert4Lean.Backend.Registers.reg) Vundef]

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values

private theorem val_inject_incr_local (F F' : Val.meminj) (v v' : val)
    (hinc : inject_incr F F') (hval : Val.inject F v v') :
    Val.inject F' v v' := by
  cases hval with
  | inject_int i => exact Val.inject.inject_int i
  | inject_long i => exact Val.inject.inject_long i
  | inject_float f => exact Val.inject.inject_float f
  | inject_single f => exact Val.inject.inject_single f
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta (hinc b1 b2 delta hmap) hofs
  | val_inject_undef v' => exact Val.inject.val_inject_undef v'

theorem agree_regs_incr : agree_regs_incrStatement := by
  intro F ctx rs1 rs2 F' hag hinc
  unfold agree_regs at *
  rcases hag with ⟨hbelow, habove⟩
  constructor
  · intro r hr
    exact val_inject_incr_local F F' _ _ hinc (hbelow r hr)
  · exact habove

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem agree_regs_init_regs : agree_regs_init_regsStatement := by
  intro F ctx rl
  induction rl with
  | nil =>
      intro vl vl' hvl hrl
      cases vl with
      | nil =>
          cases vl' with
          | nil =>
              exact agree_regs_init F ctx _
          | cons v' vl' =>
              cases hvl
      | cons v vl =>
          cases vl' with
          | nil =>
              cases hvl
          | cons v' vl' =>
              exact agree_regs_init F ctx _
  | cons r rl ih =>
      intro vl vl' hvl hrl
      cases vl with
      | nil =>
          cases vl' with
          | nil =>
              exact agree_regs_init F ctx _
          | cons v' vl' =>
              cases hvl
      | cons v vl =>
          cases vl' with
          | nil =>
              cases hvl
          | cons v' vl' =>
              cases hvl with
              | inject_list_cons _ _ _ _ hv htail =>
                  have hr : CompCert4Lean.Lib.Coqlib.Ple r ctx.mreg := by
                    exact hrl r (List.mem_cons_self)
                  have hrl' : ∀ r0, r0 ∈ rl → CompCert4Lean.Lib.Coqlib.Ple r0 ctx.mreg := by
                    intro r0 hr0
                    exact hrl r0 (List.mem_cons_of_mem r hr0)
                  have htailAgree := ih vl vl' htail hrl'
                  change agree_regs F ctx
                    (Regmap.set r v (init_regs vl rl))
                    (Regmap.set (sreg ctx r) v' (init_regs vl' (sregs ctx rl)))
                  exact agree_set_reg F ctx
                    (init_regs vl rl) (init_regs vl' (sregs ctx rl)) r v v'
                    htailAgree hv hr

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem tr_moves_nil_pc (c : code) (pc1 pc2 : node) (srcs : List reg) :
    tr_moves c pc1 srcs [] pc2 → pc1 = pc2 := by
  intro h
  cases h with
  | tr_moves_nil => rfl

theorem tr_moves_init_regs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    tr_moves_init_regsStatement := by
  intro xi tprog F stk f sp m ctx1 ctx2 hctx
  intro rdsts
  induction rdsts with
  | nil =>
      intro rsrcs vl pc1 pc2 rs1 htr hdst hvl
      have hpc : pc1 = pc2 := tr_moves_nil_pc f.fn_code pc1 pc2 (sregs ctx1 rsrcs) htr
      subst pc2
      refine ⟨rs1, ?_, ?_, ?_⟩
      · exact star_refl _ _ _
      · cases vl <;> exact agree_regs_init F ctx2 rs1
      · intro r hr
        rfl
  | cons a rdsts ih =>
      intro rsrcs vl pc1 pc2 rs1 htr hdst hvl
      cases hvl with
      | nil =>
          simp only [sregs, List.map] at htr
          cases htr with
          | tr_moves_nil =>
              refine ⟨rs1, ?_, ?_, ?_⟩
              · exact star_refl _ _ _
              · change agree_regs F ctx2 (Regmap.init Vundef) rs1
                exact agree_regs_init F ctx2 rs1
              · intro r hr
                rfl
      | cons v r hv htail =>
          rename_i vl_tail rsrcs_tail
          simp only [sregs, List.map] at htr
          cases htr with
          | tr_moves_cons =>
              rename_i htr' hcode
              have hdst_a : Ple a ctx2.mreg := hdst a (List.mem_cons_self)
              have hdst_tail : ∀ r, r ∈ rdsts → Ple r ctx2.mreg := by
                intro r hr
                exact hdst r (List.mem_cons_of_mem a hr)
              have ih_result := ih _ _ _ _ rs1 htr' hdst_tail htail
              rcases ih_result with ⟨rs2, hstar, hagree, hbelow⟩
              refine ⟨Regmap.set (sreg ctx2 a) (Regmap.get (sreg ctx1 r) rs2) rs2, ?_, ?_, ?_⟩
              · exact star_right
                  (genv := RTL.genv) (state := RTL.state) (step := RTL.step xi)
                  (ge := CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog)
                  (s1 := State stk f sp pc1 rs1 m) (t1 := E0)
                  (s2 := _)
                  (t2 := E0)
                  (s3 := State stk f sp pc2 (Regmap.set (sreg ctx2 a)
                    (Regmap.get (sreg ctx1 r) rs2) rs2) m) (t := E0)
                  hstar (by
                    apply RTL.step.exec_Iop
                    · exact hcode
                    · rfl) rfl
              · change agree_regs F ctx2
                  (Regmap.set a v (init_regs vl_tail rdsts))
                  (Regmap.set (sreg ctx2 a) (Regmap.get (sreg ctx1 r) rs2) rs2)
                rcases hv with ⟨hbelow_src, hvundef⟩ | ⟨hsrcle, hvis⟩
                · subst v
                  exact agree_set_reg_undef F ctx2
                    (init_regs vl_tail rdsts) rs2 a (Regmap.get (sreg ctx1 r) rs2) hagree
                · apply agree_set_reg F ctx2
                    (init_regs vl_tail rdsts) rs2 a v (Regmap.get (sreg ctx1 r) rs2) hagree
                  · have hsrcbelow : Plt (sreg ctx1 r) ctx2.dreg := by
                      exact context_below_lt ctx1 ctx2 r hctx hsrcle
                    have heq := hbelow (sreg ctx1 r) hsrcbelow
                    rw [heq]
                    exact hvis
                  · exact hdst_a
              · intro r0 hr
                rw [@Regmap.gsspec_proof val r0 (sreg ctx2 a)
                  (Regmap.get (sreg ctx1 r) rs2) rs2]
                cases peq r0 (sreg ctx2 a) with
                | left h =>
                    have hdiff : sreg ctx2 a ≠ r0 := by
                      exact sreg_below_diff ctx2 a r0 hr
                    exact False.elim (hdiff h.symm)
                | right h =>
                    simpa [h] using hbelow r0 hr
          | tr_moves_nil =>
              rename_i hcase
              simp at hcase

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Common.Memory

theorem range_private_perms : range_private_permsStatement := by
  intro F m m' sp lo hi h ofs hof
  exact (h ofs hof).1

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem pmap_get_set_spec_local {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) :
    PMap.get i (PMap.set j x m) = if h : i = j then x else PMap.get i m := by
  unfold PMap.get PMap.set
  rw [PTree.gsspec_proof]
  cases h : peq i j with
  | left hij => simp [hij]
  | right hne => simp [h, hne]

private theorem mem_perm_alloc_inv_local
    (m : mem) (lo hi : Z) (m2 : mem) (b : positive)
    (halloc : Mem.alloc m lo hi = (m2, b))
    (b' : CompCert4Lean.Common.Values.block) (ofs : Z) (k : perm_kind) (p : permission)
    (hperm : Mem.perm m2 b' ofs k p) :
    match eq_block b' b with
    | .left _ => zLe lo ofs ∧ zLt ofs hi
    | .right _ => Mem.perm m b' ofs k p := by
  unfold Mem.alloc at halloc
  cases halloc
  let fresh : positive := m.nextblock
  cases heq : eq_block b' m.nextblock with
  | left hbeq =>
      subst b'
      simp only [Mem.perm] at hperm
      rw [pmap_get_set_spec_local] at hperm
      simp at hperm
      unfold Mem.perm_order' at hperm
      split at hperm
      · rename_i hIn
        split at hIn
        · rename_i hRange
          simp only [heq]
          change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hRange
          simp only [Bool.and_eq_true] at hRange
          constructor
          · change intOfZ lo ≤ intOfZ ofs
            simpa [ZArith.BinInt.Z.leb] using hRange.1
          · change intOfZ ofs < intOfZ hi
            simpa [ZArith.BinInt.Z.ltb] using hRange.2
        · simp at hIn
      · simp at hperm
  | right hbneq =>
      simp only [Mem.perm] at hperm
      change Mem.perm_order'
        ((PMap.get (show positive from b')
          (PMap.set (show positive from m.nextblock) _ m.mem_access)) ofs k) p at hperm
      rw [pmap_get_set_spec_local] at hperm
      have hbneq' : (show positive from b') ≠ (show positive from m.nextblock) := by
        intro h
        apply hbneq
        exact h
      simp [hbneq, hbneq'] at hperm
      simpa [heq, hbneq, Mem.perm] using hperm

theorem range_private_alloc_left : range_private_alloc_leftStatement := by
  intro F m m' sp' base hi sz m1 sp F1 hpriv halloc hmap hsame
  unfold range_private loc_private at hpriv ⊢
  intro ofs hofs
  rcases hofs with ⟨hofs_lo, hofs_hi⟩
  have hz0 : intOfZ zZero = 0 := by rfl
  have hmax0 : zLe zZero (ZArith.BinInt.Z.max sz zZero) := by
    change 0 ≤ intOfZ (ZArith.BinInt.Z.max sz zZero)
    by_cases h : intOfZ sz ≤ 0
    · simp [ZArith.BinInt.Z.max, h, hz0]
    · simp [ZArith.BinInt.Z.max, h, Int.le_of_not_le h, hz0]
  have hofs_lo' : intOfZ base + intOfZ (ZArith.BinInt.Z.max sz zZero) ≤ intOfZ ofs := by
    simpa only [zLe, zAdd, ZArith.BinInt.Z.le, ZArith.BinInt.Z.add,
      intOfZ_zOfInt] using hofs_lo
  have hbase : zLe base ofs := by
    change intOfZ base ≤ intOfZ ofs
    have hnonneg : 0 ≤ intOfZ (ZArith.BinInt.Z.max sz zZero) := by
      simpa only [zLe, ZArith.BinInt.Z.le, hz0] using hmax0
    omega
  have horig := hpriv ofs ⟨hbase, hofs_hi⟩
  constructor
  · exact horig.1
  · intro b delta hF1 hnot
    cases hb : eq_block b sp with
    | left hbeq =>
        subst b
        have hdelta : delta = base := by
          rw [hmap] at hF1
          cases hF1
          rfl
        subst delta
        have hinv := mem_perm_alloc_inv_local m zZero sz m1 sp halloc
          sp (zSub ofs base) Max Nonempty hnot
        have hinv' : zLe zZero (zSub ofs base) ∧ zLt (zSub ofs base) sz := by
          simpa [hb] using hinv
        have hmax : zLe sz (ZArith.BinInt.Z.max sz zZero) := by
          change intOfZ sz ≤ intOfZ (ZArith.BinInt.Z.max sz zZero)
          by_cases h : intOfZ sz ≤ 0
          · simp [ZArith.BinInt.Z.max, h, hz0]
          · simp [ZArith.BinInt.Z.max, h, Int.le_of_not_le h, hz0]
        have hlt := hinv'.2
        have hlt' : intOfZ ofs - intOfZ base < intOfZ sz := by
          simpa only [zLt, zSub, ZArith.BinInt.Z.lt, ZArith.BinInt.Z.sub,
            intOfZ_zOfInt] using hlt
        have hmax' : intOfZ sz ≤ intOfZ (ZArith.BinInt.Z.max sz zZero) := by
          simpa only [zLe, ZArith.BinInt.Z.le] using hmax
        omega
    | right hbneq =>
        have hF : F b = some (sp', delta) := by
          rw [← hsame b hbneq]
          exact hF1
        have hinv := mem_perm_alloc_inv_local m zZero sz m1 sp halloc
          b (zSub ofs delta) Max Nonempty hnot
        have hm : Mem.perm m b (zSub ofs delta) Max Nonempty := by
          simpa [hb, hF] using hinv
        exact horig.2 b delta hF hm

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps

theorem find_inlined_function : find_inlined_functionStatement := by
  intro prog fenv id rs fd f hcompat hfind hget
  have hdef := hcompat id f hget
  have hs := (Genv.find_def_symbol (F := fundef) (V := Unit)
    (p := prog) (id := id) (g := (Gfun (Internal f)))).mp hdef
  rcases hs with ⟨b, hsym, hfun⟩
  unfold find_function at hfind
  simp only [Sum.rec] at hfind
  rw [hsym] at hfind
  have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some (Internal f) :=
    (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
      (ge := Genv.globalenv prog) (b := b) (f := Internal f)).mpr hfun
  exact Option.some.inj (hfind.symm.trans hptr)

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Events

theorem range_private_extcall : range_private_extcallStatement := by
  intro F F' m1 m2 m1' m2' sp base hi hpriv hperm hunch hinj hincr hsep hvalid
  unfold range_private loc_private at hpriv ⊢
  intro ofs hofs
  have horig := hpriv ofs hofs
  constructor
  · have hloc : loc_out_of_reach F m1 sp ofs := by
      intro b delta hmap
      exact horig.2 b delta hmap
    exact (hunch.unchanged_on_perm sp ofs Cur Freeable hloc hvalid).mp horig.1
  · intro b delta hF' hnot
    cases hF : F b with
    | some p =>
        rcases p with ⟨b', delta'⟩
        have hinc := hincr b b' delta' hF
        have hpairs : (b', delta') = (sp, delta) :=
          Option.some.inj (hinc.symm.trans hF')
        rcases hpairs with ⟨rfl, rfl⟩
        have hbvalid : Mem.valid_block m1 b := by
          by_cases hb : Mem.valid_block m1 b
          · exact hb
          · have hnone := hinj.mi_freeblocks b hb
            rw [hF] at hnone
            cases hnone
        have hp1 := hperm b (zSub ofs delta) Nonempty hbvalid hnot
        exact horig.2 b delta hF hp1
    | none =>
        have hsep' := hsep b sp delta hF hF'
        exact hsep'.2 hvalid

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inlining_ptrofs_add_zero_repr :
    CompCert4Lean.Lib.Integers.Ptrofs.add
        CompCert4Lean.Lib.Integers.Ptrofs.zero
        (CompCert4Lean.Lib.Integers.Ptrofs.repr zZero) =
      CompCert4Lean.Lib.Integers.Ptrofs.zero := by
  rfl

theorem find_function_agree : find_function_agreeStatement := by
  intro cfg prog tprog hm ros rs fd F ctx rs' bound hfind hregs hgenv
  cases ros with
  | inl r =>
      simp only [CompCert4Lean.Backend.RTL.find_function, Sum.rec, sros] at hfind ⊢
      have hinv := Genv.find_funct_inv (F := fundef) (V := Unit)
        (ge := Genv.globalenv prog) (v := Regmap.get r rs) (f := fd) hfind
      rcases hinv with ⟨b, hv⟩
      have hfind_v : Genv.find_funct (Genv.globalenv prog)
          (Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero) = some fd := by
        simpa [hv] using hfind
      have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some fd := by
        exact (Genv.find_funct_find_funct_ptr (F := fundef) (V := Unit)
          (ge := Genv.globalenv prog) (b := b)).symm.trans hfind_v
      rcases hgenv with ⟨hdom, himage, hsymbols, hfunctions, hvarinfos⟩
      have hb : Plt b bound := hfunctions b fd hptr
      have hmap : F b = some (b, zZero) := hdom b hb
      have hinj0 := agree_val_reg F ctx rs rs' r hregs
      rw [hv] at hinj0
      generalize hval : Regmap.get (sreg ctx r) rs' = v at hinj0 ⊢
      cases v with
      | Vundef => cases hinj0
      | Vint i => cases hinj0
      | Vlong i => cases hinj0
      | Vfloat f => cases hinj0
      | Vsingle f => cases hinj0
      | Vptr b2 ofs2 =>
          have hinj : Val.inject F (Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero) (Vptr b2 ofs2) := by
            exact hinj0
          cases hinj with
          | inject_ptr _ _ _ _ delta hF hofs =>
              have hp : (b2, delta) = (b, zZero) :=
                Option.some.inj (hF.symm.trans hmap)
              have hbs : b2 = b := congrArg Prod.fst hp
              have hdelta : delta = zZero := congrArg Prod.snd hp
              subst b2
              subst delta
              have hofs0 : ofs2 = CompCert4Lean.Lib.Integers.Ptrofs.zero := by
                rw [hofs]
                exact inlining_ptrofs_add_zero_repr
              rw [hofs0]
              exact functions_translated cfg prog tprog hm
                (Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero) fd hfind_v
  | inr id =>
      simp only [CompCert4Lean.Backend.RTL.find_function, Sum.rec, sros] at hfind ⊢
      cases hs : Genv.find_symbol (Genv.globalenv prog) id with
      | none => simp [hs] at hfind
      | some b =>
          have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some fd := by
            simpa [hs] using hfind
          obtain ⟨cu, fd', hptr', htrans, horder⟩ :=
            function_ptr_translated cfg prog tprog hm b fd hptr
          have hst : Genv.find_symbol (Genv.globalenv tprog) id = some b := by
            rw [symbols_preserved cfg prog tprog hm id]
            exact hs
          refine ⟨cu, fd', ?_, htrans, horder⟩
          simpa [hs, hst] using hptr'

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

theorem match_stacks_ind : match_stacks_indStatement := by
  intro prog F m m' P Hnil Hcons Htail l l0 b h
  refine match_stacks.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 b _ => P l l0 b)
    (motive_2 := fun _ _ _ _ _ _ _ => True) ?_ ?_ ?_ ?_ ?_ h
  · intro bound1 bound MG BELOW
    exact Hnil bound1 bound MG BELOW
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    exact Hcons res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    exact Htail stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih
    exact True.intro
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    exact True.intro

theorem match_stacks_inside_ind : match_stacks_inside_indStatement := by
  intro prog F m m' P Hbase Hinlined l l0 f c b r h
  refine match_stacks_inside.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun l l0 f c b r _ => P l l0 f c b r) ?_ ?_ ?_ ?_ ?_ h
  · intro bound1 bound MG BELOW
    exact True.intro
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    exact True.intro
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    exact True.intro
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih
    exact Hbase stk stk' f' ctx sp' rs' MS RET DSTK
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    exact Hinlined res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS ih COMPAT FB AG SP PAD RES RET BELOW SBELOW

theorem match_stacks_globalenvs : match_stacks_globalenvsStatement := by
  intro prog F m m' stk stk' bound h
  refine match_stacks.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun _ _ _ _ => ∃ b, match_globalenvs prog F b)
    (motive_2 := fun _ _ _ _ _ _ _ => ∃ b, match_globalenvs prog F b) ?_ ?_ ?_ ?_ ?_ h
  · intro bound1 bound MG BELOW
    exact ⟨bound1, MG⟩
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    exact ih
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    exact ih
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih
    exact ih
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    exact ih

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem match_stacks_bound : match_stacks_boundStatement := by
  intro prog F m m' stk stk' bound bound1 h hbound
  refine match_stacks.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 b _ => ∀ b1, Ple b b1 → match_stacks prog F m m' l l0 b1)
    (motive_2 := fun _ _ _ _ _ _ _ => True) ?_ ?_ ?_ ?_ ?_ h bound1 hbound
  · intro bound0 boundx MG Hbelow btarget Htarget
    exact match_stacks_nil bound0 btarget MG
      (Ple_trans bound0 boundx btarget Hbelow (Ple_trans boundx btarget btarget Htarget (Ple_refl _)))
  · intro res f sp pc rs stk f' sp' rs' stk' boundx fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih btarget Htarget
    exact match_stacks_cons res f sp pc rs stk f' sp' rs' stk' btarget fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES
      (Plt_Ple_trans sp' boundx btarget BELOW Htarget)
  · intro stk res f' sp' rpc rs' stk' boundx ctx MS PRIV SSZ1 SSZ2 RET BELOW ih btarget Htarget
    exact match_stacks_untailcall stk res f' sp' rpc rs' stk' btarget ctx MS PRIV SSZ1 SSZ2 RET
      (Plt_Ple_trans sp' boundx btarget BELOW Htarget)
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih
    exact True.intro
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    exact True.intro

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem match_globalenvs_preserves_globals : match_globalenvs_preserves_globalsStatement := by
  intro prog F bound h
  rcases h with ⟨DOMAIN, IMAGE, SYMBOLS, FUNCTIONS, VARINFOS⟩
  constructor
  · intro id b hsym
    exact DOMAIN b (SYMBOLS id b hsym)
  constructor
  · intro b gv hvar
    exact DOMAIN b (VARINFOS b gv hvar)
  · intro b1 b2 delta gv hvar hmap
    exact (IMAGE b1 b2 delta hmap (VARINFOS b2 gv hvar)).symm

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem match_stacks_inside_globalenvs : match_stacks_inside_globalenvsStatement := by
  intro prog F m m' stk stk' f ctx sp rs h
  refine match_stacks_inside.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun _ _ _ _ => ∃ b, match_globalenvs prog F b)
    (motive_2 := fun _ _ _ _ _ _ _ => ∃ b, match_globalenvs prog F b) ?_ ?_ ?_ ?_ ?_ h
  · intro bound1 bound MG BELOW
    exact ⟨bound1, MG⟩
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    exact ih
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    exact ih
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih
    exact ih
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PRIV RES RET BELOW SBELOW ih
    exact ih

theorem match_stacks_inside_globals : match_stacks_inside_globalsStatement := by
  intro prog F m m' stk stk' f ctx sp rs h
  obtain ⟨bound, hbound⟩ := match_stacks_inside_globalenvs prog F m m' stk stk' f ctx sp rs h
  exact match_globalenvs_preserves_globals prog F bound hbound

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

theorem match_stacks_empty : match_stacks_emptyStatement := by
  intro prog F m m' stk stk' bound h hstk
  refine match_stacks.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 b _ => l = [] -> l0 = [])
    (motive_2 := fun l l0 f c b r _ => l = [] -> l0 = [] ∧ c.retinfo = none)
    ?_ ?_ ?_ ?_ ?_ h hstk
  · intro bound1 bound MG BELOW hnil
    exact rfl
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih hnil
    cases hnil
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih hnil
    have hinner := ih hnil
    rw [hinner.2] at RET
    cases RET
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih hnil
    exact ⟨ih hnil, RET⟩
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih hnil
    cases hnil

theorem match_stacks_inside_empty : match_stacks_inside_emptyStatement := by
  intro prog F m m' stk stk' f ctx sp rs h hstk
  refine match_stacks_inside.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 b _ => l = [] -> l0 = [])
    (motive_2 := fun l l0 f c b r _ => l = [] -> l0 = [] ∧ c.retinfo = none)
    ?_ ?_ ?_ ?_ ?_ h hstk
  · intro bound1 bound MG BELOW hnil
    exact rfl
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih hnil
    cases hnil
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih hnil
    have hinner := ih hnil
    rw [hinner.2] at RET
    cases RET
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih hnil
    exact ⟨match_stacks_empty prog F m m' stk stk' sp' MS hnil, RET⟩
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih hnil
    cases hnil

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem match_stacks_inside_set_reg : match_stacks_inside_set_regStatement := by
  intro prog F m m' stk stk' f ctx sp rs r v h
  refine match_stacks_inside.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun l l0 f c b rs0 _ =>
      ∀ q, Ple c.dreg q →
        match_stacks_inside prog F m m' l l0 f c b (Regmap.set q v rs0)) ?_ ?_ ?_ ?_ ?_ h
    (sreg ctx r) (CompCert4Lean.Backend.Inliningspec.shiftpos_above r ctx.dreg)
  · intro bound1 bound MG BELOW
    exact True.intro
  · intro res f sp pc rs stk f' sp' rs' stk' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    exact True.intro
  · intro stk res f' sp' rpc rs' stk' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    exact True.intro
  · intro stk stk' f' ctx sp' rs' MS RET DSTK ih q Hq
    exact match_stacks_inside_base stk stk' f' ctx sp' (Regmap.set q v rs') MS RET DSTK
  · intro res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' MS COMPAT FB AG SP PRIV RES RET BELOW SBELOW ih q Hq
    have Hctx'_le_sum : Ple ctx'.dreg (PArith.BinPos.Pos.add ctx'.dreg ctx'.mreg) := by
      unfold Ple PArith.BinPos.Pos.le
      have hadd : posToNat (PArith.BinPos.Pos.add ctx'.dreg ctx'.mreg) =
          posToNat ctx'.dreg + posToNat ctx'.mreg := by
        simpa [PArith.BinPos.Pos.add] using posToNat_posOfNat (by
          have hdpos := posToNat_positive ctx'.dreg
          have hmpos := posToNat_positive ctx'.mreg
          omega : 0 < posToNat ctx'.dreg + posToNat ctx'.mreg)
      rw [hadd]
      omega
    have Hq' : Ple ctx'.dreg q :=
      Ple_trans ctx'.dreg (PArith.BinPos.Pos.add ctx'.dreg ctx'.mreg) q Hctx'_le_sum
        (Ple_trans (PArith.BinPos.Pos.add ctx'.dreg ctx'.mreg) ctx.dreg q BELOW Hq)
    have AG' : agree_regs F ctx' rs
        (Regmap.set q v rs') := by
      apply agree_regs_invariant F ctx' rs rs'
        (Regmap.set q v rs') AG
      intro r0 Hbelow Hupper
      have Hbelow_ctx : Plt r0 ctx.dreg :=
        Plt_Ple_trans r0 (PArith.BinPos.Pos.add ctx'.dreg ctx'.mreg) ctx.dreg
          Hupper BELOW
      have Hlt_q : Plt r0 q := Plt_Ple_trans r0 ctx.dreg q Hbelow_ctx Hq
      exact Regmap.gso_proof CompCert4Lean.Common.Values.val r0 q v rs'
        (Plt_ne r0 q Hlt_q)
    exact match_stacks_inside_inlined res f sp pc rs stk stk' f' fenv ctx sp'
      (Regmap.set q v rs') ctx' (ih q Hq') COMPAT FB AG' SP PRIV RES RET BELOW SBELOW

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST

theorem match_stacks_inside_set_res : match_stacks_inside_set_resStatement := by
  intro prog F m m' stk stk' f ctx sp rs res v h
  cases res with
  | BR r =>
      simpa [regmap_setres, sbuiltinres] using
        (match_stacks_inside_set_reg prog F m m' stk stk' f ctx sp rs r v h)
  | BR_none =>
      simpa [regmap_setres, sbuiltinres] using h
  | BR_splitlong hi lo =>
      simpa [regmap_setres, sbuiltinres] using h

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

private theorem range_private_store_local
    (F : Val.meminj) (m m' m1 m1' : mem) (sp : block) (lo hi : Z)
    (chunk chunk' : memory_chunk) (b b' : block) (ofs ofs' : Z) (v v' : val)
    (hpriv : range_private F m m' sp lo hi)
    (hs : Mem.store chunk m b ofs v = some m1)
    (hs' : Mem.store chunk' m' b' ofs' v' = some m1') :
    range_private F m1 m1' sp lo hi := by
  unfold range_private loc_private at hpriv ⊢
  intro p hp
  rcases hpriv p hp with ⟨hperm, hprivate⟩
  constructor
  · exact Mem.perm_store_1 chunk' m' b' ofs' v' m1' hs' sp p .Cur .Freeable hperm
  · intro b0 delta hmap hbad
    apply hprivate b0 delta hmap
    exact Mem.perm_store_2 chunk m b ofs v m1 hs b0 (zSub p delta) .Max .Nonempty hbad

theorem match_stacks_inside_store : match_stacks_inside_storeStatement := by
  intro prog F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1' h hs hs'
  refine match_stacks_inside.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 bound _ =>
      Mem.store chunk m b ofs v = some m1 →
      Mem.store chunk' m' b' ofs' v' = some m1' →
      match_stacks prog F m1 m1' l l0 bound)
    (motive_2 := fun l l0 f c bound r _ =>
      Mem.store chunk m b ofs v = some m1 →
      Mem.store chunk' m' b' ofs' v' = some m1' →
      match_stacks_inside prog F m1 m1' l l0 f c bound r)
    ?_ ?_ ?_ ?_ ?_ h hs hs'
  · intro bound1 bound MG BELOW hs hs'
    exact match_stacks_nil bound1 bound MG BELOW
  · intro res f sp pc rs l f' sp' rs' l' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih hs hs'
    exact match_stacks_cons res f sp pc rs l f' sp' rs' l' bound fenv ctx
      (ih hs hs') COMPAT FB AG SP
      (range_private_store_local F m m' m1 m1' sp' (zAdd ctx.dstk ctx.mstk)
        f'.fn_stacksize chunk chunk' b b' ofs ofs' v v' PRIV hs hs')
      SSZ1
      (by
        intro ofs0 hperm
        exact SSZ2 ofs0
          (Mem.perm_store_2 chunk' m' b' ofs' v' m1' hs' sp' ofs0
            .Max .Nonempty hperm))
      RES BELOW
  · intro l res f' sp' rpc rs' l' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih hs hs'
    exact match_stacks_untailcall l res f' sp' rpc rs' l' bound ctx
      (ih hs hs')
      (range_private_store_local F m m' m1 m1' sp' ctx.dstk f'.fn_stacksize
        chunk chunk' b b' ofs ofs' v v' PRIV hs hs')
      SSZ1
      (by
        intro ofs0 hperm
        exact SSZ2 ofs0
          (Mem.perm_store_2 chunk' m' b' ofs' v' m1' hs' sp' ofs0
            .Max .Nonempty hperm))
      RET BELOW
  · intro l l' f' c sp' rs' MS RET DSTK ih hs hs'
    exact match_stacks_inside_base l l' f' c sp' rs' (ih hs hs') RET DSTK
  · intro res f sp pc rs l l' f' fenv c sp' rs' c' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih hs hs'
    exact match_stacks_inside_inlined res f sp pc rs l l' f' fenv c sp'
      rs' c' (ih hs hs') COMPAT FB AG SP
      (range_private_store_local F m m' m1 m1' sp' (zAdd c'.dstk c'.mstk) c.dstk
        chunk chunk' b b' ofs ofs' v v' PAD hs hs')
      RES RET BELOW SBELOW

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem zsub_zadd_cancel_local (a d : Z) :
    zSub (zAdd a d) d = a := by
  apply intOfZ_injective
  simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
    intOfZ_zOfInt]
  omega

private theorem zsub_add_cancel_local (a d : Z) :
    zAdd (zSub a d) d = a := by
  apply intOfZ_injective
  simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
    intOfZ_zOfInt]
  omega

private theorem ple_plt_trans_local (a b c : positive) :
    Ple a b → Plt b c → Plt a c := by
  intro hab hbc
  unfold Ple PArith.BinPos.Pos.le at hab
  unfold Plt PArith.BinPos.Pos.lt at hbc ⊢
  omega

private theorem plt_add_right_local (a b : positive) :
    Plt a (PArith.BinPos.Pos.add a b) := by
  unfold Plt PArith.BinPos.Pos.lt
  have hadd : posToNat (PArith.BinPos.Pos.add a b) =
      posToNat a + posToNat b := by
    simpa [PArith.BinPos.Pos.add] using posToNat_posOfNat (by
      have ha := posToNat_positive a
      have hb := posToNat_positive b
      omega : 0 < posToNat a + posToNat b)
  rw [hadd]
  have hb := posToNat_positive b
  omega

private theorem range_private_invariant_local : range_private_invariantStatement := by
  intro F m m' sp lo hi F1 m1 m1' hpriv hinj hperm
  unfold range_private loc_private at hpriv ⊢
  intro ofs hofs
  have hloc := hpriv ofs hofs
  constructor
  · exact hperm ofs hloc.1
  · intro b delta hmap hbad
    have hmap' := hinj b delta (zSub ofs delta) hmap hbad (by
      rw [zsub_add_cancel_local]
      exact hofs)
    exact hloc.2 b delta hmap'.1 hmap'.2

private theorem match_stacks_invariant_local : match_stacks_invariantStatement := by
  intro prog F m m' F1 m1 m1' hIncr
  intro stk stk' bound hstacks
  refine match_stacks.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 bound _ =>
      ∀ (INJ : ∀ b1 b2 delta, F1 b1 = some (b2, delta) → Plt b2 bound →
        F b1 = some (b2, delta))
        (PERM1 : ∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → Plt b2 bound →
          Mem.perm m1 b1 ofs .Max .Nonempty → Mem.perm m b1 ofs .Max .Nonempty)
        (PERM2 : ∀ b ofs, Plt b bound →
          Mem.perm m' b ofs .Cur .Freeable → Mem.perm m1' b ofs .Cur .Freeable)
        (PERM3 : ∀ b ofs k p, Plt b bound →
          Mem.perm m1' b ofs k p → Mem.perm m' b ofs k p),
        match_stacks prog F1 m1 m1' l l0 bound)
    (motive_2 := fun l l0 f c b r _ =>
      ∀ rs2,
        (∀ r0, Plt r0 c.dreg → Regmap.get r0 rs2 = Regmap.get r0 r) →
        (∀ b1 b2 delta, F1 b1 = some (b2, delta) → Ple b2 b →
          F b1 = some (b2, delta)) →
        (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → Ple b2 b →
          Mem.perm m1 b1 ofs .Max .Nonempty → Mem.perm m b1 ofs .Max .Nonempty) →
        (∀ b0 ofs, Ple b0 b → Mem.perm m' b0 ofs .Cur .Freeable →
          Mem.perm m1' b0 ofs .Cur .Freeable) →
        (∀ b0 ofs k p, Ple b0 b → Mem.perm m1' b0 ofs k p →
          Mem.perm m' b0 ofs k p) →
        match_stacks_inside prog F1 m1 m1' l l0 f c b rs2)
    ?_ ?_ ?_ ?_ ?_ hstacks
  · intro bound1 bound0 MG BELOW INJ PERM1 PERM2 PERM3
    rcases MG with ⟨DOMAIN, IMAGE, SYMBOLS, FUNCTIONS, VARINFOS⟩
    apply match_stacks_nil bound1 bound0
    · refine ⟨?_, ?_, SYMBOLS, FUNCTIONS, VARINFOS⟩
      · intro b hb
        exact hIncr b b zZero (DOMAIN b hb)
      · intro b1 b2 delta hmap hlt
        apply IMAGE b1 b2 delta (INJ b1 b2 delta hmap
          (Plt_Ple_trans b2 bound1 bound0 hlt BELOW)) hlt
    · exact BELOW
  · intro res f sp pc rs l f' sp' rs' l' bound0 fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    intro INJ PERM1 PERM2 PERM3
    have MS' := ih rs'
      (by intro r0 _; rfl)
      (by
        intro b1 b2 delta hmap hle
        exact INJ b1 b2 delta hmap (ple_plt_trans_local b2 sp' bound0 hle BELOW))
      (by
        intro b1 b2 delta ofs hmap hle hperm
        exact PERM1 b1 b2 delta ofs hmap
          (ple_plt_trans_local b2 sp' bound0 hle BELOW) hperm)
      (by
        intro b0 ofs hle hperm
        exact PERM2 b0 ofs (ple_plt_trans_local b0 sp' bound0 hle BELOW) hperm)
      (by
        intro b0 ofs k p hle hperm
        exact PERM3 b0 ofs k p (ple_plt_trans_local b0 sp' bound0 hle BELOW) hperm)
    have PRIV' := range_private_invariant_local F m m' sp'
      (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize F1 m1 m1' PRIV
      (by
        intro b1 delta ofs hmap hperm hrange
        exact ⟨INJ b1 sp' delta hmap BELOW,
          PERM1 b1 sp' delta ofs hmap BELOW hperm⟩)
      (by
        intro ofs hperm
        exact PERM2 sp' ofs BELOW hperm)
    apply match_stacks_cons res f sp pc rs l f' sp' rs' l' bound0 fenv ctx
      MS' COMPAT FB (agree_regs_incr F ctx rs rs' F1 AG hIncr)
      (hIncr sp sp' ctx.dstk SP) PRIV' SSZ1
    · intro ofs hperm
      exact SSZ2 ofs (PERM3 sp' ofs .Max .Nonempty BELOW hperm)
    · exact RES
    · exact BELOW
  · intro l res f' sp' rpc rs' l' bound0 ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    intro INJ PERM1 PERM2 PERM3
    have MS' := ih rs'
      (by intro r0 _; rfl)
      (by
        intro b1 b2 delta hmap hle
        exact INJ b1 b2 delta hmap (ple_plt_trans_local b2 sp' bound0 hle BELOW))
      (by
        intro b1 b2 delta ofs hmap hle hperm
        exact PERM1 b1 b2 delta ofs hmap
          (ple_plt_trans_local b2 sp' bound0 hle BELOW) hperm)
      (by
        intro b0 ofs hle hperm
        exact PERM2 b0 ofs (ple_plt_trans_local b0 sp' bound0 hle BELOW) hperm)
      (by
        intro b0 ofs k p hle hperm
        exact PERM3 b0 ofs k p (ple_plt_trans_local b0 sp' bound0 hle BELOW) hperm)
    have PRIV' := range_private_invariant_local F m m' sp' ctx.dstk f'.fn_stacksize F1 m1 m1' PRIV
      (by
        intro b1 delta ofs hmap hperm hrange
        exact ⟨INJ b1 sp' delta hmap BELOW,
          PERM1 b1 sp' delta ofs hmap BELOW hperm⟩)
      (by
        intro ofs hperm
        exact PERM2 sp' ofs BELOW hperm)
    apply match_stacks_untailcall l res f' sp' rpc rs' l' bound0 ctx
      MS' PRIV' SSZ1
    · intro ofs hperm
      exact SSZ2 ofs (PERM3 sp' ofs .Max .Nonempty BELOW hperm)
    · exact RET
    · exact BELOW
  · intro l l' f' c sp' rs' MS RET DSTK ih
    intro rs2 RS INJ PERM1 PERM2 PERM3
    apply match_stacks_inside_base l l' f' c sp' rs2
    · apply ih
      · intro b1 b2 delta hmap hlt
        exact INJ b1 b2 delta hmap (Plt_Ple _ _ hlt)
      · intro b1 b2 delta ofs hmap hlt hperm
        exact PERM1 b1 b2 delta ofs hmap (Plt_Ple _ _ hlt) hperm
      · intro b0 ofs hlt hperm
        exact PERM2 b0 ofs (Plt_Ple _ _ hlt) hperm
      · intro b0 ofs k p hlt hperm
        exact PERM3 b0 ofs k p (Plt_Ple _ _ hlt) hperm
    · exact RET
    · exact DSTK
  · intro res f sp pc rs l l' f' fenv c sp' rs' c' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    intro rs2 RS INJ PERM1 PERM2 PERM3
    have MS' := ih rs2
      (by
        intro r0 hlt
        apply RS r0
        exact Plt_Ple_trans r0 (PArith.BinPos.Pos.add c'.dreg c'.mreg) c.dreg
          (Plt_trans r0 c'.dreg (PArith.BinPos.Pos.add c'.dreg c'.mreg) hlt
            (plt_add_right_local c'.dreg c'.mreg)) BELOW)
      INJ PERM1 PERM2 PERM3
    have AG0 := agree_regs_invariant F c' rs rs' rs2 AG (by
      intro r0 hle hlt
      apply RS r0
      exact Plt_Ple_trans r0 (PArith.BinPos.Pos.add c'.dreg c'.mreg) c.dreg hlt BELOW)
    have AG' := agree_regs_incr F c' rs rs2 F1 AG0 hIncr
    have PAD' := range_private_invariant_local F m m' sp'
      (zAdd c'.dstk c'.mstk) c.dstk F1 m1 m1' PAD
      (by
        intro b1 delta ofs hmap hperm hrange
        exact ⟨INJ b1 sp' delta hmap (Ple_refl sp'),
          PERM1 b1 sp' delta ofs hmap (Ple_refl sp') hperm⟩)
      (by
        intro ofs hperm
        exact PERM2 sp' ofs (Ple_refl sp') hperm)
    exact match_stacks_inside_inlined res f sp pc rs l l' f' fenv c sp' rs2 c'
      MS' COMPAT FB AG' (hIncr sp sp' c'.dstk SP) PAD' RES RET BELOW SBELOW

private theorem match_stacks_alloc_left_at_bound_local
    (prog : program) (F : Val.meminj) (m m' : mem)
    (stk stk' : List stackframe) (bound sp' : block)
    (hnot : ¬ Plt sp' bound)
    (h : match_stacks prog F m m' stk stk' bound)
    (sz : Z) (m1 : mem) (b : block) (F1 : Val.meminj) (delta : Z)
    (halloc : Mem.alloc m zZero sz = (m1, b))
    (hIncr : inject_incr F F1)
    (hmap : F1 b = some (sp', delta))
    (hsame : ∀ b1, b1 ≠ b → F1 b1 = F b1) :
    match_stacks prog F1 m1 m' stk stk' bound := by
  apply match_stacks_invariant_local prog F m m' F1 m1 m' hIncr
    stk stk' bound h
  · intro b1 b2 d hF hlt
    cases hb : eq_block b1 b with
    | left hbeq =>
        subst b1
        rw [hmap] at hF
        cases hF
        exact False.elim (hnot hlt)
    | right hbneq =>
        rw [← hsame b1 hbneq]
        exact hF
  · intro b1 b2 d ofs hF hlt hperm
    have hinv := mem_perm_alloc_inv_local m zZero sz m1 b halloc
      b1 ofs .Max .Nonempty hperm
    cases hb : eq_block b1 b with
    | left hbeq =>
        subst b1
        rw [hmap] at hF
        cases hF
        exact False.elim (hnot hlt)
    | right hbneq =>
        simpa [hb] using hinv
  · intro b0 ofs hlt hperm
    exact hperm
  · intro b0 ofs k p hlt hperm
    exact hperm

theorem match_stacks_inside_alloc_left : match_stacks_inside_alloc_leftStatement := by
  intro prog F m m' stk stk' f' ctx sp' rs' h
  intro sz m1 b F1 delta halloc hIncr hmap hsame hdelta
  refine match_stacks_inside.rec (prog := prog) (F := F) (m := m) (m' := m')
    (motive_1 := fun l l0 bound _ =>
      (¬ Plt bound bound) →
      Mem.alloc m zZero sz = (m1, b) → inject_incr F F1 →
      F1 b = some (bound, delta) →
      (∀ b1, b1 ≠ b → F1 b1 = F b1) →
      match_stacks prog F1 m1 m' l l0 bound)
    (motive_2 := fun l l0 f c bound r _ =>
      Mem.alloc m zZero sz = (m1, b) → inject_incr F F1 →
      F1 b = some (bound, delta) →
      (∀ b1, b1 ≠ b → F1 b1 = F b1) →
      (¬ Plt bound bound) →
      zLe c.dstk delta →
      match_stacks_inside prog F1 m1 m' l l0 f c bound r)
    ?_ ?_ ?_ ?_ ?_ h halloc hIncr hmap hsame (by exact Plt_strict _) hdelta
  · intro bound1 bound MG BELOW hnot halloc hIncr hmap hsame
    exact match_stacks_alloc_left_at_bound_local prog F m m' [] [] bound bound
      hnot (match_stacks_nil bound1 bound MG BELOW)
      sz m1 b F1 delta halloc hIncr hmap hsame
  · intro res f sp pc rs l f' sp' rs' l' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    intro hnot halloc hIncr hmap hsame
    exact match_stacks_alloc_left_at_bound_local prog F m m'
      (Stackframe res f (Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero) pc rs :: l)
      (Stackframe (sreg ctx res)
        f' (Vptr sp' CompCert4Lean.Lib.Integers.Ptrofs.zero) (spc ctx pc) rs' :: l')
      bound bound hnot
      (match_stacks_cons res f sp pc rs l f' sp' rs' l' bound fenv ctx
        MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW)
      sz m1 b F1 delta halloc hIncr hmap hsame
  · intro l res f' sp' rpc rs' l' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    intro hnot halloc hIncr hmap hsame
    exact match_stacks_alloc_left_at_bound_local prog F m m'
      l (Stackframe res f' (Vptr sp' CompCert4Lean.Lib.Integers.Ptrofs.zero) rpc rs' :: l') bound bound hnot
      (match_stacks_untailcall l res f' sp' rpc rs' l' bound ctx
        MS PRIV SSZ1 SSZ2 RET BELOW)
      sz m1 b F1 delta halloc hIncr hmap hsame
  · intro l l' f' c sp0 rs' MS RET DSTK ih
    intro halloc hIncr hmap hsame hnot hdelta
    exact match_stacks_inside_base l l' f' c sp0 rs'
      (ih hnot halloc hIncr hmap hsame) RET DSTK
  · intro res f sp pc rs l l' f' fenv c0 sp0 rs' c' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    intro halloc hIncr hmap hsame hnot hdelta
    have hdelta' : zLe c'.dstk delta := by
      rcases SBELOW with ⟨hmstk, hstack⟩
      change 0 ≤ intOfZ c'.mstk at hmstk
      change intOfZ (zAdd c'.dstk c'.mstk) ≤ intOfZ c0.dstk at hstack
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hstack
      change intOfZ c0.dstk ≤ intOfZ delta at hdelta
      change intOfZ c'.dstk ≤ intOfZ delta
      omega
    have MS' := ih halloc hIncr hmap hsame (by exact Plt_strict _) hdelta'
    have AG' := agree_regs_incr F c' rs rs' F1 AG hIncr
    have PAD' := range_private_invariant_local F m m' sp0
      (zAdd c'.dstk c'.mstk) c0.dstk F1 m1 m' PAD
      (by
        intro b1 delta0 ofs hmap0 hperm0 hrange
        cases hb : eq_block b1 b with
        | left hbeq =>
            subst b1
            have hinv := mem_perm_alloc_inv_local m zZero sz m1 b halloc
              b ofs .Max .Nonempty hperm0
            have hinv' : zLe zZero ofs ∧ zLt ofs sz := by
              simpa [hb] using hinv
            have hnonneg : zLe zZero ofs := hinv'.1
            have hsum : zLe c0.dstk (zAdd ofs delta0) := by
              have : zLe c0.dstk delta := hdelta
              have hdelta0 : delta0 = delta := by
                rw [hmap] at hmap0
                cases hmap0
                rfl
              subst delta0
              change intOfZ c0.dstk ≤ intOfZ (zAdd ofs delta)
              simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
              change intOfZ c0.dstk ≤ intOfZ ofs + intOfZ delta
              change intOfZ c0.dstk ≤ intOfZ delta at this
              have hofs0 : 0 ≤ intOfZ ofs := by
                change 0 ≤ intOfZ ofs at hnonneg
                exact hnonneg
              omega
            have hlt' : intOfZ (zAdd ofs delta0) < intOfZ c0.dstk := by
              have hlt0 := hrange.2
              change intOfZ (zAdd ofs delta0) < intOfZ c0.dstk at hlt0
              exact hlt0
            have hge' : intOfZ c0.dstk ≤ intOfZ (zAdd ofs delta0) := by
              change intOfZ c0.dstk ≤ intOfZ (zAdd ofs delta0)
              exact hsum
            exact False.elim (by omega)
        | right hbneq =>
            have hF : F b1 = some (sp0, delta0) := by
              rw [← hsame b1 hbneq]
              exact hmap0
            exact ⟨hF, by
              have hinv := mem_perm_alloc_inv_local m zZero sz m1 b halloc
                b1 ofs .Max .Nonempty hperm0
              simpa [hb] using hinv⟩)
      (by intro ofs hperm; exact hperm)
    exact match_stacks_inside_inlined res f sp pc rs l l' f' fenv c0 sp0 rs' c'
      MS' COMPAT FB AG' (hIncr sp sp0 c'.dstk SP) PAD' RES RET BELOW SBELOW

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

theorem match_stacks_inside_extcall : match_stacks_inside_extcallStatement := by
  intro prog F1 F2 m1 m2 m1' m2' MAXPERM MAXPERM' UNCHANGED INJ INCR SEP
  intro stk stk' f' ctx sp' rs' hstacks hsp
  refine match_stacks_inside.rec (prog := prog) (F := F1) (m := m1) (m' := m1')
    (motive_1 := fun l l0 bound _ =>
      Ple bound m1'.nextblock → match_stacks prog F2 m2 m2' l l0 bound)
    (motive_2 := fun l l0 f c sp r _ =>
      Plt sp m1'.nextblock → match_stacks_inside prog F2 m2 m2' l l0 f c sp r)
    ?_ ?_ ?_ ?_ ?_ hstacks hsp
  · intro bound1 bound MG BELOW hbound
    rcases MG with ⟨DOMAIN, IMAGE, SYMBOLS, FUNCTIONS, VARINFOS⟩
    apply match_stacks_nil bound1 bound
    · refine ⟨?_, ?_, SYMBOLS, FUNCTIONS, VARINFOS⟩
      · intro b hb
        exact INCR b b zZero (DOMAIN b hb)
      · intro b1 b2 delta hmap hlt
        cases hF1 : F1 b1 with
        | some p =>
            rcases p with ⟨b2', delta'⟩
            have hmap' := INCR b1 b2' delta' hF1
            have hp : (b2', delta') = (b2, delta) :=
              Option.some.inj (hmap'.symm.trans hmap)
            rcases hp with ⟨rfl, rfl⟩
            exact IMAGE b1 b2 delta hF1 hlt
        | none =>
            have hsep := SEP b1 b2 delta hF1 hmap
            have hvalid : Mem.valid_block m1' b2 :=
              Plt_Ple_trans b2 bound1 m1'.nextblock hlt
                (Ple_trans bound1 bound m1'.nextblock BELOW hbound)
            exact False.elim (hsep.2 hvalid)
    · exact BELOW
  · intro res f sp pc rs l f' sp' rs' l' bound fenv ctx MS COMPAT FB AG SP PRIV SSZ1 SSZ2 RES BELOW ih
    intro hbound
    have hvalid : Mem.valid_block m1' sp' :=
      Plt_Ple_trans sp' bound m1'.nextblock BELOW hbound
    apply match_stacks_cons res f sp pc rs l f' sp' rs' l' bound fenv ctx
    · exact ih hvalid
    · exact COMPAT
    · exact FB
    · exact agree_regs_incr F1 ctx rs rs' F2 AG INCR
    · exact INCR sp sp' ctx.dstk SP
    · exact range_private_extcall F1 F2 m1 m2 m1' m2' sp'
        (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize PRIV MAXPERM UNCHANGED INJ INCR SEP hvalid
    · exact SSZ1
    · intro ofs hperm
      exact SSZ2 ofs (MAXPERM' sp' ofs .Nonempty hvalid hperm)
    · exact RES
    · exact BELOW
  · intro l res f' sp' rpc rs' l' bound ctx MS PRIV SSZ1 SSZ2 RET BELOW ih
    intro hbound
    have hvalid : Mem.valid_block m1' sp' :=
      Plt_Ple_trans sp' bound m1'.nextblock BELOW hbound
    apply match_stacks_untailcall l res f' sp' rpc rs' l' bound ctx
    · exact ih hvalid
    · exact range_private_extcall F1 F2 m1 m2 m1' m2' sp'
        ctx.dstk f'.fn_stacksize PRIV MAXPERM UNCHANGED INJ INCR SEP hvalid
    · exact SSZ1
    · intro ofs hperm
      exact SSZ2 ofs (MAXPERM' sp' ofs .Nonempty hvalid hperm)
    · exact RET
    · exact BELOW
  · intro l l' f' c sp' rs' MS RET DSTK ih
    intro hvalid
    exact match_stacks_inside_base l l' f' c sp' rs'
      (ih (Plt_Ple sp' m1'.nextblock hvalid)) RET DSTK
  · intro res f sp pc rs l l' f' fenv c sp' rs' c' MS COMPAT FB AG SP PAD RES RET BELOW SBELOW ih
    intro hvalid
    exact match_stacks_inside_inlined res f sp pc rs l l' f' fenv c sp' rs' c'
      (ih hvalid) COMPAT FB
      (agree_regs_incr F1 c' rs rs' F2 AG INCR)
      (INCR sp sp' c'.dstk SP)
      (range_private_extcall F1 F2 m1 m2 m1' m2' sp'
        (zAdd c'.dstk c'.mstk) c.dstk PAD MAXPERM UNCHANGED INJ INCR SEP hvalid)
      RES RET BELOW SBELOW

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

theorem align_unchanged : align_unchangedStatement := by
  intro n amount hpos hdiv
  rcases hdiv with ⟨k, hk⟩
  change 0 < intOfZ amount at hpos
  rw [hk]
  unfold CompCert4Lean.Lib.Coqlib.align
  have hq :
      ZArith.BinInt.Z.div
          (ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.mul amount k) amount)
            (Zpos xH)) amount = k := by
    apply CompCert4Lean.Lib.Coqlib.Zdiv_unique
        (ZArith.BinInt.Z.sub
          (ZArith.BinInt.Z.add
            (ZArith.BinInt.Z.mul amount k) amount)
          (Zpos xH)) amount k
        (ZArith.BinInt.Z.sub amount (Zpos xH))
    · apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
        ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      change intOfZ amount * intOfZ k + intOfZ amount - 1 =
        intOfZ k * intOfZ amount + (intOfZ amount - 1)
      rw [Int.mul_comm (intOfZ amount) (intOfZ k)]
      omega
    · constructor
      · change 0 ≤ intOfZ (ZArith.BinInt.Z.sub amount (Zpos xH))
        simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change 0 ≤ intOfZ amount - 1
        omega
      · change intOfZ (ZArith.BinInt.Z.sub amount (Zpos xH)) < intOfZ amount
        simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change intOfZ amount - 1 < intOfZ amount
        omega
  rw [hq]
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  exact Int.mul_comm _ _

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

theorem tr_funbody_inv : tr_funbody_invStatement := by
  intro fenv sz ctx f c pc i hbody hget
  cases hbody with
  | tr_funbody_intro ctx f c hparams hinstr hstk hdiv hnonneg hsize =>
      exact hinstr pc i hget

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

theorem transf_final_states : transf_final_statesStatement := by
  intro cfg prog st1 st2 r hmatch hfinal
  cases hfinal with
  | intro r m =>
      cases hmatch with
      | match_return_states stk v m stk' v' m' F hstacks hinj hmem =>
          have hstk : stk' = [] :=
            match_stacks_empty prog F m m' [] stk' m'.nextblock hstacks rfl
          subst stk'
          cases hinj
          exact CompCert4Lean.Backend.RTL.final_state.intro r m'
      | match_return_regular_states stk v m stk' f' sp' rs' m' F ctx pc' or rinfo
          hinside hret hcode hv hinj hvalid hprivate hsize hperms =>
          have hstk := match_stacks_inside_empty prog F m m' [] stk' f' ctx sp' rs'
            hinside rfl
          cases hstk.1
          have hfalse := hret.symm.trans hstk.2
          cases hfalse

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

theorem range_private_invariant : range_private_invariantStatement :=
  range_private_invariant_local

end CompCert4Lean.Backend.Inliningproof

namespace CompCert4Lean.Backend.Inliningproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem range_private_free_left : range_private_free_leftStatement := by
  intro F m m' sp base sz hi b m1 hpriv hfree hmap hinj
  unfold range_private loc_private at hpriv ⊢
  intro ofs hofs
  rcases hofs with ⟨hofs_lo, hofs_hi⟩
  have hz0 : intOfZ zZero = 0 := by rfl
  have hmax0 : zLe zZero (ZArith.BinInt.Z.max sz zZero) := by
    change 0 ≤ intOfZ (ZArith.BinInt.Z.max sz zZero)
    by_cases h : intOfZ sz ≤ 0
    · simp [ZArith.BinInt.Z.max, h, hz0]
    · simp [ZArith.BinInt.Z.max, h, Int.le_of_not_le h, hz0]
  have hmax : zLe sz (ZArith.BinInt.Z.max sz zZero) := by
    change intOfZ sz ≤ intOfZ (ZArith.BinInt.Z.max sz zZero)
    by_cases h : intOfZ sz ≤ 0
    · simp [ZArith.BinInt.Z.max, h, hz0]
    · simp [ZArith.BinInt.Z.max, h, Int.le_of_not_le h, hz0]
  have hbase_int : intOfZ base ≤ intOfZ ofs := by
    simpa only [zLe, ZArith.BinInt.Z.le] using hofs_lo
  have hhi_int : intOfZ ofs < intOfZ hi := by
    simpa only [zLt, ZArith.BinInt.Z.lt] using hofs_hi
  have hmax0_int : 0 ≤ intOfZ (ZArith.BinInt.Z.max sz zZero) := by
    simpa only [zLe, ZArith.BinInt.Z.le, hz0] using hmax0
  have hmax_int : intOfZ sz ≤ intOfZ (ZArith.BinInt.Z.max sz zZero) := by
    simpa only [zLe, ZArith.BinInt.Z.le] using hmax
  by_cases hbelow : zLt ofs (zAdd base (ZArith.BinInt.Z.max sz zZero))
  · have hbelow_int : intOfZ ofs <
        intOfZ base + intOfZ (ZArith.BinInt.Z.max sz zZero) := by
      simpa only [zLt, zAdd, ZArith.BinInt.Z.lt, ZArith.BinInt.Z.add,
        intOfZ_zOfInt] using hbelow
    have hsublo_int : 0 ≤ intOfZ (zSub ofs base) := by
      simpa only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] using
        (show 0 ≤ intOfZ ofs - intOfZ base by omega)
    have hsubhi_int : intOfZ (zSub ofs base) < intOfZ sz := by
      have hsubhi' : intOfZ ofs - intOfZ base < intOfZ sz := by
        by_cases hsz : intOfZ sz ≤ 0
        · have hmax_eq : intOfZ (ZArith.BinInt.Z.max sz zZero) = 0 := by
            simp [ZArith.BinInt.Z.max, hsz, hz0]
          omega
        · have hmax_eq : intOfZ (ZArith.BinInt.Z.max sz zZero) = intOfZ sz := by
            simp [ZArith.BinInt.Z.max, hsz, Int.le_of_not_le hsz, hz0]
          omega
      simpa only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] using hsubhi'
    have hsublo : zLe zZero (zSub ofs base) := by
      simpa only [zLe, zSub, ZArith.BinInt.Z.le,
        ZArith.BinInt.Z.sub, intOfZ_zOfInt, hz0] using hsublo_int
    have hsubhi : zLt (zSub ofs base) sz := by
      simpa only [zLt, zSub, ZArith.BinInt.Z.lt,
        ZArith.BinInt.Z.sub, intOfZ_zOfInt] using hsubhi_int
    constructor
    · have hfreeperm := Mem.free_range_perm m b zZero sz m1 hfree
      have hsrc := hfreeperm (zSub ofs base) ⟨hsublo, hsubhi⟩
      have hdst := hinj.mi_inj.mi_perm b sp base (zSub ofs base) Cur Freeable hmap hsrc
      change Mem.perm m' sp
        (ZArith.BinInt.Z.add (ZArith.BinInt.Z.sub ofs base) base)
        Cur Freeable at hdst
      have heq : ZArith.BinInt.Z.add (ZArith.BinInt.Z.sub ofs base) base = ofs := by
        apply intOfZ_injective
        simp only [zAdd, zSub, ZArith.BinInt.Z.add,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
      rw [heq] at hdst
      exact hdst
    · intro b0 delta hF hperm
      by_cases hb : b0 = b
      · subst b0
        rw [hmap] at hF
        cases hF
        exact Mem.perm_free_2 m b zZero sz m1 hfree
          (zSub ofs base) Max Nonempty ⟨hsublo, hsubhi⟩ hperm
      · have hperm_old : Mem.perm m b0 (zSub ofs delta) Max Nonempty :=
          Mem.perm_free_3 m b zZero sz m1 hfree b0 (zSub ofs delta)
            Max Nonempty hperm
        have hfreeperm := Mem.free_range_perm m b zZero sz m1 hfree
        have hsrc := hfreeperm (zSub ofs base) ⟨hsublo, hsubhi⟩
        have hsrc_max : Mem.perm m b (zSub ofs base) Max Nonempty :=
          Mem.perm_implies m b (zSub ofs base) Max Freeable Nonempty
            (Mem.perm_cur_max m b (zSub ofs base) Freeable hsrc)
            (perm_any_N Freeable)
        have hb' : b ≠ b0 := by
          intro heq
          exact hb heq.symm
        have hcontra := hinj.mi_no_overlap b sp base b0 sp delta
          (zSub ofs base) (zSub ofs delta) hb' hmap hF hsrc_max hperm_old
        rcases hcontra with hne | hne
        · exact (hne rfl).elim
        · apply hne
          apply intOfZ_injective
          simp only [zAdd, zSub, ZArith.BinInt.Z.add,
            ZArith.BinInt.Z.sub, intOfZ_zOfInt]
          omega
  · have hlow_int : intOfZ base + intOfZ (ZArith.BinInt.Z.max sz zZero) ≤
        intOfZ ofs := by
      have hn : ¬ intOfZ ofs <
          intOfZ base + intOfZ (ZArith.BinInt.Z.max sz zZero) := by
        intro hh
        apply hbelow
        simpa only [zLt, zAdd, ZArith.BinInt.Z.lt,
          ZArith.BinInt.Z.add, intOfZ_zOfInt] using hh
      omega
    have hlow : zLe (zAdd base (ZArith.BinInt.Z.max sz zZero)) ofs := by
      simpa only [zLe, zAdd, ZArith.BinInt.Z.le,
        ZArith.BinInt.Z.add, intOfZ_zOfInt] using hlow_int
    have horig := hpriv ofs ⟨hlow, hofs_hi⟩
    constructor
    · exact horig.1
    · intro b0 delta hF hperm
      exact horig.2 b0 delta hF
        (Mem.perm_free_3 m b zZero sz m1 hfree b0 (zSub ofs delta)
          Max Nonempty hperm)

end CompCert4Lean.Backend.Inliningproof
namespace CompCert4Lean.Backend.Inliningproof
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open Lean Elab Tactic Meta
private def pgPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base
private theorem pg_wordcore_val_repr (bits : Nat) (i : Int) :
    (WordCore.repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let e ← mkAppM
      (pgPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[mkFVar bF.fvarId, mkFVar iF.fvarId]
    closeMainGoal Name.anonymous e
private theorem pg_wordcore_intval_eq_zOfNat_val {bits : Nat} (x : WordCore.Word bits) :
    x.intval = ZArith.BinInt.Z.of_nat x.val := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (pgPrivateName "CompCert4Lean.Lib.Integers.WordCore.intval_eq_zOfNat_val")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e
private theorem pg_ptrofs_modulus :
    Ptrofs.modulus = ZArith.BinInt.Z.of_nat (2 ^ Ptrofs.wordsize) := by
  unfold Ptrofs.modulus
  run_tac
    let e ← mkAppM
      (pgPrivateName "CompCert4Lean.Lib.Integers.WordCore.twoPowerNat_eq_zOfNat_twoPow")
      #[mkConst ``CompCert4Lean.Lib.Integers.Ptrofs.wordsize]
    closeMainGoal Name.anonymous e


private theorem pg_wordcore_add_val {bits : Nat} (x y : WordCore.Word bits) :
    (WordCore.add x y).val = (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (pgPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e
private theorem pg_wordcore_val_lt {bits : Nat} (x : WordCore.Word bits) :
    x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (pgPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e
private theorem pg_wordcore_zero_val (bits : Nat) :
    (WordCore.zero bits).val = 0 := by
  unfold WordCore.zero
  change (WordCore.repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat 0))).val = 0
  simpa using pg_wordcore_val_repr bits 0
private theorem pg_ptr_add_zero (x : Ptrofs.int) :
    Ptrofs.add x Ptrofs.zero = x := by
  change WordCore.add x (WordCore.zero Ptrofs.wordsize) = x
  apply WordCore.ext_of_val_eq
  rw [pg_wordcore_add_val, pg_wordcore_zero_val]
  exact Nat.mod_eq_of_lt (pg_wordcore_val_lt x)
private theorem pg_ptr_add_zero_repr (x : Ptrofs.int) :
    Ptrofs.add x (Ptrofs.repr (.Z0)) = x := by
  change WordCore.add x (WordCore.repr Ptrofs.wordsize (.Z0)) = x
  apply WordCore.ext_of_val_eq
  rw [pg_wordcore_add_val]
  have hz : (WordCore.repr Ptrofs.wordsize (.Z0)).val = 0 := by
    change (WordCore.repr Ptrofs.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat 0))).val = 0
    simpa using pg_wordcore_val_repr Ptrofs.wordsize 0
  rw [hz, Nat.add_zero]
  exact Nat.mod_eq_of_lt (pg_wordcore_val_lt x)
private theorem pg_ptr_add_zero_l (x : Ptrofs.int) :
    Ptrofs.add Ptrofs.zero x = x := by
  rw [Ptrofs.add_commut_proof_api]
  exact pg_ptr_add_zero x

private theorem pg_ptr_unsigned_repr (z : Z)
    (hz : ZArith.BinInt.Z.le (.Z0) z ∧ ZArith.BinInt.Z.le z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have hznonneg : 0 ≤ intOfZ z := by
    have hz0 := hz.1
    change 0 ≤ intOfZ z at hz0
    exact hz0
  have hzlt : intOfZ z < ((2 ^ Ptrofs.wordsize : Nat) : Int) := by
    have hzmax := hz.2
    change intOfZ z ≤ intOfZ Ptrofs.max_unsigned at hzmax
    change intOfZ z ≤ intOfZ (Ptrofs.max_unsigned) at hzmax
    unfold Ptrofs.max_unsigned at hzmax
    change intOfZ z ≤ intOfZ (ZArith.BinInt.Z.sub Ptrofs.modulus (.Zpos xH)) at hzmax
    rw [pg_ptrofs_modulus] at hzmax
    change intOfZ z ≤ Int.ofNat (2 ^ Ptrofs.wordsize) - 1 at hzmax
    have hzmax' : intOfZ z ≤ ((2 ^ Ptrofs.wordsize : Nat) : Int) - 1 := by
      simpa only [Int.ofNat_eq_natCast] using hzmax
    omega
  change (WordCore.repr Ptrofs.wordsize z).intval = z
  rw [pg_wordcore_intval_eq_zOfNat_val]
  have hval :
      (WordCore.repr Ptrofs.wordsize z).val =
        Int.toNat (intOfZ z % ((2 ^ Ptrofs.wordsize : Nat) : Int)) := by
    rw [← zOfInt_intOfZ z]
    simpa only [intOfZ_zOfInt] using pg_wordcore_val_repr Ptrofs.wordsize (intOfZ z)
  rw [hval, Int.emod_eq_of_lt hznonneg hzlt]
  change zOfInt (Int.ofNat (Int.toNat (intOfZ z))) = z
  calc
    _ = zOfInt (intOfZ z) := congrArg zOfInt (Int.toNat_of_nonneg hznonneg)
    _ = z := zOfInt_intOfZ z

end CompCert4Lean.Backend.Inliningproof
namespace CompCert4Lean.Backend.Inliningproof
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
private theorem pg_address_inject
    (f : Val.meminj) (m1 m2 : mem) (b1 : block) (ofs1 : Ptrofs.int)
    (b2 : block) (delta : Z) (p : CompCert4Lean.Common.Memtype.permission) :
    Mem.inject f m1 m2 →
    Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur p →
    f b1 = some (b2, delta) →
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
      ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) delta := by
  intro hinj hperm hmap
  have hpmax : Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty := by
    exact Mem.perm_implies m1 b1 (Ptrofs.unsigned ofs1) Max p Nonempty
      (Mem.perm_cur_max m1 b1 (Ptrofs.unsigned ofs1) p hperm)
      (perm_any_N p)
  have hrep := hinj.mi_representable b1 b2 delta ofs1 hmap (Or.inl hpmax)
  have hdelta0 : 0 ≤ intOfZ delta := by
    change 0 ≤ intOfZ delta
    exact hrep.1
  have hsum0 : 0 ≤ intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) delta) := by
    change 0 ≤ intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) delta)
    exact hrep.2.1
  have hsummax : intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) delta) ≤
      intOfZ Ptrofs.max_unsigned := by
    simpa only [ZArith.BinInt.Z.le] using hrep.2.2
  have hofs0 : 0 ≤ intOfZ (Ptrofs.unsigned ofs1) := by
    have h := ofs1.intrange.1
    change (-1 : Int) < intOfZ (Ptrofs.unsigned ofs1) at h
    omega
  have hdeltaMax : intOfZ delta ≤ intOfZ Ptrofs.max_unsigned := by
    have hsum := hsummax
    have hadd := hsum0
    have haddI : intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) delta) =
        intOfZ (Ptrofs.unsigned ofs1) + intOfZ delta := by
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega
  have hu_delta : Ptrofs.unsigned (Ptrofs.repr delta) = delta :=
    pg_ptr_unsigned_repr delta (by
      constructor
      · exact hdelta0
      · exact hdeltaMax)
  have haddrepr : Ptrofs.add ofs1 (Ptrofs.repr delta) =
      Ptrofs.repr (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1)
        (Ptrofs.unsigned (Ptrofs.repr delta))) := by rfl
  rw [haddrepr]
  have hsummax' : ZArith.BinInt.Z.le (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) delta)
      Ptrofs.max_unsigned := hrep.2.2
  rw [hu_delta]
  apply pg_ptr_unsigned_repr
  constructor
  · exact hsum0
  · exact hsummax'

end CompCert4Lean.Backend.Inliningproof
namespace CompCert4Lean.Backend.Inliningproof
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
private theorem pg_loadv_inject
    (f : Val.meminj) (m1 m2 : mem) (chunk : memory_chunk)
    (a1 a2 : val) (v1 : val) :
    Mem.inject f m1 m2 →
    Mem.loadv chunk m1 a1 = some v1 →
    Val.inject f a1 a2 →
    ∃ v2, Mem.loadv chunk m2 a2 = some v2 ∧ Val.inject f v1 v2 := by
  intro hinj hload haddr
  cases a1 with
  | Vptr b1 ofs1 =>
      cases a2 with
      | Vptr b2 ofs2 =>
          cases haddr with
          | inject_ptr _ _ _ _ delta hmap hofs =>
              have hacc := Mem.load_valid_access m1 chunk b1
                (Ptrofs.unsigned ofs1) v1 (by simpa [Mem.loadv] using hload)
              have hp : Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur Readable := by
                apply hacc.1 (Ptrofs.unsigned ofs1)
                constructor
                · exact ZArith.BinInt.Z.le_refl _
                · have hs := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
                  change intOfZ (Ptrofs.unsigned ofs1) <
                    intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) (size_chunk chunk))
                  have hs' : 0 < intOfZ (size_chunk chunk) := by
                    have hs0 := hs
                    change 0 < intOfZ (size_chunk chunk) at hs0
                    exact hs0
                  have hadd : intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs1) (size_chunk chunk)) =
                      intOfZ (Ptrofs.unsigned ofs1) + intOfZ (size_chunk chunk) := by
                    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
                  rw [hadd]
                  omega
              have haddr' := pg_address_inject f m1 m2 b1 ofs1 b2 delta
                Readable hinj hp hmap
              obtain ⟨v2, hload2, hinj2⟩ :=
                Mem.load_inj f m1 m2 chunk b1 (Ptrofs.unsigned ofs1)
                  b2 delta v1 hinj.mi_inj
                  (by simpa [Mem.loadv] using hload) hmap
              refine ⟨v2, ?_, hinj2⟩
              simpa [Mem.loadv, hofs, haddr'] using hload2
      | Vundef => cases haddr
      | Vint _ => cases haddr
      | Vlong _ => cases haddr
      | Vfloat _ => cases haddr
      | Vsingle _ => cases haddr
  | Vundef => cases haddr <;> simp [Mem.loadv] at hload
  | Vint _ => cases haddr <;> simp [Mem.loadv] at hload
  | Vlong _ => cases haddr <;> simp [Mem.loadv] at hload
  | Vfloat _ => cases haddr <;> simp [Mem.loadv] at hload
  | Vsingle _ => cases haddr <;> simp [Mem.loadv] at hload
end CompCert4Lean.Backend.Inliningproof
namespace CompCert4Lean.Backend.Inliningproof
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
theorem tr_builtin_arg : tr_builtin_argStatement := by
  intro cfg prog tprog hm F bound ctx rs rs' sp sp' m m' a v hMG hregs hsp hmem hEval
  rcases hMG with ⟨hdom, himage, hsymbols, hfunctions, hvarinfos⟩
  induction hEval with
  | eval_BA x =>
      refine ⟨Regmap.get (sreg ctx x) rs', ?_, ?_⟩
      · simpa [sbuiltinarg] using
          (eval_BA (ge := Genv.to_senv (Genv.globalenv tprog))
            (e := fun r => Regmap.get r rs') (sp := Vptr sp' Ptrofs.zero)
            (m := m') (sreg ctx x))
      · exact agree_val_reg F ctx rs rs' x hregs
  | eval_BA_int n => exact ⟨Vint n, eval_BA_int _, Val.inject_int F n⟩
  | eval_BA_long n => exact ⟨Vlong n, eval_BA_long _, Val.inject_long F n⟩
  | eval_BA_float n => exact ⟨Vfloat n, eval_BA_float _, Val.inject_float F n⟩
  | eval_BA_single n => exact ⟨Vsingle n, eval_BA_single _, Val.inject_single F n⟩
  | eval_BA_loadstack chunk ofs v load =>
      have hbase : Val.inject F (Vptr sp Ptrofs.zero)
          (Vptr sp' (Ptrofs.add Ptrofs.zero (Ptrofs.repr ctx.dstk))) := by
        exact Val.inject_ptr F sp Ptrofs.zero sp'
          (Ptrofs.add Ptrofs.zero (Ptrofs.repr ctx.dstk)) ctx.dstk hsp rfl
      have haddr0 := Val.offset_ptr_inject F _ _ ofs hbase
      have heq :
          Val.offset_ptr (Vptr sp' (Ptrofs.add Ptrofs.zero (Ptrofs.repr ctx.dstk))) ofs =
            Val.offset_ptr (Vptr sp' Ptrofs.zero)
              (Ptrofs.add ofs (Ptrofs.repr ctx.dstk)) := by
        simp [Val.offset_ptr]
        simp only [pg_ptr_add_zero_l]
        rw [Ptrofs.add_commut_proof_api]
      obtain ⟨v', hload', hinj'⟩ :=
        pg_loadv_inject F m m' chunk
          (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs)
          (Val.offset_ptr (Vptr sp' Ptrofs.zero)
            (Ptrofs.add ofs (Ptrofs.repr ctx.dstk))) v hmem load (by
              simpa [heq] using haddr0)
      refine ⟨v', ?_, hinj'⟩
      apply eval_BA_loadstack
      simpa [heq] using hload'
  | eval_BA_addrstack ofs =>
      have hbase : Val.inject F (Vptr sp Ptrofs.zero)
          (Vptr sp' (Ptrofs.add Ptrofs.zero (Ptrofs.repr ctx.dstk))) := by
        exact Val.inject_ptr F sp Ptrofs.zero sp'
          (Ptrofs.add Ptrofs.zero (Ptrofs.repr ctx.dstk)) ctx.dstk hsp rfl
      have haddr0 := Val.offset_ptr_inject F _ _ ofs hbase
      have heq :
          Val.offset_ptr (Vptr sp' (Ptrofs.add Ptrofs.zero (Ptrofs.repr ctx.dstk))) ofs =
            Val.offset_ptr (Vptr sp' Ptrofs.zero)
              (Ptrofs.add ofs (Ptrofs.repr ctx.dstk)) := by
        simp [Val.offset_ptr]
        simp only [pg_ptr_add_zero_l]
        rw [Ptrofs.add_commut_proof_api]
      refine ⟨Val.offset_ptr (Vptr sp' Ptrofs.zero)
        (Ptrofs.add ofs (Ptrofs.repr ctx.dstk)), ?_, ?_⟩
      · exact eval_BA_addrstack _
      · simpa [heq] using haddr0
  | eval_BA_loadglobal chunk id ofs v load =>
      change Mem.loadv chunk m
        (Genv.symbol_address (Genv.globalenv prog) id ofs) = some v at load
      cases hfind : Genv.find_symbol (Genv.globalenv prog) id with
      | none =>
          have : False := by simpa [Genv.symbol_address, hfind, Mem.loadv] using load
          exact this.elim
      | some b =>
          have hmap : F b = some (b, .Z0) := hdom b (hsymbols id b hfind)
          have hfind' : Genv.find_symbol (Genv.globalenv tprog) id = some b := by
            rw [symbols_preserved cfg prog tprog hm id]
            exact hfind
          have haddr : Val.inject F
              (Genv.symbol_address (Genv.globalenv prog) id ofs)
              (Genv.symbol_address (Genv.globalenv tprog) id ofs) := by
            simp [Genv.symbol_address, hfind, hfind']
            exact Val.inject_ptr F b ofs b ofs .Z0 hmap
              (pg_ptr_add_zero_repr ofs).symm
          obtain ⟨v', hload', hinj'⟩ := pg_loadv_inject F m m' chunk
            (Genv.symbol_address (Genv.globalenv prog) id ofs)
            (Genv.symbol_address (Genv.globalenv tprog) id ofs) v hmem load haddr
          refine ⟨v', ?_, hinj'⟩
          apply eval_BA_loadglobal
          exact hload'
  | eval_BA_addrglobal id ofs =>
      refine ⟨Senv.symbol_address (Genv.to_senv (Genv.globalenv tprog)) id ofs,
        (by simpa [sbuiltinarg] using
          (eval_BA_addrglobal (ge := Genv.to_senv (Genv.globalenv tprog))
            (e := fun r => Regmap.get r rs') (sp := Vptr sp' Ptrofs.zero) (m := m') id ofs)), ?_⟩
      change Val.inject F
        (Genv.symbol_address (Genv.globalenv prog) id ofs)
        (Genv.symbol_address (Genv.globalenv tprog) id ofs)
      cases hfind : Genv.find_symbol (Genv.globalenv prog) id with
      | none => simp [Genv.symbol_address, hfind]; exact Val.val_inject_undef F _
      | some b =>
          have hmap : F b = some (b, .Z0) := hdom b (hsymbols id b hfind)
          have hfind' : Genv.find_symbol (Genv.globalenv tprog) id = some b := by
            rw [symbols_preserved cfg prog tprog hm id]
            exact hfind
          simp [Genv.symbol_address, hfind, hfind']
          exact Val.inject_ptr F b ofs b ofs .Z0 hmap
            (pg_ptr_add_zero_repr ofs).symm
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      rcases ihhi with ⟨vhi', hhi', hinjhi⟩
      rcases ihlo with ⟨vlo', hlo', hinjlo⟩
      refine ⟨Val.longofwords vhi' vlo', ?_, ?_⟩
      · simpa [sbuiltinarg] using
          (eval_BA_splitlong (ge := Genv.to_senv (Genv.globalenv tprog))
            (e := fun r => Regmap.get r rs')
            (sp := Vptr sp' Ptrofs.zero) (m := m')
            (sbuiltinarg ctx hi) (sbuiltinarg ctx lo) vhi' vlo' hhi' hlo')
      · exact Val.longofwords_inject F vhi vlo vhi' vlo' hinjhi hinjlo
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      rcases ih1 with ⟨v1', h1', hinj1⟩
      rcases ih2 with ⟨v2', h2', hinj2⟩
      refine ⟨if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1' v2' else Val.add v1' v2', ?_, ?_⟩
      · simpa [sbuiltinarg] using
          (eval_BA_addptr (ge := Genv.to_senv (Genv.globalenv tprog))
            (e := fun r => Regmap.get r rs')
            (sp := Vptr sp' Ptrofs.zero) (m := m')
            (sbuiltinarg ctx a1) (sbuiltinarg ctx a2) v1' v2' h1' h2')
      · cases hp : CompCert4Lean.X86_64.Archi.ptr64
        · simp [hp]
          exact Val.add_inject F v1 v1' v2 v2' hinj1 hinj2
        · simp [hp]
          exact Val.addl_inject F v1 v1' v2 v2' hinj1 hinj2
end CompCert4Lean.Backend.Inliningproof
