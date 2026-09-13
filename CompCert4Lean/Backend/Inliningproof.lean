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
