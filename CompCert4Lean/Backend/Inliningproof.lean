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
