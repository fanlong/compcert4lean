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
  ∀ ofs, zLe lo ofs → zLt ofs hi → loc_private F m m' sp ofs

inductive match_globalenvs (prog : program) (F : Val.meminj) (bound : block) : Prop where
  | mk
      (DOMAIN : ∀ b, Plt b bound → F b = some (b, zZero))
      (IMAGE : ∀ b1 b2 delta, F b1 = some (b2, delta) → Plt b2 bound → b1 = b2)
      (SYMBOLS : ∀ id b, Genv.find_symbol (Genv.globalenv prog) id = some b → Plt b bound)
      (FUNCTIONS : ∀ b fd, Genv.find_funct_ptr (Genv.globalenv prog) b = some fd → Plt b bound)
      (VARINFOS : ∀ b gv, Genv.find_var_info (Genv.globalenv prog) b = some gv → Plt b bound) :
      match_globalenvs prog F bound

mutual
inductive match_stacks (cfg : InliningConfig) (prog : program) (F : Val.meminj) (m m' : mem) :
    List stackframe → List stackframe → block → Prop where
  | match_stacks_nil : ∀ bound1 bound,
      match_globalenvs prog F bound1 → Ple bound1 bound →
      match_stacks cfg prog F m m' [] [] bound
  | match_stacks_cons : ∀ res f sp pc rs stk f' sp' rs' stk' bound fenv ctx,
      match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
      agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      range_private F m m' sp' (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty → zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      Ple res ctx.mreg → Plt sp' bound →
      match_stacks cfg prog F m m'
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk') bound
  | match_stacks_untailcall : ∀ stk res f' sp' rpc rs' stk' bound ctx,
      match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs' →
      range_private F m m' sp' ctx.dstk f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty → zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      ctx.retinfo = some (rpc, res) → Plt sp' bound →
      match_stacks cfg prog F m m' stk
        (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk') bound

inductive match_stacks_inside (cfg : InliningConfig) (prog : program) (F : Val.meminj) (m m' : mem) :
    List stackframe → List stackframe → function → context → block → regset → Prop where
  | match_stacks_inside_base : ∀ stk stk' f' ctx sp' rs',
      match_stacks cfg prog F m m' stk stk' sp' → ctx.retinfo = none → ctx.dstk = zZero →
      match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined : ∀ res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx',
      match_stacks_inside cfg prog F m m' stk stk' f' ctx' sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx' f f'.fn_code →
      agree_regs F ctx' rs rs' → F sp = some (sp', ctx'.dstk) →
      range_private F m m' sp' (zAdd ctx'.dstk ctx'.mstk) ctx.dstk →
      Ple res ctx'.mreg → ctx.retinfo = some (spc ctx' pc, sreg ctx' res) →
      context_below ctx' ctx → context_stack_call ctx' ctx →
      match_stacks_inside cfg prog F m m'
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk) stk' f' ctx sp' rs'
end

export match_stacks (match_stacks_nil match_stacks_cons match_stacks_untailcall)
export match_stacks_inside (match_stacks_inside_base match_stacks_inside_inlined)

def match_stacks_indStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog : program) (F : Val.meminj) (m m' : mem)
    (P : List stackframe → List stackframe → block → Prop),
    (∀ bound1 bound,
      match_globalenvs prog F bound1 → Ple bound1 bound → P [] [] bound) →
    (∀ res f sp pc rs stk f' sp' rs' stk' bound fenv ctx,
      match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs' →
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
      match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs' →
      range_private F m m' sp' ctx.dstk f'.fn_stacksize →
      (zLe zZero f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty →
        zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      ctx.retinfo = some (rpc, res) → Plt sp' bound →
      P stk (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk') bound) →
    ∀ l l0 b, match_stacks cfg prog F m m' l l0 b → P l l0 b

def match_stacks_inside_indStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog : program) (F : Val.meminj) (m m' : mem)
    (P : List stackframe → List stackframe → function → context → block → regset → Prop),
    (∀ stk stk' f' ctx sp' rs',
      match_stacks cfg prog F m m' stk stk' sp' →
      ctx.retinfo = none → ctx.dstk = zZero →
      P stk stk' f' ctx sp' rs') →
    (∀ res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx',
      match_stacks_inside cfg prog F m m' stk stk' f' ctx' sp' rs' →
      P stk stk' f' ctx' sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx' f f'.fn_code →
      agree_regs F ctx' rs rs' → F sp = some (sp', ctx'.dstk) →
      range_private F m m' sp' (zAdd ctx'.dstk ctx'.mstk) ctx.dstk →
      Ple res ctx'.mreg → ctx.retinfo = some (spc ctx' pc, sreg ctx' res) →
      context_below ctx' ctx → context_stack_call ctx' ctx →
      P (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk) stk' f' ctx sp' rs') →
    ∀ l l0 f c b r,
      match_stacks_inside cfg prog F m m' l l0 f c b r → P l l0 f c b r

inductive match_states (cfg : InliningConfig) (prog : program) : RTL.state → RTL.state → Prop where
  | match_regular_states : ∀ stk f sp pc rs m stk' f' sp' rs' m' F fenv ctx,
      match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs' →
      fenv_compat prog fenv →
      tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
      agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
      Mem.inject F m m' → Mem.valid_block m' sp' →
      range_private F m m' sp' (zAdd ctx.dstk ctx.mstk) f'.fn_stacksize →
      zLe zZero f'.fn_stacksize → zLt f'.fn_stacksize Ptrofs.max_unsigned →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty → zLe zZero ofs ∧ zLe ofs f'.fn_stacksize) →
      match_states cfg prog (State stk f (Vptr sp Ptrofs.zero) pc rs m)
        (State stk' f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m')

export match_states (match_regular_states)

def measure : RTL.state → Nat
  | State _ _ _ _ _ _ => 1
  | Callstate _ _ _ _ => 0
  | Returnstate _ _ _ => 0

/-! Later-proof statement descriptors. -/

def Plt_Ple_decStatement : Type :=
  ∀ p q : positive, Support.Sumbool (Plt p q) (Ple q p)

def agree_regs_incrStatement : Prop :=
  ∀ F ctx rs1 rs2 F', agree_regs F ctx rs1 rs2 → Val.inject_incr F F' → agree_regs F' ctx rs1 rs2

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
  ∀ (cfg : InliningConfig) (prog : program) (fenv : funenv) (id : ident)
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
  ∀ cfg prog F m m' stk stk' bound bound1,
    match_stacks cfg prog F m m' stk stk' bound → Ple bound bound1 →
      match_stacks cfg prog F m m' stk stk' bound1

def match_stacks_emptyStatement : Prop :=
  ∀ cfg prog F m m' stk stk' bound,
    match_stacks cfg prog F m m' stk stk' bound → stk = [] → stk' = []

def match_stacks_extcallStatement : Prop :=
  ∀ cfg prog F1 F2 m1 m2 m1' m2' stk stk' bound,
    (∀ b ofs p, Mem.valid_block m1 b → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    (∀ b ofs p, Mem.valid_block m1' b → Mem.perm m2' b ofs .Max p →
      Mem.perm m1' b ofs .Max p) →
    Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2' →
    Mem.inject F1 m1 m1' →
    match_stacks cfg prog F1 m1 m1' stk stk' bound →
    Ple bound m1'.nextblock → Val.inject_incr F1 F2 →
    inject_separated F1 F2 m1 m1' →
    match_stacks cfg prog F2 m2 m2' stk stk' bound

def match_stacks_globalenvsStatement : Prop :=
  ∀ cfg prog F m m' stk stk' bound,
    match_stacks cfg prog F m m' stk stk' bound → ∃ b, match_globalenvs prog F b
def match_stacks_inside_alloc_leftStatement : Prop :=
  ∀ cfg prog F m m' stk stk' f' ctx sp' rs' sz m1 b F1 delta,
    match_stacks_inside cfg prog F m m' stk stk' f' ctx sp' rs' →
    Mem.alloc m zZero sz = (m1, b) → Val.inject_incr F F1 →
    F1 b = some (sp', delta) →
    (∀ b1, b1 ≠ b → F1 b1 = F b1) →
    zLe ctx.dstk delta →
    match_stacks_inside cfg prog F1 m1 m' stk stk' f' ctx sp' rs'

def match_stacks_inside_emptyStatement : Prop :=
  ∀ cfg prog F m m' stk stk' f ctx sp rs,
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp rs →
    stk = [] → stk' = [] ∧ ctx.retinfo = none

def match_stacks_inside_extcallStatement : Prop :=
  ∀ cfg prog F1 F2 m1 m2 m1' m2' stk stk' f' ctx sp' rs',
    (∀ b ofs p, Mem.valid_block m1 b → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    (∀ b ofs p, Mem.valid_block m1' b → Mem.perm m2' b ofs .Max p →
      Mem.perm m1' b ofs .Max p) →
    Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2' →
    Mem.inject F1 m1 m1' →
    match_stacks_inside cfg prog F1 m1 m1' stk stk' f' ctx sp' rs' →
    Plt sp' m1'.nextblock → Val.inject_incr F1 F2 →
    inject_separated F1 F2 m1 m1' →
    match_stacks_inside cfg prog F2 m2 m2' stk stk' f' ctx sp' rs'

def match_stacks_inside_globalenvsStatement : Prop :=
  ∀ cfg prog F m m' stk stk' f ctx sp rs,
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp rs →
    ∃ b, match_globalenvs prog F b

def match_stacks_inside_globalsStatement : Prop :=
  ∀ cfg prog F m m' stk stk' f ctx sp rs,
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp rs →
    CompCert4Lean.Common.Events.meminj_preserves_globals fundef Unit
      (Genv.globalenv prog) F

def match_stacks_inside_inlined_tailcallStatement : Prop :=
  ∀ cfg prog fenv F m m' stk stk' f' ctx sp rs ctx' f,
    match_stacks_inside cfg prog F m m' stk stk' f' ctx sp rs →
    context_below ctx ctx' → context_stack_tailcall ctx f ctx' →
    ctx'.retinfo = ctx.retinfo →
    range_private F m m' sp ctx.dstk f'.fn_stacksize →
    tr_funbody fenv f'.fn_stacksize ctx' f f'.fn_code →
    match_stacks_inside cfg prog F m m' stk stk' f' ctx' sp rs

def match_stacks_inside_invariantStatement : Prop :=
  ∀ cfg prog F F1 m m' m1 m1' stk stk' f' ctx sp rs rs2,
    match_stacks_inside cfg prog F m m' stk stk' f' ctx sp rs →
    (∀ r, Plt r ctx.dreg → Regmap.get r rs2 = Regmap.get r rs) →
    (∀ b1 b2 delta, F1 b1 = some (b2, delta) → Ple b2 sp → F b1 = some (b2, delta)) →
    (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → Ple b2 sp →
      Mem.perm m1 b1 ofs .Max .Nonempty → Mem.perm m b1 ofs .Max .Nonempty) →
    (∀ b ofs, Ple b sp → Mem.perm m' b ofs .Cur .Freeable →
      Mem.perm m1' b ofs .Cur .Freeable) →
    (∀ b ofs k p, Ple b sp → Mem.perm m1' b ofs k p →
      Mem.perm m' b ofs k p) →
    match_stacks_inside cfg prog F1 m1 m1' stk stk' f' ctx sp rs2

def match_stacks_inside_set_regStatement : Prop :=
  ∀ cfg prog F m m' stk stk' f ctx sp rs r v,
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp rs →
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp (Regmap.set (sreg ctx r) v rs)

def match_stacks_inside_set_resStatement : Prop :=
  ∀ cfg prog F m m' stk stk' f ctx sp rs res v,
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp rs →
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp
      (regmap_setres (sbuiltinres ctx res) v rs)

def match_stacks_inside_storeStatement : Prop :=
  ∀ cfg prog F m m' m1 m1' stk stk' f ctx sp rs chunk b ofs v chunk' b' ofs' v',
    match_stacks_inside cfg prog F m m' stk stk' f ctx sp rs →
    Mem.store chunk m b ofs v = some m1 → Mem.store chunk' m' b' ofs' v' = some m1' →
    match_stacks_inside cfg prog F m1 m1' stk stk' f ctx sp rs

def match_stacks_invariantStatement : Prop :=
  ∀ cfg prog F F1 m m' m1 m1' stk stk' bound,
    match_stacks cfg prog F m m' stk stk' bound →
    Val.inject_incr F F1 →
    (∀ b1 b2 delta, F1 b1 = some (b2, delta) → Plt b2 bound →
      F b1 = some (b2, delta)) →
    (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → Plt b2 bound →
      Mem.perm m1 b1 ofs .Max .Nonempty → Mem.perm m b1 ofs .Max .Nonempty) →
    (∀ b ofs, Plt b bound → Mem.perm m' b ofs .Cur .Freeable →
      Mem.perm m1' b ofs .Cur .Freeable) →
    (∀ b ofs k p, Plt b bound → Mem.perm m1' b ofs k p →
      Mem.perm m' b ofs k p) →
    match_stacks cfg prog F1 m1 m1' stk stk' bound

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
    Mem.inject F m1 m1' → Val.inject_incr F F' →
    inject_separated F F' m1 m1' → Mem.valid_block m1' sp →
    range_private F' m2 m2' sp base hi

def range_private_free_leftStatement : Prop :=
  ∀ F m m' sp base sz hi b m1,
    range_private F m m' sp (zAdd base (ZArith.BinInt.Z.max sz zZero)) hi →
    Mem.free m b zZero sz = some m1 → F b = some (sp, base) → Mem.inject F m m' →
    range_private F m1 m' sp base hi

def range_private_invariantStatement : Prop :=
  ∀ F m m' sp lo hi F1 m1 m1', range_private F m m' sp lo hi →
    (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) →
      Mem.perm m1 b1 ofs .Max .Nonempty →
      zLe lo (zAdd ofs delta) → zLt (zAdd ofs delta) hi →
      F b1 = some (b2, delta) ∧ Mem.perm m b1 ofs .Max .Nonempty) →
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

def step_simulationStatement : Prop :=
  ∀ (xi : ExternalCalls) (cfg : InliningConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ (S1 : RTL.state) (t : trace) (S2 : RTL.state),
      step xi (Genv.globalenv prog) S1 t S2 →
      ∀ S1', match_states cfg prog S1 S1' →
        (∃ S2', plus (step xi) (Genv.globalenv tprog) S1' t S2' ∧
          match_states cfg prog S2 S2') ∨
        (measure S2 < measure S1 ∧ t = E0 ∧ match_states cfg prog S2 S1')

def symbols_preservedStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ s, Genv.find_symbol (Genv.globalenv tprog) s = Genv.find_symbol (Genv.globalenv prog) s

def tr_builtin_argStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog : program) F bound ctx rs rs' sp sp' m m' a v,
    match_globalenvs prog F bound → agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
    Mem.inject F m m' →
    eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
      (Vptr sp Ptrofs.zero) m a v →
    ∃ v', eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs')
      (Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v' ∧ Val.inject F v v'

def tr_builtin_argsStatement : Prop :=
  ∀ (cfg : InliningConfig) (prog : program) F bound ctx rs rs' sp sp' m m' al vl,
    match_globalenvs prog F bound → agree_regs F ctx rs rs' → F sp = some (sp', ctx.dstk) →
    Mem.inject F m m' →
    eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
      (Vptr sp Ptrofs.zero) m al vl →
    ∃ vl', eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs')
      (Vptr sp' Ptrofs.zero) m' (al.map (sbuiltinarg ctx)) vl' ∧ Val.inject_list F vl vl'

def tr_funbody_invStatement : Prop :=
  ∀ fenv sz ctx (f : function) c pc i, tr_funbody fenv sz ctx f c →
    PTree.get pc f.fn_code = some i →
    tr_instr fenv sz ctx pc i c

def tr_moves_init_regsStatement : Prop :=
  ∀ (xi : ExternalCalls) (tprog : program) F (stk : List stackframe) (f : function) (sp : val) (m : mem)
    ctx1 ctx2 rdsts rsrcs vl pc1 pc2 rs1,
    context_below ctx1 ctx2 →
    tr_moves f.fn_code pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 →
    (∀ r, r ∈ rdsts → Ple r ctx2.mreg) →
    list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs →
    ∃ rs2,
      star (step xi) (Genv.globalenv tprog) (State stk f sp pc1 rs1 m) E0
        (State stk f sp pc2 rs2 m) ∧
      agree_regs F ctx2 (init_regs vl rdsts) rs2 ∧
      (∀ r, Plt r ctx2.dreg → Regmap.get r rs2 = Regmap.get r rs1)

def transf_final_statesStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ st1 st2 r, match_states cfg prog st1 st2 → final_state st1 r → final_state st2 r

def transf_initial_statesStatement : Prop :=
  ∀ cfg prog tprog, match_prog cfg prog tprog →
    ∀ st1, initial_state prog st1 → ∃ st2, initial_state tprog st2 ∧ match_states cfg prog st1 st2

def transf_program_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (cfg : InliningConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    forward_simulation (RTL.semantics xi prog) (RTL.semantics xi tprog)

def transf_program_matchStatement : Prop :=
  ∀ cfg prog tprog, transf_program cfg prog = OK tprog → match_prog cfg prog tprog

end CompCert4Lean.Backend.Inliningproof
