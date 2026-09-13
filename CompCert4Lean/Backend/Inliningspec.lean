import CompCert4Lean.Backend.Inlining
import CompCert4Lean.Common.Linking
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Recursion

/-!
# Relational specification of RTL function inlining

Definition-bearing translation of CompCert's `backend/Inliningspec.v`.
Proofs assigned to the later proof-migration phase are represented by exact
transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zGe := ZArith.BinInt.Z.ge
private abbrev zGt := ZArith.BinInt.Z.gt
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zSub := ZArith.BinInt.Z.sub

private abbrev rtlLinker : Linker program :=
  @Linker_prog fundef Unit (@Linker_fundef function) Linker_unit

private abbrev rtlLinkorder (p q : program) : Prop :=
  @linkorder program rtlLinker p q

def fenv_compat (p : program) (fenv : funenv) : Prop :=
  ∀ id f, PTree.get id fenv = some f →
    PTree.get id (prog_defmap p) = some (.Gfun (.Internal f))

def mlist_iter2 {A B : Type} (f : A → B → mon Unit)
    (l : List (A × B)) : mon Unit :=
  match l with
  | [] => ret ()
  | (x, y) :: l' => bind (f x y) (fun _ => mlist_iter2 f l')

inductive tr_moves (c : code) : node → List reg → List reg → node → Prop where
  | tr_moves_cons : ∀ pc1 src srcs dst dsts pc2 pc3,
      tr_moves c pc1 srcs dsts pc2 →
      PTree.get pc2 c = some (Iop .Omove [src] dst pc3) →
      tr_moves c pc1 (src :: srcs) (dst :: dsts) pc3
  | tr_moves_nil : ∀ srcs dsts pc,
      srcs = [] ∨ dsts = [] →
      tr_moves c pc srcs dsts pc

def context_below (ctx1 ctx2 : context) : Prop :=
  Ple (PArith.BinPos.Pos.add ctx1.dreg ctx1.mreg) ctx2.dreg

def context_stack_call (ctx1 ctx2 : context) : Prop :=
  zGe ctx1.mstk Z0 ∧ zLe (zAdd ctx1.dstk ctx1.mstk) ctx2.dstk

def context_stack_tailcall (ctx1 : context) (f : function) (ctx2 : context) : Prop :=
  ctx2.dstk = align ctx1.dstk (min_alignment f.fn_stacksize)

mutual
  inductive tr_instr (fenv : funenv) (stacksize : Z) :
      context → node → instruction → code → Prop where
    | tr_nop : ∀ ctx pc c s,
        PTree.get (spc ctx pc) c = some (Inop (spc ctx s)) →
        tr_instr fenv stacksize ctx pc (Inop s) c
    | tr_op : ∀ ctx pc c op args res s,
        Ple res ctx.mreg →
        PTree.get (spc ctx pc) c =
          some (Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s)) →
        tr_instr fenv stacksize ctx pc (Iop op args res s) c
    | tr_load : ∀ ctx pc c chunk addr args res s,
        Ple res ctx.mreg →
        PTree.get (spc ctx pc) c =
          some (Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx res) (spc ctx s)) →
        tr_instr fenv stacksize ctx pc (Iload chunk addr args res s) c
    | tr_store : ∀ ctx pc c chunk addr args src s,
        PTree.get (spc ctx pc) c =
          some (Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s)) →
        tr_instr fenv stacksize ctx pc (Istore chunk addr args src s) c
    | tr_call : ∀ ctx pc c sg ros args res s,
        Ple res ctx.mreg →
        PTree.get (spc ctx pc) c =
          some (Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s)) →
        tr_instr fenv stacksize ctx pc (Icall sg ros args res s) c
    | tr_call_inlined : ∀ ctx pc sg id args res s c f pc1 ctx',
        Ple res ctx.mreg →
        PTree.get id fenv = some f →
        PTree.get (spc ctx pc) c = some (Inop pc1) →
        tr_moves c pc1 (sregs ctx args) (sregs ctx' f.fn_params)
          (spc ctx' f.fn_entrypoint) →
        tr_funbody fenv stacksize ctx' f c →
        ctx'.retinfo = some (spc ctx s, sreg ctx res) →
        context_below ctx ctx' →
        context_stack_call ctx ctx' →
        tr_instr fenv stacksize ctx pc (Icall sg (.inr id) args res s) c
    | tr_tailcall : ∀ ctx pc c sg ros args,
        PTree.get (spc ctx pc) c = some (Itailcall sg (sros ctx ros) (sregs ctx args)) →
        ctx.retinfo = none →
        tr_instr fenv stacksize ctx pc (Itailcall sg ros args) c
    | tr_tailcall_call : ∀ ctx pc c sg ros args res s,
        PTree.get (spc ctx pc) c =
          some (Icall sg (sros ctx ros) (sregs ctx args) res s) →
        ctx.retinfo = some (s, res) →
        tr_instr fenv stacksize ctx pc (Itailcall sg ros args) c
    | tr_tailcall_inlined : ∀ ctx pc sg id args c f pc1 ctx',
        PTree.get id fenv = some f →
        PTree.get (spc ctx pc) c = some (Inop pc1) →
        tr_moves c pc1 (sregs ctx args) (sregs ctx' f.fn_params)
          (spc ctx' f.fn_entrypoint) →
        tr_funbody fenv stacksize ctx' f c →
        ctx'.retinfo = ctx.retinfo →
        context_below ctx ctx' →
        context_stack_tailcall ctx f ctx' →
        tr_instr fenv stacksize ctx pc (Itailcall sg (.inr id) args) c
    | tr_builtin : ∀ ctx pc c ef args res s,
        (match res with
         | BR r => Ple r ctx.mreg
         | _ => True) →
        PTree.get (spc ctx pc) c =
          some (Ibuiltin ef (args.map (sbuiltinarg ctx)) (sbuiltinres ctx res) (spc ctx s)) →
        tr_instr fenv stacksize ctx pc (Ibuiltin ef args res s) c
    | tr_cond : ∀ ctx pc cond args s1 s2 c,
        PTree.get (spc ctx pc) c =
          some (Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2)) →
        tr_instr fenv stacksize ctx pc (Icond cond args s1 s2) c
    | tr_jumptable : ∀ ctx pc r tbl c,
        PTree.get (spc ctx pc) c =
          some (Ijumptable (sreg ctx r) (tbl.map (spc ctx))) →
        tr_instr fenv stacksize ctx pc (Ijumptable r tbl) c
    | tr_return : ∀ ctx pc or c,
        PTree.get (spc ctx pc) c = some (Ireturn (option_map (sreg ctx) or)) →
        ctx.retinfo = none →
        tr_instr fenv stacksize ctx pc (Ireturn or) c
    | tr_return_inlined : ∀ ctx pc or c rinfo,
        PTree.get (spc ctx pc) c = some (inline_return ctx or rinfo) →
        ctx.retinfo = some rinfo →
        tr_instr fenv stacksize ctx pc (Ireturn or) c

  inductive tr_funbody (fenv : funenv) (stacksize : Z) :
      context → function → code → Prop where
    | tr_funbody_intro : ∀ ctx f c,
        (∀ r, r ∈ f.fn_params → Ple r ctx.mreg) →
        (∀ pc i, PTree.get pc f.fn_code = some i →
          tr_instr fenv stacksize ctx pc i c) →
        ctx.mstk = ZArith.BinInt.Z.max f.fn_stacksize Z0 →
        ZArith.BinInt.Z.divide (min_alignment f.fn_stacksize) ctx.dstk →
        zGe ctx.dstk Z0 →
        zLe (zAdd ctx.dstk ctx.mstk) stacksize →
        tr_funbody fenv stacksize ctx f c
end

def fenv_agree (fenv : funenv) (fe : funenv) : Prop :=
  ∀ id f, PTree.get id fe = some f → PTree.get id fenv = some f

inductive tr_function : program → function → function → Prop where
  | tr_function_intro : ∀ (p : program) (fenv : funenv) (f f' : function) (ctx : context),
    fenv_compat p fenv →
    tr_funbody fenv f'.fn_stacksize ctx f f'.fn_code →
    ctx.dstk = Z0 →
    ctx.retinfo = none →
    f'.fn_sig = f.fn_sig →
    f'.fn_params = sregs ctx f.fn_params →
    f'.fn_entrypoint = spc ctx f.fn_entrypoint →
    (zLe Z0 f'.fn_stacksize ∧ zLt f'.fn_stacksize Ptrofs.max_unsigned) →
    tr_function p f f'

export tr_instr (tr_builtin tr_call tr_call_inlined tr_cond tr_jumptable tr_load
  tr_nop tr_op tr_return tr_return_inlined tr_store tr_tailcall tr_tailcall_call
  tr_tailcall_inlined)
export tr_funbody (tr_funbody_intro)
export tr_function (tr_function_intro)
export tr_moves (tr_moves_cons tr_moves_nil)

abbrev tr_builtin (fenv : funenv) (stacksize : Z) := @tr_instr.tr_builtin fenv stacksize
abbrev tr_call (fenv : funenv) (stacksize : Z) := @tr_instr.tr_call fenv stacksize
abbrev tr_call_inlined (fenv : funenv) (stacksize : Z) :=
  @tr_instr.tr_call_inlined fenv stacksize
abbrev tr_cond (fenv : funenv) (stacksize : Z) := @tr_instr.tr_cond fenv stacksize
abbrev tr_funbody_intro (fenv : funenv) (stacksize : Z) :=
  @tr_funbody.tr_funbody_intro fenv stacksize
abbrev tr_function_intro := @tr_function.tr_function_intro
abbrev tr_jumptable (fenv : funenv) (stacksize : Z) :=
  @tr_instr.tr_jumptable fenv stacksize
abbrev tr_load (fenv : funenv) (stacksize : Z) := @tr_instr.tr_load fenv stacksize
abbrev tr_moves_cons (c : code) := @tr_moves.tr_moves_cons c
abbrev tr_moves_nil (c : code) := @tr_moves.tr_moves_nil c
abbrev tr_nop (fenv : funenv) (stacksize : Z) := @tr_instr.tr_nop fenv stacksize
abbrev tr_op (fenv : funenv) (stacksize : Z) := @tr_instr.tr_op fenv stacksize
abbrev tr_return (fenv : funenv) (stacksize : Z) := @tr_instr.tr_return fenv stacksize
abbrev tr_return_inlined (fenv : funenv) (stacksize : Z) :=
  @tr_instr.tr_return_inlined fenv stacksize
abbrev tr_store (fenv : funenv) (stacksize : Z) := @tr_instr.tr_store fenv stacksize
abbrev tr_tailcall (fenv : funenv) (stacksize : Z) :=
  @tr_instr.tr_tailcall fenv stacksize
abbrev tr_tailcall_call (fenv : funenv) (stacksize : Z) :=
  @tr_instr.tr_tailcall_call fenv stacksize
abbrev tr_tailcall_inlined (fenv : funenv) (stacksize : Z) :=
  @tr_instr.tr_tailcall_inlined fenv stacksize

/-! Exact statement descriptors for later proof migration. -/

def funenv_program_compatStatement : Prop :=
  ∀ cfg p, fenv_compat p (funenv_program cfg p)

def fenv_compat_linkorderStatement : Prop :=
  ∀ cunit prog fenv, rtlLinkorder cunit prog →
    fenv_compat cunit fenv → fenv_compat prog fenv

def shiftpos_eqStatement : Prop :=
  ∀ x y : positive,
    Zpos (shiftpos x y) =
      zSub (zAdd (Zpos x) (Zpos y)) (Zpos xH)

def shiftpos_injStatement : Prop :=
  ∀ x y n : positive, shiftpos x n = shiftpos y n → x = y

def shiftpos_diffStatement : Prop :=
  ∀ x y n : positive, x ≠ y → shiftpos x n ≠ shiftpos y n

def shiftpos_aboveStatement : Prop :=
  ∀ x n : positive, Ple n (shiftpos x n)

def shiftpos_not_belowStatement : Prop :=
  ∀ x n : positive, Plt (shiftpos x n) n → False

def shiftpos_belowStatement : Prop :=
  ∀ x n : positive, Plt (shiftpos x n) (PArith.BinPos.Pos.add x n)

def mlist_iter2_foldStatement : Prop :=
  ∀ (A B : Type) (f : A → B → mon Unit) (l : List (A × B)) (s : Inlining.state),
    ∃ i : Inlining.sincr s
        (l.foldl (fun a p => match f p.1 p.2 a with | R _ s2 _ => s2) s),
      mlist_iter2 f l s =
        R () (l.foldl (fun a p => match f p.1 p.2 a with | R _ s2 _ => s2) s) i

def ptree_mfold_specStatement : Prop :=
  ∀ (A : Type) (f : positive → A → mon Unit) (t : PTree.t A)
    (s : Inlining.state) (x : Unit) (s' : Inlining.state)
    (i : Inlining.sincr s s'),
    ptree_mfold f t s = R x s' i →
    ∃ i' : Inlining.sincr s s',
      mlist_iter2 f (PTree.elements t) s = R () s' i'

def add_moves_unchangedStatement : Prop :=
  ∀ srcs dsts pc2 s pc1 s' i pc,
    add_moves srcs dsts pc2 s = R pc1 s' i →
    (Plt pc s.st_nextnode ∨ Ple s'.st_nextnode pc) →
    PTree.get pc s'.st_code = PTree.get pc s.st_code

def add_moves_specStatement : Prop :=
  ∀ srcs dsts pc2 s pc1 s' i c,
    add_moves srcs dsts pc2 s = R pc1 s' i →
    (∀ pc, Ple s.st_nextnode pc → Plt pc s'.st_nextnode →
      PTree.get pc c = PTree.get pc s'.st_code) →
    tr_moves c pc1 srcs dsts pc2

def set_instr_otherStatement : Prop :=
  ∀ pc instr s x s' i pc',
    set_instr pc instr s = R x s' i → pc' ≠ pc →
    PTree.get pc' s'.st_code = PTree.get pc' s.st_code

def set_instr_sameStatement : Prop :=
  ∀ pc instr s x s' i c,
    set_instr pc instr s = R x s' i →
    PTree.get pc c = PTree.get pc s'.st_code →
    PTree.get pc c = some instr

def expand_instr_unchangedStatement : Prop :=
  ∀ (fe : funenv)
    (rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit),
    (∀ fe' L ctx f s x s' i pc,
      rec fe' L ctx f s = R x s' i →
      Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
      PTree.get pc s'.st_code = PTree.get pc s.st_code) →
    ∀ ctx pc instr s x s' i pc',
      expand_instr fe rec ctx pc instr s = R x s' i →
      Ple ctx.dpc s.st_nextnode → Plt pc' s.st_nextnode → pc' ≠ spc ctx pc →
      PTree.get pc' s'.st_code = PTree.get pc' s.st_code

def iter_expand_instr_unchangedStatement : Prop :=
  ∀ (fe : funenv)
    (rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit),
    (∀ fe' L ctx f s x s' i pc,
      rec fe' L ctx f s = R x s' i →
      Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
      PTree.get pc s'.st_code = PTree.get pc s.st_code) →
    ∀ ctx pc l s x s' i,
      mlist_iter2 (expand_instr fe rec ctx) l s = R x s' i →
      Ple ctx.dpc s.st_nextnode → Plt pc s.st_nextnode →
      pc ∉ (List.map (spc ctx) (List.map Prod.fst l)) →
      list_norepet (List.map Prod.fst l) →
      PTree.get pc s'.st_code = PTree.get pc s.st_code

def expand_cfg_rec_unchangedStatement : Prop :=
  ∀ (fe : funenv)
    (rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit),
    (∀ fe' L ctx f s x s' i pc,
      rec fe' L ctx f s = R x s' i →
      Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
      PTree.get pc s'.st_code = PTree.get pc s.st_code) →
    ∀ ctx f s x s' i pc,
      expand_cfg_rec fe rec ctx f s = R x s' i →
      Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
      PTree.get pc s'.st_code = PTree.get pc s.st_code

def min_alignment_posStatement : Prop :=
  ∀ sz : Z, zGt (min_alignment sz) Z0

def expand_instr_specStatement : Prop :=
  ∀ (fenv : funenv) (stacksize : Z) (fe : funenv),
    fenv_agree fenv fe →
    ∀ rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit,
      (∀ fe' L ctx f s x s' i c,
        rec fe' L ctx f s = R x s' i →
        fenv_agree fenv fe' →
        Ple (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) s.st_nextnode →
        ctx.mreg = max_reg_function f →
        Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
        zGe ctx.mstk Z0 → ctx.mstk = ZArith.BinInt.Z.max f.fn_stacksize Z0 →
        ZArith.BinInt.Z.divide (min_alignment f.fn_stacksize) ctx.dstk →
        zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
        (∀ pc, Ple ctx.dpc pc → Plt pc s'.st_nextnode →
          PTree.get pc c = PTree.get pc s'.st_code) →
        tr_funbody fenv stacksize ctx f c) →
      ∀ ctx pc instr s x s' i c,
        expand_instr fe rec ctx pc instr s = R x s' i →
        (∀ r, instr_defs instr = some r → Ple r ctx.mreg) →
        Plt (spc ctx pc) s.st_nextnode →
        Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
        zGe ctx.mstk Z0 → zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
        (∀ pc', Ple s.st_nextnode pc' → Plt pc' s'.st_nextnode →
          PTree.get pc' c = PTree.get pc' s'.st_code) →
        PTree.get (spc ctx pc) c = PTree.get (spc ctx pc) s'.st_code →
        tr_instr fenv stacksize ctx pc instr c

def iter_expand_instr_specStatement : Prop :=
  ∀ (fenv : funenv) (stacksize : Z) (fe : funenv),
    fenv_agree fenv fe →
    ∀ rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit,
      (∀ fe' L ctx f s x s' i pc,
        rec fe' L ctx f s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
        PTree.get pc s'.st_code = PTree.get pc s.st_code) →
      (∀ fe' L ctx f s x s' i c,
        rec fe' L ctx f s = R x s' i → fenv_agree fenv fe' →
        Ple (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) s.st_nextnode →
        ctx.mreg = max_reg_function f →
        Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
        zGe ctx.mstk Z0 → ctx.mstk = ZArith.BinInt.Z.max f.fn_stacksize Z0 →
        ZArith.BinInt.Z.divide (min_alignment f.fn_stacksize) ctx.dstk →
        zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
        (∀ pc, Ple ctx.dpc pc → Plt pc s'.st_nextnode →
          PTree.get pc c = PTree.get pc s'.st_code) →
        tr_funbody fenv stacksize ctx f c) →
      ∀ ctx l s x s' i c,
        mlist_iter2 (expand_instr fe rec ctx) l s = R x s' i →
        list_norepet (List.map Prod.fst l) →
        (∀ pc instr r, (pc, instr) ∈ l → instr_defs instr = some r → Ple r ctx.mreg) →
        (∀ pc instr, (pc, instr) ∈ l → Plt (spc ctx pc) s.st_nextnode) →
        Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
        zGe ctx.mstk Z0 → zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
        (∀ pc', Ple s.st_nextnode pc' → Plt pc' s'.st_nextnode →
          PTree.get pc' c = PTree.get pc' s'.st_code) →
        (∀ pc instr, (pc, instr) ∈ l →
          PTree.get (spc ctx pc) c = PTree.get (spc ctx pc) s'.st_code) →
        ∀ pc instr, (pc, instr) ∈ l → tr_instr fenv stacksize ctx pc instr c

def expand_cfg_rec_specStatement : Prop :=
  ∀ (fenv : funenv) (stacksize : Z) (fe : funenv),
    fenv_agree fenv fe →
    ∀ rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit,
      (∀ fe' L ctx f s x s' i pc,
        rec fe' L ctx f s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
        PTree.get pc s'.st_code = PTree.get pc s.st_code) →
      (∀ fe' L ctx f s x s' i c,
        rec fe' L ctx f s = R x s' i → fenv_agree fenv fe' →
        Ple (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) s.st_nextnode →
        ctx.mreg = max_reg_function f →
        Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
        zGe ctx.mstk Z0 → ctx.mstk = ZArith.BinInt.Z.max f.fn_stacksize Z0 →
        ZArith.BinInt.Z.divide (min_alignment f.fn_stacksize) ctx.dstk →
        zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
        (∀ pc, Ple ctx.dpc pc → Plt pc s'.st_nextnode →
          PTree.get pc c = PTree.get pc s'.st_code) →
        tr_funbody fenv stacksize ctx f c) →
      ∀ ctx f s x s' i c,
        expand_cfg_rec fe rec ctx f s = R x s' i →
        Ple (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) s.st_nextnode →
        ctx.mreg = max_reg_function f →
        Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
        zGe ctx.mstk Z0 → ctx.mstk = ZArith.BinInt.Z.max f.fn_stacksize Z0 →
        ZArith.BinInt.Z.divide (min_alignment f.fn_stacksize) ctx.dstk →
        zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
        (∀ pc', Ple ctx.dpc pc' → Plt pc' s'.st_nextnode →
          PTree.get pc' c = PTree.get pc' s'.st_code) →
        tr_funbody fenv stacksize ctx f c

def expand_cfg_unchangedStatement : Prop :=
  ∀ fe ctx f s x s' i pc,
    expand_cfg fe ctx f s = R x s' i →
    Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
    PTree.get pc s'.st_code = PTree.get pc s.st_code

def expand_cfg_specStatement : Prop :=
  ∀ fenv stacksize fe ctx f s x s' i c,
    expand_cfg fe ctx f s = R x s' i → fenv_agree fenv fe →
    Ple (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) s.st_nextnode →
    ctx.mreg = max_reg_function f →
    Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg) s.st_nextreg →
    zGe ctx.mstk Z0 → ctx.mstk = ZArith.BinInt.Z.max f.fn_stacksize Z0 →
    ZArith.BinInt.Z.divide (min_alignment f.fn_stacksize) ctx.dstk →
    zGe ctx.dstk Z0 → zLe s'.st_stksize stacksize →
    (∀ pc', Ple ctx.dpc pc' → Plt pc' s'.st_nextnode →
      PTree.get pc' c = PTree.get pc' s'.st_code) →
    tr_funbody fenv stacksize ctx f c

def tr_function_linkorderStatement : Prop :=
  ∀ cunit prog f f', rtlLinkorder cunit prog →
    tr_function cunit f f' → tr_function prog f f'

def transf_function_specStatement : Prop :=
  ∀ cfg cunit f f',
    CompCert4Lean.Backend.Inlining.transf_function (funenv_program cfg cunit) f =
      CompCert4Lean.Common.Errors.res.OK f' → tr_function cunit f f'

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining

private theorem shiftpos_pred_double_nat (p : positive) :
    posToNat (PArith.BinPos.Pos.pred_double p) = 2 * posToNat p - 1 := by
  induction p with
  | xH => simp [PArith.BinPos.Pos.pred_double, posToNat]
  | xI p ih =>
      simp [PArith.BinPos.Pos.pred_double, posToNat]
      omega
  | xO p ih =>
      simp [PArith.BinPos.Pos.pred_double, posToNat, ih]
      have hp := posToNat_positive p
      omega

private theorem shiftpos_pred_nat_sub_one (p : positive) (h : p ≠ xH) :
    posToNat (PArith.BinPos.Pos.pred p) = posToNat p - 1 := by
  cases p with
  | xH => contradiction
  | xI p =>
      simp [PArith.BinPos.Pos.pred, posToNat]
  | xO p =>
      simpa [PArith.BinPos.Pos.pred, posToNat] using shiftpos_pred_double_nat p

theorem shiftpos_eq : shiftpos_eqStatement := by
  intro x y
  let nx := posToNat x
  let ny := posToNat y
  have hx : 0 < nx := by dsimp [nx]; exact posToNat_positive x
  have hy : 0 < ny := by dsimp [ny]; exact posToNat_positive y
  have hxy : 0 < nx + ny := by omega
  have hp : posToNat (posOfNat (nx + ny)) = nx + ny := posToNat_posOfNat hxy
  have hne : posOfNat (nx + ny) ≠ xH := by
    intro h
    have : nx + ny = 1 := by
      have hp' : posToNat xH = 1 := rfl
      rw [h] at hp
      omega
    omega
  have hpred := shiftpos_pred_nat_sub_one (posOfNat (nx + ny)) hne
  unfold shiftpos
  change Zpos (PArith.BinPos.Pos.pred (PArith.BinPos.Pos.add x y)) = _
  have hleft : intOfZ (Zpos (PArith.BinPos.Pos.pred (PArith.BinPos.Pos.add x y))) =
      Int.ofNat (nx + ny - 1) := by
    change Int.ofNat (posToNat (PArith.BinPos.Pos.pred (PArith.BinPos.Pos.add x y))) = _
    rw [show PArith.BinPos.Pos.add x y = posOfNat (nx + ny) by rfl]
    rw [hpred, hp]
  have hright : intOfZ (ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (Zpos x) (Zpos y)) (Zpos xH)) =
      Int.ofNat (nx + ny - 1) := by
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    simp [intOfZ, nx, ny]
    have hxH : posToNat xH = 1 := rfl
    rw [hxH]
    omega
  change Zpos (PArith.BinPos.Pos.pred (PArith.BinPos.Pos.add x y)) =
    ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add (Zpos x) (Zpos y)) (Zpos xH)
  apply Eq.trans (zOfInt_intOfZ _).symm
  apply Eq.trans (congrArg zOfInt (hleft.trans hright.symm))
  exact zOfInt_intOfZ _

theorem shiftpos_inj : shiftpos_injStatement := by
  intro x y n h
  have hz : Zpos (shiftpos x n) = Zpos (shiftpos y n) := congrArg Zpos h
  rw [shiftpos_eq x n, shiftpos_eq y n] at hz
  have hi := congrArg intOfZ hz
  simp [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi
  have hn : Int.ofNat (posToNat x) = Int.ofNat (posToNat y) := by
    simpa [intOfZ] using hi
  exact posToNat_injective (Int.ofNat.inj hn)

end CompCert4Lean.Backend.Inliningspec


namespace CompCert4Lean.Backend.Inliningspec
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Maps
private def P
    (dm : PTree.tree (globdef (CompCert4Lean.Common.AST.fundef function) Unit)) (fenv : funenv) : Prop :=
  ∀ id f, PTree.get id fenv = some f →
    PTree.get id dm = some (Gfun (Internal f))

theorem funenv_program_compat : funenv_program_compatStatement := by
  intro cfg p
  let info := inlining_analysis cfg p
  have REMOVE : ∀ (dm : PTree.tree (globdef (CompCert4Lean.Common.AST.fundef function) Unit)) (fenv : funenv) id g,
      P dm fenv → P (PTree.set id g dm) (PTree.remove id fenv) := by
    intro dm fenv id g h
    intro id0 f hget
    change PTree.get id0 (PTree.remove id (fenv : PTree.t function)) = some f at hget
    have hr := @PTree.getRemove_equation function id0 id (fenv : PTree.tree function)
    rw [hr] at hget
    split at hget
    · contradiction
    · rename_i hne
      have hdm := h id0 f hget
      change PTree.get id0 (PTree.set id g dm) = some (Gfun (Internal f))
      have hs := @PTree.getSet_equation
        (globdef (CompCert4Lean.Common.AST.fundef function) Unit) id0 id g dm
      rw [hs]
      simp [hne, hdm]
  have ADD : ∀ (cfg : InliningConfig) (info : inlining_info)
      (dm : PTree.tree (globdef (CompCert4Lean.Common.AST.fundef function) Unit)) (fenv : funenv)
      (idg : ident × globdef (CompCert4Lean.Common.AST.fundef function) Unit),
      P dm fenv →
      P (PTree.set idg.1 idg.2 dm)
        (add_globdef cfg info fenv idg) := by
    intro cfg info dm fenv idg h
    rcases idg with ⟨id, gd⟩
    change positive at id
    cases gd with
    | Gvar v =>
        intro id0 f hget
        change PTree.get id0 (PTree.remove (show positive from id)
          (fenv : PTree.t function)) = some f at hget
        have hr := @PTree.getRemove_equation function id0 (show positive from id)
          (fenv : PTree.tree function)
        rw [hr] at hget
        split at hget
        · contradiction
        · rename_i hne
          have hdm := h id0 f hget
          change PTree.get id0 (PTree.set (show positive from id) (Gvar v) dm) =
            some (Gfun (Internal f))
          have hs := @PTree.getSet_equation
            (globdef (CompCert4Lean.Common.AST.fundef function) Unit) id0
              (show positive from id) (Gvar v) dm
          rw [hs]
          simp [hne, hdm]
    | Gfun fd =>
        cases fd with
        | External ef =>
            intro id0 f hget
            change PTree.get id0 (PTree.remove (show positive from id)
              (fenv : PTree.t function)) = some f at hget
            have hr := @PTree.getRemove_equation function id0 (show positive from id)
              (fenv : PTree.tree function)
            rw [hr] at hget
            split at hget
            · contradiction
            · rename_i hne
              have hdm := h id0 f hget
              change PTree.get id0
                (PTree.set (show positive from id) (Gfun (External ef)) dm) =
                some (Gfun (Internal f))
              have hs := @PTree.getSet_equation
                (globdef (CompCert4Lean.Common.AST.fundef function) Unit) id0
                (show positive from id) (Gfun (External ef)) dm
              rw [hs]
              simp [hne, hdm]
        | Internal f0 =>
            by_cases hi : should_inline cfg info id f0
            · intro id0 f hget
              have hget' : PTree.get id0 (PTree.set (show positive from id) f0
                (fenv : PTree.t function)) = some f := by
                simpa [add_globdef, hi] using hget
              have hsenv := @PTree.getSet_equation function id0
                (show positive from id) f0 (fenv : PTree.tree function)
              rw [hsenv] at hget'
              split at hget'
              · rename_i heq
                subst id0
                cases hget'
                change PTree.get id (PTree.set (show positive from id)
                  (Gfun (Internal f0)) dm) = some (Gfun (Internal f0))
                have hs := @PTree.getSet_equation
                  (globdef (CompCert4Lean.Common.AST.fundef function) Unit) id id
                  (Gfun (Internal f0)) dm
                rw [hs]
                simp
              · rename_i hne
                have hdm := h id0 f hget'
                change PTree.get id0
                  (PTree.set (show positive from id) (Gfun (Internal f0)) dm) =
                  some (Gfun (Internal f))
                have hs := @PTree.getSet_equation
                  (globdef (CompCert4Lean.Common.AST.fundef function) Unit) id0
                  (show positive from id) (Gfun (Internal f0)) dm
                rw [hs]
                simp [hne, hdm]
            · intro id0 f hget
              have hget' : PTree.get id0 (PTree.remove (show positive from id)
                (fenv : PTree.t function)) = some f := by
                simpa [add_globdef, hi] using hget
              have hr := @PTree.getRemove_equation function id0 (show positive from id)
                (fenv : PTree.tree function)
              rw [hr] at hget'
              split at hget'
              · contradiction
              · rename_i hne
                have hdm := h id0 f hget'
                change PTree.get id0
                  (PTree.set (show positive from id) (Gfun (Internal f0)) dm) =
                  some (Gfun (Internal f))
                have hs := @PTree.getSet_equation
                  (globdef (CompCert4Lean.Common.AST.fundef function) Unit) id0
                  (show positive from id) (Gfun (Internal f0)) dm
                rw [hs]
                simp [hne, hdm]
  have REC : ∀ (l : List (ident × globdef (CompCert4Lean.Common.AST.fundef function) Unit))
      (dm : PTree.tree (globdef (CompCert4Lean.Common.AST.fundef function) Unit)) (fenv : funenv),
      P dm fenv →
      P (l.foldl (fun m idg => PTree.set idg.1 idg.2 m) dm)
        (l.foldl (add_globdef cfg info) fenv) := by
    intro l
    induction l with
    | nil =>
        intro dm fenv h
        simpa only [List.foldl] using h
    | cons idg l ih =>
        intro dm fenv h
        apply ih
        exact ADD cfg info dm fenv idg h
  have h0 : P (PTree.empty (globdef (CompCert4Lean.Common.AST.fundef function) Unit))
      (PTree.empty function) := by
    intro id f hget
    change PTree.get id (PTree.Empty : PTree.tree function) = some f at hget
    simp [PTree.get] at hget
  have h := REC p.prog_defs
      (PTree.empty (globdef (CompCert4Lean.Common.AST.fundef function) Unit))
      (PTree.empty function) h0
  change P (prog_defmap p) (funenv_program cfg p)
  exact h


theorem fenv_compat_linkorder : fenv_compat_linkorderStatement := by
  intro cunit prog fenv horder hcompat id f hget
  change @linkorder CompCert4Lean.Backend.RTL.program
      (@Linker_prog CompCert4Lean.Backend.RTL.fundef Unit
        (@Linker_fundef CompCert4Lean.Backend.RTL.function) Linker_unit)
      cunit prog at horder
  have hc := hcompat id f hget
  obtain ⟨gd2, hget2, hgd⟩ :=
    CompCert4Lean.Common.Linking.prog_defmap_linkorder_proof
      (F := CompCert4Lean.Backend.RTL.fundef) (V := Unit)
      (LF := Linker_fundef CompCert4Lean.Backend.RTL.function) (LV := Linker_unit)
      cunit prog id (Gfun (Internal f)) horder hc
  cases hgd with
  | linkorder_def_fun _ _ hfd =>
      cases hfd with
      | linkorder_fundef_refl _ => exact hget2

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Coqlib

private theorem shiftpos_posToNat_formula (x n : positive) :
    posToNat (shiftpos x n) = posToNat x + posToNat n - 1 := by
  let nx := posToNat x
  let nn := posToNat n
  have hx : 0 < nx := by
    dsimp [nx]
    exact posToNat_positive x
  have hn : 0 < nn := by
    dsimp [nn]
    exact posToNat_positive n
  have hsum : 0 < nx + nn := by omega
  have hadd : posToNat (PArith.BinPos.Pos.add x n) = nx + nn := by
    simpa [PArith.BinPos.Pos.add, nx, nn] using posToNat_posOfNat hsum
  have hne : PArith.BinPos.Pos.add x n ≠ xH := by
    intro h
    have h' := hadd
    rw [h] at h'
    have hxH : posToNat xH = 1 := rfl
    omega
  have hpred := shiftpos_pred_nat_sub_one (PArith.BinPos.Pos.add x n) hne
  unfold shiftpos
  rw [hpred, hadd]

theorem shiftpos_diff : shiftpos_diffStatement := by
  intro x y n hxy h
  exact hxy (shiftpos_inj x y n h)

theorem shiftpos_above : shiftpos_aboveStatement := by
  intro x n
  unfold Ple PArith.BinPos.Pos.le
  rw [shiftpos_posToNat_formula]
  have hn := posToNat_positive n
  have hx := posToNat_positive x
  omega

theorem shiftpos_not_below : shiftpos_not_belowStatement := by
  intro x n h
  unfold Plt PArith.BinPos.Pos.lt at h
  have habove : posToNat n ≤ posToNat (shiftpos x n) := by
    rw [shiftpos_posToNat_formula]
    have hn := posToNat_positive n
    have hx := posToNat_positive x
    omega
  omega

theorem shiftpos_below : shiftpos_belowStatement := by
  intro x n
  unfold Plt PArith.BinPos.Pos.lt
  rw [shiftpos_posToNat_formula]
  change posToNat x + posToNat n - 1 < posToNat (PArith.BinPos.Pos.add x n)
  rw [show posToNat (PArith.BinPos.Pos.add x n) =
      posToNat x + posToNat n by
    simpa [PArith.BinPos.Pos.add] using
      posToNat_posOfNat (by
        have hx := posToNat_positive x
        have hn := posToNat_positive n
        omega : 0 < posToNat x + posToNat n)]
  have hx := posToNat_positive x
  have hn := posToNat_positive n
  omega

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

theorem mlist_iter2_fold : mlist_iter2_foldStatement := by
  intro A B f l
  induction l with
  | nil =>
      intro s
      refine ⟨CompCert4Lean.Backend.Inlining.sincr_refl s, ?_⟩
      rfl
  | cons p l ih =>
      rcases p with ⟨x, y⟩
      intro s
      unfold mlist_iter2 CompCert4Lean.Backend.Inlining.bind
      generalize hxy : f x y s = r
      cases r with
      | R _ s1 i1 =>
          obtain ⟨i2, hi2⟩ := ih s1
          have hfold :
              List.foldl
                  (fun a p =>
                    match f p.1 p.2 a with
                    | CompCert4Lean.Backend.Inlining.R _ s2 _ => s2)
                  s ((x, y) :: l) =
                List.foldl
                  (fun a p =>
                    match f p.1 p.2 a with
                    | CompCert4Lean.Backend.Inlining.R _ s2 _ => s2)
                  s1 l := by
            simp [hxy]
          refine ⟨?_, ?_⟩
          · rw [hfold]
            exact CompCert4Lean.Backend.Inlining.sincr_trans _ _ _ i1 i2
          · have hstate0 : (f x y s).2 = s1 := by
              rw [hxy]
            have hstate : (mlist_iter2 f l s1).2 =
                List.foldl
                  (fun a p =>
                    match f p.1 p.2 a with
                    | CompCert4Lean.Backend.Inlining.R _ s2 _ => s2)
                  s1 l :=
              congrArg (fun r => r.2) hi2
            simp
            rw [hstate, hstate0]

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem ptree_mfold_spec : ptree_mfold_specStatement := by
  intro A f t s x s' i h
  rcases mlist_iter2_fold positive A f (CompCert4Lean.Lib.Maps.PTree.elements t) s with ⟨i', hi'⟩
  unfold ptree_mfold at h
  rw [CompCert4Lean.Lib.Maps.PTree.fold_spec_proof] at h
  let stepR : res (A := Unit) (s := s) → (positive × A) → res (A := Unit) (s := s) := fun a p =>
    match a with
    | R _ s1 h1 =>
        match f p.1 p.2 s1 with
        | R _ s2 h2 => R () s2 (Inlining.sincr_trans _ _ _ h1 h2)
  let stepS : state → (positive × A) → state := fun a p =>
    match f p.1 p.2 a with
    | R _ s2 _ => s2
  change List.foldl stepR (R () s (.intro (Nat.le_refl _) (Nat.le_refl _) (Int.le_refl _)))
      (CompCert4Lean.Lib.Maps.PTree.elements t) = R x s' i at h
  have fold_state_aux : ∀ (l : List (positive × A)) (s0 : state)
      (h0 : sincr s s0),
      (match List.foldl stepR (R () s0 h0) l with
       | R _ sf _ => sf) = List.foldl stepS s0 l := by
    intro l
    induction l with
    | nil => intro s0 h0; rfl
    | cons p l ih =>
        intro s0 h0
        simp only [List.foldl]
        cases hf : f p.1 p.2 s0 with
        | R u s1 h1 =>
            have hi := ih s1 (Inlining.sincr_trans s s0 s1 h0 h1)
            simpa [stepR, stepS, hf] using hi
  have fold_state :
      (match List.foldl stepR (R () s (.intro (Nat.le_refl _) (Nat.le_refl _) (Int.le_refl _)))
          (CompCert4Lean.Lib.Maps.PTree.elements t) with
       | R _ sf _ => sf) =
        List.foldl stepS s (CompCert4Lean.Lib.Maps.PTree.elements t) :=
    fold_state_aux _ s (.intro (Nat.le_refl _) (Nat.le_refl _) (Int.le_refl _))
  have hs : List.foldl stepS s (CompCert4Lean.Lib.Maps.PTree.elements t) = s' := by
    have hstate := congrArg (fun q => match q with | R _ sf _ => sf) h
    simpa [fold_state] using hstate
  cases hs
  exact ⟨i', hi'⟩

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem add_moves_unchanged : add_moves_unchangedStatement := by
  have succ_formula : ∀ p : positive,
      posToNat (PArith.BinPos.Pos.succ p) = posToNat p + 1 := by
    intro p
    induction p with
    | xH => simp [PArith.BinPos.Pos.succ, posToNat]
    | xI p ih => simp [PArith.BinPos.Pos.succ, posToNat, ih]; omega
    | xO p => simp [PArith.BinPos.Pos.succ, posToNat]
  intro srcs
  induction srcs with
  | nil =>
      intro dsts pc2 s pc1 s' i pc h hpc
      cases dsts <;>
        simp [add_moves, ret] at h ⊢ <;>
        rcases h with ⟨rfl, rfl⟩ <;> rfl
  | cons src srcs ih =>
      intro dsts pc2 s pc1 s' i pc h hpc
      cases dsts with
      | nil =>
          simp [add_moves, ret] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          rfl
      | cons dst dsts =>
          unfold add_moves at h
          unfold CompCert4Lean.Backend.Inlining.bind at h
          simp only [add_instr] at h
          cases hstep : (add_moves srcs dsts s.st_nextnode
              { st_nextreg := s.st_nextreg
                st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
                st_code := PTree.set s.st_nextnode
                  (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code
                st_stksize := s.st_stksize }) with
          | R next s1 hinc =>
              simp [hstep] at h
              rcases h with ⟨rfl, rfl⟩
              have hcode : PTree.get pc s1.st_code =
                  PTree.get pc
                    (PTree.set s.st_nextnode
                      (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code) := by
                apply ih dsts s.st_nextnode
                  { st_nextreg := s.st_nextreg
                    st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
                    st_code := PTree.set s.st_nextnode
                      (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code
                    st_stksize := s.st_stksize }
                  next s1 hinc pc
                exact hstep
                rcases hpc with hlt | hge
                · left
                  change posToNat pc < posToNat
                    (PArith.BinPos.Pos.succ s.st_nextnode)
                  change posToNat pc < posToNat s.st_nextnode at hlt
                  rw [succ_formula]
                  omega
                · exact Or.inr hge
              rw [hcode]
              rcases hpc with hlt | hge
              · apply PTree.gso
                intro heq
                subst pc
                change posToNat s.st_nextnode < posToNat s.st_nextnode at hlt
                omega
              · apply PTree.gso
                intro heq
                subst pc
                have hstrict : posToNat (PArith.BinPos.Pos.succ s.st_nextnode) ≤
                    posToNat s1.st_nextnode := by
                  exact hinc.2
                change posToNat s1.st_nextnode ≤ posToNat s.st_nextnode at hge
                rw [succ_formula] at hstrict
                omega

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem add_moves_spec : add_moves_specStatement := by
  have succ_formula : ∀ p : positive,
      posToNat (PArith.BinPos.Pos.succ p) = posToNat p + 1 := by
    intro p
    induction p with
    | xH => simp [PArith.BinPos.Pos.succ, posToNat]
    | xI p ih => simp [PArith.BinPos.Pos.succ, posToNat, ih]; omega
    | xO p => simp [PArith.BinPos.Pos.succ, posToNat]
  intro srcs
  induction srcs with
  | nil =>
      intro dsts pc2 s pc1 s' i c h hcode
      cases dsts with
      | nil =>
          simp [add_moves, ret] at h
          rcases h with ⟨rfl, rfl⟩
          exact tr_moves.tr_moves_nil [] [] pc2 (Or.inl rfl)
      | cons dst dsts =>
          simp [add_moves, ret] at h
          rcases h with ⟨rfl, rfl⟩
          exact tr_moves.tr_moves_nil [] (dst :: dsts) pc2 (Or.inl rfl)
  | cons src srcs ih =>
      intro dsts pc2 s pc1 s' i c h hcode
      cases dsts with
      | nil =>
          simp [add_moves, ret] at h
          rcases h with ⟨rfl, rfl⟩
          exact tr_moves.tr_moves_nil (src :: srcs) [] pc2 (Or.inr rfl)
      | cons dst dsts =>
          unfold add_moves at h
          unfold CompCert4Lean.Backend.Inlining.bind at h
          simp only [add_instr] at h
          cases hstep : (add_moves srcs dsts s.st_nextnode
              { st_nextreg := s.st_nextreg
                st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
                st_code := PTree.set s.st_nextnode
                  (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code
                st_stksize := s.st_stksize }) with
          | R next s1 hinc =>
              simp [hstep] at h
              rcases h with ⟨rfl, rfl⟩
              apply tr_moves.tr_moves_cons (pc1 := next)
                (pc2 := s.st_nextnode) (pc3 := pc2)
              · apply ih
                  dsts s.st_nextnode
                  { st_nextreg := s.st_nextreg
                    st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
                    st_code := PTree.set s.st_nextnode
                      (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code
                    st_stksize := s.st_stksize }
                  next s1 hinc c hstep
                intro pc hpc hlt
                apply hcode pc
                · change posToNat s.st_nextnode ≤ posToNat pc
                  change posToNat (PArith.BinPos.Pos.succ s.st_nextnode) ≤
                    posToNat pc at hpc
                  rw [succ_formula] at hpc
                  omega
                · exact hlt
              · have hlt_succ : Plt s.st_nextnode
                    (PArith.BinPos.Pos.succ s.st_nextnode) := by
                  change posToNat s.st_nextnode <
                    posToNat (PArith.BinPos.Pos.succ s.st_nextnode)
                  rw [succ_formula]
                  omega
                have hlt_final : Plt s.st_nextnode s1.st_nextnode := by
                  have hinc' := hinc.2
                  change posToNat (PArith.BinPos.Pos.succ s.st_nextnode) ≤
                    posToNat s1.st_nextnode at hinc'
                  change posToNat s.st_nextnode < posToNat s1.st_nextnode
                  rw [succ_formula] at hinc'
                  omega
                have hc := hcode s.st_nextnode (by
                  change posToNat s.st_nextnode ≤ posToNat s.st_nextnode
                  omega) hlt_final
                rw [hc]
                have hunch := add_moves_unchanged srcs dsts s.st_nextnode
                  { st_nextreg := s.st_nextreg
                    st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
                    st_code := PTree.set s.st_nextnode
                      (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code
                    st_stksize := s.st_stksize }
                  next s1 hinc s.st_nextnode hstep (Or.inl hlt_succ)
                rw [hunch]
                exact PTree.gss s.st_nextnode
                  (RTL.Iop X86.Op.Omove [src] dst pc2) s.st_code

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Maps

theorem set_instr_other : set_instr_otherStatement := by
  intro pc instr s x s' i pc' h hne
  simp [Inlining.set_instr] at h
  cases h
  exact CompCert4Lean.Lib.Maps.PTree.gso instr s.st_code hne

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Maps

theorem set_instr_same : set_instr_sameStatement := by
  intro pc instr s x s' i c h hc
  simp [Inlining.set_instr] at h
  cases h
  rw [hc]
  exact CompCert4Lean.Lib.Maps.PTree.gss pc instr s.st_code

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inline_function_unchanged_below :
    ∀ (fe : funenv)
      (rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit),
      (∀ fe' L ctx f s x s' i pc,
        rec fe' L ctx f s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
        PTree.get pc s'.st_code = PTree.get pc s.st_code) →
      ∀ ctx id f (lookup : PTree.get id fe = some f) args retpc retreg
        s x s' i pc,
        inline_function fe rec ctx id f lookup args retpc retreg s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc s.st_nextnode →
        PTree.get pc s'.st_code = PTree.get pc s.st_code := by
  intro fe rec hrec ctx id f lookup args retpc retreg s x s' i pc h
    hbelow hlt
  unfold inline_function at h
  simp [Inlining.bind, reserve_nodes, reserve_regs] at h
  let rs : Inlining.state :=
    { st_nextreg := PArith.BinPos.Pos.add s.st_nextreg (max_reg_function f)
      st_nextnode := PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f)
      st_code := s.st_code
      st_stksize := s.st_stksize }
  generalize hrec' : rec (PTree.remove id fe) _
      (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
        f.fn_stacksize retpc retreg) f rs = rr at h
  cases rr with
  | R u s3 i3 =>
      cases hmove : add_moves (sregs ctx args)
          (sregs (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
            f.fn_stacksize retpc retreg) f.fn_params)
          (spc (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
            f.fn_stacksize retpc retreg) f.fn_entrypoint) s3 with
      | R n s4 i4 =>
          simp [hmove] at h
          rcases h with ⟨_, hs⟩
          subst s'
          have hpleAdd : Ple s.st_nextnode rs.st_nextnode := by
            change posToNat s.st_nextnode ≤
              posToNat (PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f))
            change posToNat s.st_nextnode ≤
              posToNat (posOfNat (posToNat s.st_nextnode + posToNat (max_pc_function f)))
            have hpos : 0 < posToNat s.st_nextnode + posToNat (max_pc_function f) :=
              Nat.add_pos_left (posToNat_positive s.st_nextnode) _
            rw [posToNat_posOfNat hpos]
            omega
          have hrecpc := hrec (PTree.remove id fe) _
            (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize retpc retreg)
            f rs u s3 i3 pc hrec'
            (by
              change Ple s.st_nextnode rs.st_nextnode
              exact hpleAdd)
            (by
              change Plt pc s.st_nextnode
              exact hlt)
          have hmove := add_moves_unchanged
            (sregs ctx args)
            (sregs (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize retpc retreg) f.fn_params)
            (spc (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize retpc retreg) f.fn_entrypoint)
            s3 n s4 i4 pc hmove
            (Or.inl (Plt_Ple_trans pc s.st_nextnode s3.st_nextnode hlt
              (Ple_trans s.st_nextnode rs.st_nextnode s3.st_nextnode hpleAdd i3.2)))
          exact hmove.trans (hrecpc.trans rfl)

private theorem inline_tail_function_unchanged_below :
    ∀ (fe : funenv)
      (rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit),
      (∀ fe' L ctx f s x s' i pc,
        rec fe' L ctx f s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
        PTree.get pc s'.st_code = PTree.get pc s.st_code) →
      ∀ ctx id f (lookup : PTree.get id fe = some f) args
        s x s' i pc,
        inline_tail_function fe rec ctx id f lookup args s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc s.st_nextnode →
        PTree.get pc s'.st_code = PTree.get pc s.st_code := by
  intro fe rec hrec ctx id f lookup args s x s' i pc h hbelow hlt
  unfold inline_tail_function at h
  simp [Inlining.bind, reserve_nodes, reserve_regs] at h
  let rs : Inlining.state :=
    { st_nextreg := PArith.BinPos.Pos.add s.st_nextreg (max_reg_function f)
      st_nextnode := PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f)
      st_code := s.st_code
      st_stksize := s.st_stksize }
  generalize hrec' : rec (PTree.remove id fe) _
      (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
        f.fn_stacksize) f rs = rr at h
  cases rr with
  | R u s3 i3 =>
      cases hmove : add_moves (sregs ctx args)
          (sregs (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
            f.fn_stacksize) f.fn_params)
          (spc (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
            f.fn_stacksize) f.fn_entrypoint) s3 with
      | R n s4 i4 =>
          simp [hmove] at h
          rcases h with ⟨_, hs⟩
          subst s'
          have hpleAdd : Ple s.st_nextnode rs.st_nextnode := by
            change posToNat s.st_nextnode ≤
              posToNat (PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f))
            change posToNat s.st_nextnode ≤
              posToNat (posOfNat (posToNat s.st_nextnode + posToNat (max_pc_function f)))
            have hpos : 0 < posToNat s.st_nextnode + posToNat (max_pc_function f) :=
              Nat.add_pos_left (posToNat_positive s.st_nextnode) _
            rw [posToNat_posOfNat hpos]
            omega
          have hrecpc := hrec (PTree.remove id fe) _
            (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize)
            f rs u s3 i3 pc hrec'
            (by
              change Ple s.st_nextnode rs.st_nextnode
              exact hpleAdd)
            (by
              change Plt pc s.st_nextnode
              exact hlt)
          have hmove := add_moves_unchanged
            (sregs ctx args)
            (sregs (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize) f.fn_params)
            (spc (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize) f.fn_entrypoint)
            s3 n s4 i4 pc hmove
            (Or.inl (Plt_Ple_trans pc s.st_nextnode s3.st_nextnode hlt
              (Ple_trans s.st_nextnode rs.st_nextnode s3.st_nextnode hpleAdd i3.2)))
          exact hmove.trans (hrecpc.trans rfl)

private theorem expand_instr_unchanged_aux :
    ∀ (fe : funenv)
      (rec : ∀ fe', size_fenv fe' < size_fenv fe → context → function → mon Unit),
      (∀ fe' L ctx f s x s' i pc,
        rec fe' L ctx f s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc ctx.dpc →
        PTree.get pc s'.st_code = PTree.get pc s.st_code) →
      ∀ ctx pc instr s x s' i pc',
        expand_instr fe rec ctx pc instr s = R x s' i →
        Ple ctx.dpc s.st_nextnode → Plt pc' s.st_nextnode → pc' ≠ spc ctx pc →
        PTree.get pc' s'.st_code = PTree.get pc' s.st_code := by
  intro fe rec hrec ctx pc instr s x s' i pc' h hbelow hlt hne
  unfold expand_instr at h
  cases instr with
  | Inop succ =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Iop op args result succ =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Iload chunk addr args dst succ =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Istore chunk addr args src succ =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Ibuiltin ef args result succ =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Icond cond args ifso ifnot =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Ijumptable arg tbl =>
      change set_instr (spc ctx pc) _ s = R x s' i at h
      exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Ireturn result =>
      cases hret : ctx.retinfo with
      | none =>
          simp only [hret] at h
          exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
      | some returnInfo =>
          simp only [hret] at h
          exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
  | Icall sig ros args result succ =>
      cases hcan : can_inline fe ros with
      | Cannot_inline =>
          simp only [hcan] at h
          exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
      | Can_inline id f target lookup =>
          simp only [hcan] at h
          unfold Inlining.bind at h
          cases hi : inline_function fe rec ctx id f lookup args succ result s with
          | R next s1 i1 =>
              rw [hi] at h
              cases hs : set_instr (spc ctx pc) (Inop next) s1 with
              | R u s2 i2 =>
                  have hs_eq : s2 = s' := by
                    have hstate := congrArg (fun r => r.2) h
                    simpa [Inlining.bind, hi, hs] using hstate
                  subst s'
                  have hinline := inline_function_unchanged_below fe rec hrec ctx id f lookup
                    args succ result s next s1 i1 pc' hi hbelow hlt
                  exact (set_instr_other (spc ctx pc) (Inop next) s1 u s2 i2 pc'
                    hs hne).trans hinline
  | Itailcall sig ros args =>
      cases hcan : can_inline fe ros with
      | Cannot_inline =>
          cases hret : ctx.retinfo with
          | none =>
              simp only [hcan, hret] at h
              exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
          | some returnInfo =>
              simp only [hcan, hret] at h
              exact set_instr_other (spc ctx pc) _ s x s' i pc' h hne
      | Can_inline id f target lookup =>
          simp only [hcan] at h
          unfold Inlining.bind at h
          cases hi : inline_tail_function fe rec ctx id f lookup args s with
          | R next s1 i1 =>
              rw [hi] at h
              cases hs : set_instr (spc ctx pc) (Inop next) s1 with
              | R u s2 i2 =>
                  have hs_eq : s2 = s' := by
                    have hstate := congrArg (fun r => r.2) h
                    simpa [Inlining.bind, hi, hs] using hstate
                  subst s'
                  have hinline := inline_tail_function_unchanged_below fe rec hrec ctx id f lookup
                    args s next s1 i1 pc' hi hbelow hlt
                  exact (set_instr_other (spc ctx pc) (Inop next) s1 u s2 i2 pc'
                    hs hne).trans hinline

theorem iter_expand_instr_unchanged : iter_expand_instr_unchangedStatement := by
  intro fe rec hrec ctx pc l s x s' i h hbelow hlt hnot hnr
  cases x
  induction l generalizing s with
  | nil =>
      simp [mlist_iter2] at h
      cases h
      rfl
  | cons a l ih =>
      rcases a with ⟨pc1, instr1⟩
      change Inlining.bind (expand_instr fe rec ctx pc1 instr1)
          (fun _ => mlist_iter2 (expand_instr fe rec ctx) l) s = R () s' i at h
      cases hstep : expand_instr fe rec ctx pc1 instr1 s with
      | R y s1 i1 =>
          simp only [Inlining.bind] at h
          rw [hstep] at h
          cases htail : mlist_iter2 (expand_instr fe rec ctx) l s1 with
          | R z s2 i2 =>
            simp [Inlining.bind, htail] at h
            cases z
            subst s'
            have hlt1 : Plt pc s1.st_nextnode :=
              Plt_Ple_trans pc s.st_nextnode s1.st_nextnode hlt i1.2
            have hbelow1 : Ple ctx.dpc s1.st_nextnode :=
              Ple_trans ctx.dpc s.st_nextnode s1.st_nextnode hbelow i1.2
            change list_norepet (pc1 :: List.map Prod.fst l) at hnr
            cases hnr with
            | cons _ hhd hnr' =>
              simp only [List.map_cons] at hnot
              have hnot' : pc ∉ List.map (spc ctx) (List.map Prod.fst l) := by
                intro hin
                apply hnot
                exact List.mem_cons.mpr (Or.inr hin)
              have htail' := ih s1 i2 hbelow1 hlt1 hnot' hnr' htail
              calc
                PTree.get pc s2.st_code = PTree.get pc s1.st_code := htail'
                _ = PTree.get pc s.st_code :=
                  expand_instr_unchanged_aux fe rec hrec ctx pc1 instr1 s Unit.unit s1 i1 pc
                    hstep hbelow hlt (by
                      intro heq
                      apply hnot
                      exact List.mem_cons.mpr (Or.inl (heq ▸ rfl)))

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inliningspec_xelements_append {A : Type}
    (m : PTree.tree' A) (i : positive) (k1 k2 : List (positive × A)) :
    PTree.xelements' m i (k1 ++ k2) =
      PTree.xelements' m i k1 ++ k2 := by
  induction m generalizing i k1 k2 with
  | Node001 r ih => exact ih (xI i) k1 k2
  | Node010 x => simp [PTree.xelements']
  | Node011 x r ih => simp [PTree.xelements', ih, List.append_assoc]
  | Node100 l ih => exact ih (xO i) k1 k2
  | Node101 l r ihl ihr =>
      simp [PTree.xelements', ihl, ihr, List.append_assoc]
  | Node110 l x ih =>
      change PTree.xelements' l (xO i) ((PTree.prev i, x) :: (k1 ++ k2)) =
        PTree.xelements' l (xO i) ((PTree.prev i, x) :: k1) ++ k2
      exact ih (xO i) ((PTree.prev i, x) :: k1) k2
  | Node111 l x r ihl ihr =>
      simp only [PTree.xelements']
      rw [ihr (xI i) k1 k2]
      exact ihl (xO i) ((PTree.prev i, x) :: PTree.xelements' r (xI i) k1) k2

private theorem inliningspec_key_form {A : Type} (m : PTree.tree' A) (i : positive)
    (p : positive × A) (h : p ∈ PTree.xelements' m i []) :
    ∃ j, p.1 = PTree.prev_append i j := by
  induction m generalizing i p with
  | Node001 r ih =>
      have hr := ih (xI i) p (by simpa [PTree.xelements'] using h)
      rcases hr with ⟨j, hj⟩
      exact ⟨xI j, by simpa [PTree.prev_append] using hj⟩
  | Node010 x =>
      rcases p with ⟨k, v⟩
      simp [PTree.xelements'] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨xH, rfl⟩
  | Node011 x r ih =>
      rcases p with ⟨k, v⟩
      simp [PTree.xelements'] at h
      rcases h with h | h
      · have hp : (k, v) = (PTree.prev i, x) := by simpa using h
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨xH, rfl⟩
      · have hr := ih (xI i) (k, v) h
        rcases hr with ⟨j, hj⟩
        exact ⟨xI j, by simpa [PTree.prev_append] using hj⟩
  | Node100 l ih =>
      have hl := ih (xO i) p (by simpa [PTree.xelements'] using h)
      rcases hl with ⟨j, hj⟩
      exact ⟨xO j, by simpa [PTree.prev_append] using hj⟩
  | Node101 l r ihl ihr =>
      change p ∈ PTree.xelements' l (xO i) (PTree.xelements' r (xI i) []) at h
      rw [show PTree.xelements' l (xO i) (PTree.xelements' r (xI i) []) =
          PTree.xelements' l (xO i) [] ++ PTree.xelements' r (xI i) [] by
            simpa using inliningspec_xelements_append l (xO i) []
              (PTree.xelements' r (xI i) [])] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ihl (xO i) p h
        rcases hl with ⟨j, hj⟩
        exact ⟨xO j, by simpa [PTree.prev_append] using hj⟩
      · have hr := ihr (xI i) p h
        rcases hr with ⟨j, hj⟩
        exact ⟨xI j, by simpa [PTree.prev_append] using hj⟩
  | Node110 l x ih =>
      rcases p with ⟨k, v⟩
      change (k, v) ∈ PTree.xelements' l (xO i) [(PTree.prev i, x)] at h
      rw [show PTree.xelements' l (xO i) [(PTree.prev i, x)] =
          PTree.xelements' l (xO i) [] ++ [(PTree.prev i, x)] by
            simpa using inliningspec_xelements_append l (xO i) []
              [(PTree.prev i, x)]] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ih (xO i) (k, v) h
        rcases hl with ⟨j, hj⟩
        exact ⟨xO j, by simpa [PTree.prev_append] using hj⟩
      · have hp : (k, v) = (PTree.prev i, x) := by simpa using h
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨xH, rfl⟩
  | Node111 l x r ihl ihr =>
      rcases p with ⟨k, v⟩
      change (k, v) ∈ PTree.xelements' l (xO i)
        ((PTree.prev i, x) :: PTree.xelements' r (xI i) []) at h
      rw [show PTree.xelements' l (xO i)
          ((PTree.prev i, x) :: PTree.xelements' r (xI i) []) =
          PTree.xelements' l (xO i) [] ++
            ((PTree.prev i, x) :: PTree.xelements' r (xI i) []) by
              simpa using inliningspec_xelements_append l (xO i) []
                ((PTree.prev i, x) :: PTree.xelements' r (xI i) [])] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ihl (xO i) (k, v) h
        rcases hl with ⟨j, hj⟩
        exact ⟨xO j, by simpa [PTree.prev_append] using hj⟩
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · have hp : (k, v) = (PTree.prev i, x) := by simpa using h
          rcases hp with ⟨rfl, rfl⟩
          exact ⟨xH, rfl⟩
        · have hr := ihr (xI i) (k, v) h
          rcases hr with ⟨j, hj⟩
          exact ⟨xI j, by simpa [PTree.prev_append] using hj⟩

private theorem inliningspec_prev_append_injective (i : positive) :
    Function.Injective (PTree.prev_append i) := by
  induction i with
  | xH => intro j k h; exact h
  | xI i ih =>
      intro j k h
      have h' : xI j = xI k := ih h
      cases h'
      rfl
  | xO i ih =>
      intro j k h
      have h' : xO j = xO k := ih h
      cases h'
      rfl

private theorem inliningspec_keys_disjoint {A B : Type}
    (l : PTree.tree' A) (r : PTree.tree' B) (i : positive) :
    ∀ k, k ∈ (PTree.xelements' l (xO i) []).map Prod.fst →
      k ∉ (PTree.xelements' r (xI i) []).map Prod.fst := by
  intro k hl hr
  rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩
  rcases List.mem_map.mp hr with ⟨q, hq, hkey⟩
  rcases inliningspec_key_form l (xO i) p hp with ⟨j, hj⟩
  rcases inliningspec_key_form r (xI i) q hq with ⟨k, hk⟩
  have heq : PTree.prev_append i (xO j) = PTree.prev_append i (xI k) := by
    calc
      PTree.prev_append i (xO j) = p.1 := by simpa [PTree.prev_append] using hj.symm
      _ = q.1 := hkey.symm
      _ = PTree.prev_append i (xI k) := by simpa [PTree.prev_append] using hk
  have hbits : xO j = xI k := inliningspec_prev_append_injective i heq
  cases hbits

private theorem inliningspec_key_not_in_xO {A : Type} (l : PTree.tree' A) (i : positive) :
    PTree.prev i ∉ (PTree.xelements' l (xO i) []).map Prod.fst := by
  intro h
  rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
  rcases inliningspec_key_form l (xO i) p hp with ⟨j, hj⟩
  have heq : PTree.prev_append i xH = PTree.prev_append i (xO j) := by
    calc
      PTree.prev_append i xH = PTree.prev i := by rfl
      _ = p.1 := hkey.symm
      _ = PTree.prev_append (xO i) j := hj
      _ = PTree.prev_append i (xO j) := by rfl
  have hbits : xH = xO j := inliningspec_prev_append_injective i heq
  cases hbits

private theorem inliningspec_key_not_in_xI {A : Type} (r : PTree.tree' A) (i : positive) :
    PTree.prev i ∉ (PTree.xelements' r (xI i) []).map Prod.fst := by
  intro h
  rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
  rcases inliningspec_key_form r (xI i) p hp with ⟨j, hj⟩
  have heq : PTree.prev_append i xH = PTree.prev_append i (xI j) := by
    calc
      PTree.prev_append i xH = PTree.prev i := by rfl
      _ = p.1 := hkey.symm
      _ = PTree.prev_append (xI i) j := hj
      _ = PTree.prev_append i (xI j) := by rfl
  have hbits : xH = xI j := inliningspec_prev_append_injective i heq
  cases hbits

private theorem inliningspec_keys_nodup {A : Type} (m : PTree.tree' A) (i : positive) :
    ((PTree.xelements' m i []).map Prod.fst).Nodup := by
  induction m generalizing i with
  | Node001 r ih => exact ih (xI i)
  | Node010 x => simp [PTree.xelements']
  | Node011 x r ih =>
      simp only [PTree.xelements', List.map_cons, List.nodup_cons]
      exact ⟨by
        intro h
        rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
        exact inliningspec_key_not_in_xI r i (by simpa [hkey] using h), ih (xI i)⟩
  | Node100 l ih => exact ih (xO i)
  | Node101 l r ihl ihr =>
      change ((PTree.xelements' l (xO i) (PTree.xelements' r (xI i) [])).map Prod.fst).Nodup
      rw [show PTree.xelements' l (xO i) (PTree.xelements' r (xI i) []) =
          PTree.xelements' l (xO i) [] ++ PTree.xelements' r (xI i) [] by
            simpa using inliningspec_xelements_append l (xO i) []
              (PTree.xelements' r (xI i) [])]
      simp only [List.map_append, List.nodup_append]
      exact ⟨ihl (xO i), ihr (xI i), by
        intro a ha b hb hEq
        exact inliningspec_keys_disjoint l r i a ha (by simpa [hEq] using hb)⟩
  | Node110 l x ih =>
      change ((PTree.xelements' l (xO i) [(PTree.prev i, x)]).map Prod.fst).Nodup
      rw [show PTree.xelements' l (xO i) [(PTree.prev i, x)] =
          PTree.xelements' l (xO i) [] ++ [(PTree.prev i, x)] by
            simpa using inliningspec_xelements_append l (xO i) []
              [(PTree.prev i, x)]]
      simp only [List.map_append, List.map_singleton]
      rw [List.nodup_append]
      refine ⟨ih (xO i), by simp, ?_⟩
      intro k hk b hb hkb
      have hb' : b = PTree.prev i := by simpa using hb
      have hkroot : k = PTree.prev i := hkb.trans hb'
      subst b
      apply inliningspec_key_not_in_xO l i
      rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
      exact List.mem_map.mpr ⟨p, hp, hpk.trans hkroot⟩
  | Node111 l x r ihl ihr =>
      change ((PTree.xelements' l (xO i)
        ((PTree.prev i, x) :: PTree.xelements' r (xI i) [])).map Prod.fst).Nodup
      rw [show PTree.xelements' l (xO i)
          ((PTree.prev i, x) :: PTree.xelements' r (xI i) []) =
          PTree.xelements' l (xO i) [] ++
            ((PTree.prev i, x) :: PTree.xelements' r (xI i) []) by
              simpa using inliningspec_xelements_append l (xO i) []
                ((PTree.prev i, x) :: PTree.xelements' r (xI i) [])]
      simp only [List.map_append]
      rw [List.nodup_append]
      have htail : ((PTree.prev i, x) :: PTree.xelements' r (xI i) []).map Prod.fst |>.Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨inliningspec_key_not_in_xI r i, ihr (xI i)⟩
      refine ⟨ihl (xO i), htail, ?_⟩
      intro k hk b hb hkb
      simp only [List.map_cons, List.mem_cons] at hb
      rcases hb with hroot | hright
      · apply inliningspec_key_not_in_xO l i
        rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
        exact List.mem_map.mpr ⟨p, hp, hpk.trans (hkb.trans hroot)⟩
      · exact inliningspec_keys_disjoint l r i k hk (by simpa [hkb] using hright)

private theorem inliningspec_elements_nodup {A : Type} (m : PTree.t A) :
    ((PTree.elements m).map Prod.fst).Nodup := by
  cases m with
  | Empty => simp [PTree.elements, PTree.xelements]
  | Nodes m => simpa [PTree.elements, PTree.xelements] using inliningspec_keys_nodup m xH

private theorem inliningspec_nodup_to_norepet {A : Type} :
    ∀ l : List A, l.Nodup → list_norepet l
  | [], _ => .nil _
  | a :: l, h =>
      .cons a (by
        intro ha
        exact (List.nodup_cons.mp h).1 ha)
        (inliningspec_nodup_to_norepet l (List.nodup_cons.mp h).2)

theorem expand_cfg_rec_unchanged : expand_cfg_rec_unchangedStatement := by
  intro fe rec hrec ctx f s x s' i pc h hbelow hlt
  unfold expand_cfg_rec at h
  cases hreq : request_stack (zAdd ctx.dstk ctx.mstk) s with
  | R u s0 i0 =>
      simp only [Inlining.bind] at h
      rw [hreq] at h
      cases hfold : ptree_mfold (expand_instr fe rec ctx) f.fn_code s0 with
      | R z s1 i1 =>
          simp [Inlining.bind, hfold] at h
          cases z
          subst s'
          have hcode : s0.st_code = s.st_code := by
            simpa [request_stack] using (congrArg (fun r => r.2.st_code) hreq).symm
          have hnext : s0.st_nextnode = s.st_nextnode := by
            simpa [request_stack] using (congrArg (fun r => r.2.st_nextnode) hreq).symm
          have hbelow0 : Ple ctx.dpc s0.st_nextnode := by
            rw [hnext]
            exact hbelow
          have hlt0 : Plt pc s0.st_nextnode := by
            exact Plt_Ple_trans pc ctx.dpc s0.st_nextnode hlt hbelow0
          have hspec := ptree_mfold_spec _ _
            f.fn_code s0 () s1 i1 hfold
          rcases hspec with ⟨i', hiter⟩
          have hnot : pc ∉ List.map (spc ctx)
              (List.map Prod.fst (PTree.elements f.fn_code)) := by
            intro hmem
            rcases List.mem_map.mp hmem with ⟨p, hp, hpc⟩
            rcases List.mem_map.mp hp with ⟨q, hq, hpq⟩
            rcases q with ⟨pc1, instr1⟩
            subst p
            subst pc
            apply shiftpos_not_below pc1 ctx.dpc
            exact hlt
          have hiter' := iter_expand_instr_unchanged fe rec hrec ctx pc
            (PTree.elements f.fn_code) s0 () s1 i' hiter hbelow0 hlt0 hnot
            (inliningspec_nodup_to_norepet _ (inliningspec_elements_nodup _))
          calc
            PTree.get pc s1.st_code = PTree.get pc s0.st_code := hiter'
            _ = PTree.get pc s.st_code := by simpa [hcode]

theorem min_alignment_pos : min_alignment_posStatement := by
  intro sz
  unfold min_alignment
  split
  · simp only [ZArith.BinInt.Z.gt, ZArith.BinInt.Z.lt, intOfZ,
      ZArith.BinInt.Z.of_nat, zOfInt]
    exact Int.natCast_pos.mpr (posToNat_positive _)
  · split
    · simp only [ZArith.BinInt.Z.gt, ZArith.BinInt.Z.lt, intOfZ,
        ZArith.BinInt.Z.of_nat, zOfInt]
      exact Int.natCast_pos.mpr (posToNat_positive _)
    · split
      · simp only [ZArith.BinInt.Z.gt, ZArith.BinInt.Z.lt, intOfZ,
          ZArith.BinInt.Z.of_nat, zOfInt]
        exact Int.natCast_pos.mpr (posToNat_positive _)
      · simp only [ZArith.BinInt.Z.gt, ZArith.BinInt.Z.lt, intOfZ,
          ZArith.BinInt.Z.of_nat, zOfInt]
        exact Int.natCast_pos.mpr (posToNat_positive _)

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem inliningspec_align_le (x y : Z)
    (hy : zGt y Z0) : zLe x (CompCert4Lean.Lib.Coqlib.align x y) := by
  unfold zGt at hy
  change intOfZ x ≤ intOfZ (CompCert4Lean.Lib.Coqlib.align x y)
  unfold CompCert4Lean.Lib.Coqlib.align
  simp only [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.div,
    ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hdiv := ZArith.Zdiv.Z_div_mod_eq_full
    (zOfInt (intOfZ x + intOfZ y - 1)) y
  have hdiv' := congrArg intOfZ hdiv
  simp only [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hdiv'
  change 0 < intOfZ y at hy
  have hmod := ZArith.Zdiv.Z_mod_lt (zOfInt (intOfZ x + intOfZ y - 1)) y hy
  change 0 ≤ intOfZ (ZArith.BinInt.Z.modulo
      (zOfInt (intOfZ x + intOfZ y - 1)) y) ∧
    intOfZ (ZArith.BinInt.Z.modulo
      (zOfInt (intOfZ x + intOfZ y - 1)) y) < intOfZ y at hmod
  simp only [ZArith.BinInt.Z.modulo, intOfZ_zOfInt] at hmod
  have hxone : intOfZ (Zpos xH) = 1 := rfl
  rw [hxone]
  simp only [ZArith.BinInt.Z.div, ZArith.BinInt.Z.modulo, intOfZ_zOfInt] at hdiv' ⊢
  have hdiv'' := hdiv'
  rw [Int.mul_comm] at hdiv''
  omega

private theorem inliningspec_align_divides (x y : Z)
    (hy : zGt y Z0) : ZArith.BinInt.Z.divide y (CompCert4Lean.Lib.Coqlib.align x y) := by
  unfold CompCert4Lean.Lib.Coqlib.align
  refine ⟨ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add x y) (Zpos xH)) y, ?_⟩
  simp only [ZArith.BinInt.Z.mul]
  apply congrArg zOfInt
  simp [Int.mul_comm]

private theorem inliningspec_expand_instr_spec_aux : expand_instr_specStatement := by
  intro fenv stacksize fe hfe rec hrec
  intro ctx pc instr s x s' i c hexp hdefs hopc hreg hstk hdstk hsize hunch hsame
  change code at c
  have hbase := set_instr_same
  unfold expand_instr at hexp
  cases instr with
  | Inop succ =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc) (Inop (spc ctx succ)) s = R x s' i at hexp
      apply tr_instr.tr_nop
      exact hbase _ _ _ _ _ _ _ hexp hsame
  | Iop op args res succ =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc)
        (Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx succ)) s = R x s' i at hexp
      apply tr_instr.tr_op
      · exact hdefs _ rfl
      · exact hbase _ _ _ _ _ _ _ hexp hsame
  | Iload chunk addr args res succ =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc)
        (Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx res) (spc ctx succ)) s = R x s' i at hexp
      apply tr_instr.tr_load
      · exact hdefs _ rfl
      · exact hbase _ _ _ _ _ _ _ hexp hsame
  | Istore chunk addr args src succ =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc)
        (Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx succ)) s = R x s' i at hexp
      apply tr_instr.tr_store
      exact hbase _ _ _ _ _ _ _ hexp hsame
  | Ibuiltin ef args res succ =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc)
        (Ibuiltin ef (args.map (sbuiltinarg ctx)) (sbuiltinres ctx res) (spc ctx succ)) s = R x s' i at hexp
      apply tr_instr.tr_builtin
      · cases res with
        | BR r => exact hdefs _ rfl
        | BR_none => trivial
        | BR_splitlong hi lo => trivial
      · exact hbase _ _ _ _ _ _ _ hexp hsame
  | Icond cond args ifso ifnot =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc)
        (Icond cond (sregs ctx args) (spc ctx ifso) (spc ctx ifnot)) s = R x s' i at hexp
      apply tr_instr.tr_cond
      exact hbase _ _ _ _ _ _ _ hexp hsame
  | Ijumptable arg tbl =>
      simp only [Inlining.expand_instr] at hexp
      change set_instr (spc ctx pc)
        (Ijumptable (sreg ctx arg) (tbl.map (spc ctx))) s = R x s' i at hexp
      apply tr_instr.tr_jumptable
      exact hbase _ _ _ _ _ _ _ hexp hsame
  | Ireturn result =>
      cases hret : ctx.retinfo with
      | none =>
          simp only [Inlining.expand_instr] at hexp
          simp only [hret] at hexp
          change set_instr (spc ctx pc) (Ireturn (Option.map (sreg ctx) result)) s = R x s' i at hexp
          apply tr_instr.tr_return
          · cases result <;> exact hbase _ _ _ _ _ _ _ hexp hsame
          · exact hret
      | some rinfo =>
          simp only [Inlining.expand_instr] at hexp
          simp only [hret] at hexp
          change set_instr (spc ctx pc) (inline_return ctx result rinfo) s = R x s' i at hexp
          apply tr_instr.tr_return_inlined
          · exact hbase _ _ _ _ _ _ _ hexp hsame
          · exact hret
  | Icall sig ros args result succ =>
      cases hcan : can_inline fe ros with
      | Cannot_inline =>
          simp only [Inlining.expand_instr] at hexp
          simp only [hcan] at hexp
          change set_instr (spc ctx pc)
            (Icall sig (sros ctx ros) (sregs ctx args) (sreg ctx result) (spc ctx succ)) s = R x s' i at hexp
          apply tr_instr.tr_call
          · exact hdefs _ rfl
          · exact hbase _ _ _ _ _ _ _ hexp hsame
      | Can_inline id f target lookup =>
          subst ros
          simp only [hcan] at hexp
          unfold Inlining.bind at hexp
          unfold Inlining.inline_function at hexp
          simp [Inlining.bind, reserve_nodes, reserve_regs] at hexp
          let rs : Inlining.state :=
            { st_nextreg := PArith.BinPos.Pos.add s.st_nextreg (max_reg_function f)
              st_nextnode := PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f)
              st_code := s.st_code
              st_stksize := s.st_stksize }
          generalize hrec' : rec (PTree.remove id fe) _
            (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize succ result) f rs = rr at hexp
          cases rr with
          | R urec s3 i3 =>
              cases hmove : add_moves (sregs ctx args)
                  (sregs (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                    f.fn_stacksize succ result) f.fn_params)
                  (spc (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                    f.fn_stacksize succ result) f.fn_entrypoint) s3 with
              | R next s4 i4 =>
                  cases houter : set_instr (spc ctx pc) (Inop next) s4 with
              | R uout s2 i2 =>
                      rw [hmove, houter] at hexp
                      cases hexp
                      simp at *
                      let ctx' := callcontext ctx s.st_nextnode s.st_nextreg
                        (max_reg_function f) f.fn_stacksize succ result
                      have hnode : Ple s.st_nextnode rs.st_nextnode := by
                        change posToNat s.st_nextnode ≤
                          posToNat (PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f))
                        change posToNat s.st_nextnode ≤
                          posToNat (posOfNat (posToNat s.st_nextnode + posToNat (max_pc_function f)))
                        have hp : 0 < posToNat s.st_nextnode + posToNat (max_pc_function f) :=
                          Nat.add_pos_left (posToNat_positive s.st_nextnode) _
                        rw [posToNat_posOfNat hp]
                        omega
                      have hregAdd : Ple s.st_nextreg rs.st_nextreg := by
                        change posToNat s.st_nextreg ≤
                          posToNat (PArith.BinPos.Pos.add s.st_nextreg (max_reg_function f))
                        change posToNat s.st_nextreg ≤
                          posToNat (posOfNat (posToNat s.st_nextreg + posToNat (max_reg_function f)))
                        have hp : 0 < posToNat s.st_nextreg + posToNat (max_reg_function f) :=
                          Nat.add_pos_left (posToNat_positive s.st_nextreg) _
                        rw [posToNat_posOfNat hp]
                        omega
                      refine @tr_instr.tr_call_inlined fenv stacksize ctx pc sig id args result succ c f next ctx' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                      · exact hdefs _ rfl
                      · exact hfe id f lookup
                      · exact hbase _ _ _ _ _ _ _ houter hsame
                      · apply add_moves_spec _ _ _ s3 next s4 i4 c hmove
                        intro pc0 hpc0 hpc0'
                        have hpc0s : Ple s.st_nextnode pc0 :=
                          Ple_trans s.st_nextnode s3.st_nextnode pc0
                            (Ple_trans s.st_nextnode rs.st_nextnode s3.st_nextnode hnode i3.2)
                            hpc0
                        have hlt2 : Plt pc0 s2.st_nextnode :=
                          Plt_Ple_trans pc0 s4.st_nextnode s2.st_nextnode hpc0' i2.2
                        rw [hunch pc0 hpc0s hlt2]
                        exact set_instr_other (spc ctx pc) (Inop next) s4 uout s2 i2 pc0 houter (by
                          intro heq
                          subst pc0
                          exact (Nat.not_lt_of_ge hpc0s) hopc)
                      · have hrecbody : tr_funbody fenv stacksize ctx' f c := by
                          exact hrec _ _ ctx' f rs urec s3 i3 c (by simpa [ctx'] using hrec')
                            (by
                              intro id0 f0 hget
                              change PTree.get id0 (PTree.remove id (fe : PTree.t function)) = some f0 at hget
                              have hr := @PTree.getRemove_equation function id0 id
                                (fe : PTree.t function)
                              rw [hr] at hget
                              split at hget
                              · contradiction
                              · rename_i hne
                                exact hfe id0 f0 hget)
                            (by
                              simpa [ctx', callcontext, rs] using
                                (Ple_refl (PArith.BinPos.Pos.add s.st_nextnode
                                  (max_pc_function f))))
                            (by simp [ctx', callcontext])
                            (by
                              simpa [ctx', callcontext, rs] using
                                (Ple_refl (PArith.BinPos.Pos.add s.st_nextreg
                                  (max_reg_function f))))
                            (by
                              simp only [ctx', callcontext]
                              change ZArith.BinInt.Z.le Z0
                                (ZArith.BinInt.Z.max f.fn_stacksize Z0)
                              exact ZArith.BinInt.Z.le_max_r f.fn_stacksize Z0)
                            (by rfl)
                            (by
                              exact inliningspec_align_divides (zAdd ctx.dstk ctx.mstk)
                                (min_alignment f.fn_stacksize) (min_alignment_pos _))
                            (by
                              simp only [ctx', callcontext]
                              have ha := inliningspec_align_le (zAdd ctx.dstk ctx.mstk)
                                (min_alignment f.fn_stacksize) (min_alignment_pos _)
                              have hsum : zGe (zAdd ctx.dstk ctx.mstk) Z0 := by
                                change 0 ≤ intOfZ (zAdd ctx.dstk ctx.mstk)
                                simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
                                change 0 ≤ intOfZ ctx.dstk at hdstk
                                change 0 ≤ intOfZ ctx.mstk at hstk
                                omega
                              change 0 ≤ intOfZ (CompCert4Lean.Lib.Coqlib.align
                                (zAdd ctx.dstk ctx.mstk) (min_alignment f.fn_stacksize))
                              change intOfZ (zAdd ctx.dstk ctx.mstk) ≤
                                intOfZ (CompCert4Lean.Lib.Coqlib.align
                                  (zAdd ctx.dstk ctx.mstk) (min_alignment f.fn_stacksize)) at ha
                              have hsum' : 0 ≤ intOfZ (zAdd ctx.dstk ctx.mstk) := hsum
                              have ha' : intOfZ (zAdd ctx.dstk ctx.mstk) ≤
                                  intOfZ (CompCert4Lean.Lib.Coqlib.align
                                    (zAdd ctx.dstk ctx.mstk) (min_alignment f.fn_stacksize)) := ha
                              exact Int.le_trans hsum' ha')
                            (by
                              change intOfZ s3.st_stksize ≤ intOfZ stacksize
                              have hs3s4 : intOfZ s3.st_stksize ≤ intOfZ s4.st_stksize := i4.3
                              have hs4s2 : intOfZ s4.st_stksize ≤ intOfZ s2.st_stksize := i2.3
                              have hs2size : intOfZ s2.st_stksize ≤ intOfZ stacksize := hsize
                              exact Int.le_trans (Int.le_trans hs3s4 hs4s2) hs2size)
                            (by
                              intro pc0 hpc0 hpc0'
                              have hpc0s : Ple s.st_nextnode pc0 := by
                                simpa [ctx', callcontext] using hpc0
                              have hlt2 : Plt pc0 s2.st_nextnode :=
                                Plt_Ple_trans pc0 s3.st_nextnode s2.st_nextnode hpc0'
                                  (Ple_trans s3.st_nextnode s4.st_nextnode s2.st_nextnode i4.2 i2.2)
                              have hne : pc0 ≠ spc ctx pc := by
                                intro heq
                                subst pc0
                                exact (Nat.not_lt_of_ge hpc0s) hopc
                              calc
                                PTree.get pc0 c = PTree.get pc0 s2.st_code := hunch pc0 hpc0s hlt2
                                _ = PTree.get pc0 s4.st_code := set_instr_other (spc ctx pc) (Inop next) s4 uout s2 i2 pc0 houter hne
                                _ = PTree.get pc0 s3.st_code := add_moves_unchanged
                                  (sregs ctx args)
                                  (sregs (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                                    f.fn_stacksize succ result) f.fn_params)
                                  (spc (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                                    f.fn_stacksize succ result) f.fn_entrypoint)
                                  s3 next s4 i4 pc0 hmove (Or.inl hpc0'))
                        exact hrecbody
                      · simp [ctx', callcontext]
                      · simpa [context_below, ctx', callcontext] using hreg
                      · simp only [context_stack_call, ctx', callcontext]
                        constructor
                        · exact hstk
                        · exact inliningspec_align_le (zAdd ctx.dstk ctx.mstk)
                            (min_alignment f.fn_stacksize) (min_alignment_pos _)
                        /-
                        · intro id0 f0 hget
                          change PTree.get id0 (PTree.remove id (fe : PTree.t function)) = some f0 at hget
                          have hr := @PTree.getRemove_equation function id0 id
                            (fe : PTree.t function)
                          rw [hr] at hget
                          split at hget
                          · contradiction
                          · rename_i hne
                            exact hfe id0 f0 hget
                        · simpa [ctx', rs] using
                            (show Ple (PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f))
                              s3.st_nextnode from by
                              exact Ple_trans (PArith.BinPos.Pos.add s.st_nextnode
                                (max_pc_function f)) rs.st_nextnode s3.st_nextnode
                                (by simpa [rs] using (Ple_refl _)) i3.2)
                        · simp [ctx']
                        · simpa [ctx', rs] using
                            (Ple_trans (PArith.BinPos.Pos.add s.st_nextreg (max_reg_function f))
                              rs.st_nextreg s3.st_nextreg
                              (by simpa [rs] using (Ple_refl _)) i3.1)
                        · simpa [ctx'] using (ZArith.BinInt.Z.le_max_r _ _)
                        · rfl
                        · apply align_divides
                          exact min_alignment_pos _
                        · simp [ctx']
                          have ha := align_le (zAdd ctx.dstk ctx.mstk)
                            (min_alignment f.fn_stacksize) (min_alignment_pos _)
                          have hsum : zGe (zAdd ctx.dstk ctx.mstk) Z0 := by
                            simp only [zGe, ZArith.BinInt.Z.ge]
                            simp only [zAdd]
                            omega
                          omega
                        · change intOfZ s3.st_stksize ≤ intOfZ stacksize
                          change intOfZ s3.st_stksize ≤ intOfZ s2.st_stksize at hsize
                          change intOfZ s3.st_stksize ≤ intOfZ s4.st_stksize at i4
                          change intOfZ s4.st_stksize ≤ intOfZ s2.st_stksize at i2
                          exact Int.le_trans (Int.le_trans i4.3 i2.3) hsize
                        · intro pc0 hpc0 hpc0'
                          have hpc0s : Ple s.st_nextnode pc0 :=
                            Ple_trans s.st_nextnode s3.st_nextnode pc0
                              (Ple_trans s.st_nextnode rs.st_nextnode s3.st_nextnode hnode i3.2) hpc0
                          have hlt2 : Plt pc0 s2.st_nextnode :=
                            Plt_Ple_trans pc0 s3.st_nextnode s2.st_nextnode hpc0'
                              (Ple_trans s3.st_nextnode s4.st_nextnode s2.st_nextnode i4.2 i2.2)
                          have hne : pc0 ≠ spc ctx pc := by
                            intro heq
                            subst pc0
                            exact (Nat.not_lt_of_ge hpc0s) hopc
                          calc
                            PTree.get pc0 c = PTree.get pc0 s2.st_code := hunch pc0 hpc0s hlt2
                            _ = PTree.get pc0 s4.st_code := set_instr_other (spc ctx pc) (Inop next) s4 u s2 i2 pc0 houter hne
                            _ = PTree.get pc0 s3.st_code := add_moves_unchanged
                              (sregs ctx args)
                              (sregs (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                                f.fn_stacksize succ result) f.fn_params)
                              (spc (callcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                                f.fn_stacksize succ result) f.fn_entrypoint)
                              s3 next s4 i4 pc0 hmove (Or.inl hpc0')
                      · simp [ctx']
                      · simp [ctx']
                        constructor
                        · exact hstk
                        · have ha := align_le (zAdd ctx.dstk ctx.mstk)
                            (min_alignment f.fn_stacksize) (min_alignment_pos _)
                          omega
                        -/
  | Itailcall sig ros args =>
      cases hcan : can_inline fe ros with
      | Cannot_inline =>
          cases hret : ctx.retinfo with
          | none =>
              simp only [Inlining.expand_instr] at hexp
              simp only [hcan, hret] at hexp
              change set_instr (spc ctx pc)
                (Itailcall sig (sros ctx ros) (sregs ctx args)) s = R x s' i at hexp
              apply tr_instr.tr_tailcall
              · exact hbase _ _ _ _ _ _ _ hexp hsame
              · exact hret
          | some rinfo =>
              simp only [Inlining.expand_instr] at hexp
              simp only [hcan, hret] at hexp
              rcases rinfo with ⟨rpc, rreg⟩
              change set_instr (spc ctx pc)
                (Icall sig (sros ctx ros) (sregs ctx args) rreg rpc) s = R x s' i at hexp
              apply tr_instr.tr_tailcall_call
              · exact hbase _ _ _ _ _ _ _ hexp hsame
              · exact hret
      | Can_inline id f target lookup =>
          subst ros
          simp only [hcan] at hexp
          unfold Inlining.bind at hexp
          unfold Inlining.inline_tail_function at hexp
          simp [Inlining.bind, reserve_nodes, reserve_regs] at hexp
          let rs : Inlining.state :=
            { st_nextreg := PArith.BinPos.Pos.add s.st_nextreg (max_reg_function f)
              st_nextnode := PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f)
              st_code := s.st_code
              st_stksize := s.st_stksize }
          generalize hrec' : rec (PTree.remove id fe) _
            (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
              f.fn_stacksize) f rs = rr at hexp
          cases rr with
          | R urec s3 i3 =>
              cases hmove : add_moves (sregs ctx args)
                  (sregs (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                    f.fn_stacksize) f.fn_params)
                  (spc (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                    f.fn_stacksize) f.fn_entrypoint) s3 with
              | R next s4 i4 =>
                  cases houter : set_instr (spc ctx pc) (Inop next) s4 with
                  | R uout s2 i2 =>
                      rw [hmove, houter] at hexp
                      cases hexp
                      simp at *
                      let ctx' := tailcontext ctx s.st_nextnode s.st_nextreg
                        (max_reg_function f) f.fn_stacksize
                      have hnode : Ple s.st_nextnode rs.st_nextnode := by
                        change posToNat s.st_nextnode ≤
                          posToNat (PArith.BinPos.Pos.add s.st_nextnode (max_pc_function f))
                        change posToNat s.st_nextnode ≤
                          posToNat (posOfNat (posToNat s.st_nextnode + posToNat (max_pc_function f)))
                        have hp : 0 < posToNat s.st_nextnode + posToNat (max_pc_function f) :=
                          Nat.add_pos_left (posToNat_positive s.st_nextnode) _
                        rw [posToNat_posOfNat hp]
                        omega
                      refine @tr_instr.tr_tailcall_inlined fenv stacksize ctx pc sig id args c f next ctx' ?_ ?_ ?_ ?_ ?_ ?_ ?_
                      · exact hfe id f lookup
                      · exact hbase _ _ _ _ _ _ _ houter hsame
                      · apply add_moves_spec _ _ _ s3 next s4 i4 c hmove
                        intro pc0 hpc0 hpc0'
                        have hpc0s : Ple s.st_nextnode pc0 :=
                          Ple_trans s.st_nextnode s3.st_nextnode pc0
                            (Ple_trans s.st_nextnode rs.st_nextnode s3.st_nextnode hnode i3.2) hpc0
                        have hlt2 : Plt pc0 s2.st_nextnode :=
                          Plt_Ple_trans pc0 s4.st_nextnode s2.st_nextnode hpc0' i2.2
                        rw [hunch pc0 hpc0s hlt2]
                        exact set_instr_other (spc ctx pc) (Inop next) s4 uout s2 i2 pc0 houter (by
                          intro heq
                          subst pc0
                          exact (Nat.not_lt_of_ge hpc0s) hopc)
                      · have hrecbody : tr_funbody fenv stacksize ctx' f c := by
                          exact hrec _ _ ctx' f rs urec s3 i3 c (by simpa [ctx'] using hrec')
                            (by
                              intro id0 f0 hget
                              change PTree.get id0 (PTree.remove id (fe : PTree.t function)) = some f0 at hget
                              have hr := @PTree.getRemove_equation function id0 id (fe : PTree.t function)
                              rw [hr] at hget
                              split at hget
                              · contradiction
                              · rename_i hne
                                exact hfe id0 f0 hget)
                            (by
                              simpa [ctx', tailcontext, rs] using
                                (Ple_refl (PArith.BinPos.Pos.add s.st_nextnode
                                  (max_pc_function f))))
                            (by simp [ctx', tailcontext])
                            (by
                              simpa [ctx', tailcontext, rs] using
                                (Ple_refl (PArith.BinPos.Pos.add s.st_nextreg
                                  (max_reg_function f))))
                            (by
                              simp only [ctx', tailcontext]
                              change ZArith.BinInt.Z.le Z0
                                (ZArith.BinInt.Z.max f.fn_stacksize Z0)
                              exact ZArith.BinInt.Z.le_max_r f.fn_stacksize Z0)
                            (by rfl)
                            (by
                              exact inliningspec_align_divides ctx.dstk
                                (min_alignment f.fn_stacksize) (min_alignment_pos _))
                            (by
                              simp only [ctx', tailcontext]
                              have ha := inliningspec_align_le ctx.dstk
                                (min_alignment f.fn_stacksize) (min_alignment_pos _)
                              have hsum' : 0 ≤ intOfZ ctx.dstk := by
                                change 0 ≤ intOfZ ctx.dstk at hdstk
                                exact hdstk
                              have ha' : intOfZ ctx.dstk ≤
                                  intOfZ (CompCert4Lean.Lib.Coqlib.align ctx.dstk
                                    (min_alignment f.fn_stacksize)) := ha
                              exact Int.le_trans hsum' ha')
                            (by
                              change intOfZ s3.st_stksize ≤ intOfZ stacksize
                              have hs3s4 : intOfZ s3.st_stksize ≤ intOfZ s4.st_stksize := i4.3
                              have hs4s2 : intOfZ s4.st_stksize ≤ intOfZ s2.st_stksize := i2.3
                              have hs2size : intOfZ s2.st_stksize ≤ intOfZ stacksize := hsize
                              exact Int.le_trans (Int.le_trans hs3s4 hs4s2) hs2size)
                            (by
                              intro pc0 hpc0 hpc0'
                              have hpc0s : Ple s.st_nextnode pc0 := by
                                simpa [ctx', tailcontext] using hpc0
                              have hlt2 : Plt pc0 s2.st_nextnode :=
                                Plt_Ple_trans pc0 s3.st_nextnode s2.st_nextnode hpc0'
                                  (Ple_trans s3.st_nextnode s4.st_nextnode s2.st_nextnode i4.2 i2.2)
                              have hne : pc0 ≠ spc ctx pc := by
                                intro heq
                                subst pc0
                                exact (Nat.not_lt_of_ge hpc0s) hopc
                              calc
                                PTree.get pc0 c = PTree.get pc0 s2.st_code := hunch pc0 hpc0s hlt2
                                _ = PTree.get pc0 s4.st_code := set_instr_other (spc ctx pc) (Inop next) s4 uout s2 i2 pc0 houter hne
                                _ = PTree.get pc0 s3.st_code := add_moves_unchanged
                                  (sregs ctx args)
                                  (sregs (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                                    f.fn_stacksize) f.fn_params)
                                  (spc (tailcontext ctx s.st_nextnode s.st_nextreg (max_reg_function f)
                                    f.fn_stacksize) f.fn_entrypoint)
                                  s3 next s4 i4 pc0 hmove (Or.inl hpc0'))
                        exact hrecbody
                      · simp [ctx', tailcontext]
                      · simpa [context_below, ctx', tailcontext] using hreg
                      · simp only [context_stack_tailcall, ctx', tailcontext]

theorem iter_expand_instr_spec : iter_expand_instr_specStatement := by
  intro fenv stacksize fe hfe rec hrec_unchanged hrec_spec
  intro ctx l s x s' i c hiter hnr hdefs hopcs hreg hstk hdstk hsize hunch hsame
  induction l generalizing s x s' i with
  | nil =>
      intro pc instr hmem
      exact (_root_.List.not_mem_nil hmem).elim
  | cons a l ih =>
      rcases a with ⟨pc1, instr1⟩
      change Inlining.bind (expand_instr fe rec ctx pc1 instr1)
          (fun _ => mlist_iter2 (expand_instr fe rec ctx) l) s = R x s' i at hiter
      cases hstep : expand_instr fe rec ctx pc1 instr1 s with
      | R y s1 i1 =>
          simp only [Inlining.bind] at hiter
          rw [hstep] at hiter
          cases htail : mlist_iter2 (expand_instr fe rec ctx) l s1 with
          | R z s2 i2 =>
              simp [Inlining.bind, htail] at hiter
              cases z
              subst s'
              have hmem_head : (pc1, instr1) ∈ (pc1, instr1) :: l := by simp
              have hnr' : list_norepet (List.map Prod.fst l) := by
                change list_norepet (pc1 :: List.map Prod.fst l) at hnr
                cases hnr with
                | cons _ _ htailnr => exact htailnr
              have hdefs_head : ∀ r, instr_defs instr1 = some r → Ple r ctx.mreg := by
                intro r hr
                exact hdefs pc1 instr1 r (by simp) hr
              have hopc_head : Plt (spc ctx pc1) s.st_nextnode :=
                hopcs pc1 instr1 (by simp)
              have hbelow0 : Ple ctx.dpc s.st_nextnode := by
                exact Ple_trans ctx.dpc (spc ctx pc1) s.st_nextnode
                  (shiftpos_above pc1 ctx.dpc) (Plt_Ple _ _ hopc_head)
              have hbelow1 : Ple ctx.dpc s1.st_nextnode :=
                Ple_trans ctx.dpc s.st_nextnode s1.st_nextnode hbelow0 i1.2
              have hnot_tail : ∀ pc', Ple s.st_nextnode pc' → Plt pc' s1.st_nextnode →
                  pc' ∉ List.map (spc ctx) (List.map Prod.fst l) := by
                intro pc' hpc' hlt'
                intro hmem
                rcases List.mem_map.mp hmem with ⟨q, hq, hqpc⟩
                rcases List.mem_map.mp hq with ⟨pair, hpair, hpairq⟩
                rcases pair with ⟨pc0, instr0⟩
                have hpc0 : Plt (spc ctx pc0) s.st_nextnode :=
                  hopcs pc0 instr0 (by simp [hpair])
                have hqeq : q = pc0 := by simpa using hpairq.symm
                subst q
                subst pc'
                exact (Nat.not_lt_of_ge hpc') hpc0
              have hunch1 : ∀ pc', Ple s.st_nextnode pc' → Plt pc' s1.st_nextnode →
                  PTree.get pc' c = PTree.get pc' s1.st_code := by
                intro pc' hpc' hlt'
                have hlt2 : Plt pc' s2.st_nextnode := Plt_Ple_trans pc' s1.st_nextnode s2.st_nextnode hlt' i2.2
                calc
                  PTree.get pc' c = PTree.get pc' s2.st_code := hunch pc' hpc' hlt2
                  _ = PTree.get pc' s1.st_code :=
                    iter_expand_instr_unchanged fe rec hrec_unchanged ctx pc' l s1 () s2 i2 htail
                      hbelow1 hlt' (hnot_tail pc' hpc' hlt') hnr'
              have hsize1 : zLe s1.st_stksize stacksize := by
                change intOfZ s1.st_stksize ≤ intOfZ stacksize
                have hs1s2 : intOfZ s1.st_stksize ≤ intOfZ s2.st_stksize := i2.3
                have hs2size : intOfZ s2.st_stksize ≤ intOfZ stacksize := hsize
                exact Int.le_trans hs1s2 hs2size
              have hsame1 : PTree.get (spc ctx pc1) c =
                  PTree.get (spc ctx pc1) s1.st_code := by
                have hlt_head1 : Plt (spc ctx pc1) s1.st_nextnode :=
                  Plt_Ple_trans (spc ctx pc1) s.st_nextnode s1.st_nextnode hopc_head i1.2
                have hnot_head : spc ctx pc1 ∉
                    List.map (spc ctx) (List.map Prod.fst l) := by
                  intro hmem
                  rcases List.mem_map.mp hmem with ⟨q, hq, hqpc⟩
                  rcases List.mem_map.mp hq with ⟨pair, hpair, hpairq⟩
                  rcases pair with ⟨pc0, instr0⟩
                  have heq : spc ctx pc1 = spc ctx pc0 := by
                    have hqeq : q = pc0 := by simpa using hpairq.symm
                    subst q
                    exact hqpc.symm
                  have hpc_eq : pc1 = pc0 := shiftpos_inj pc1 pc0 ctx.dpc heq
                  change list_norepet (pc1 :: List.map Prod.fst l) at hnr
                  cases hnr with
                  | cons _ hhd _ =>
                      apply hhd
                      exact List.mem_map.mpr ⟨(pc0, instr0), hpair, by simpa [hpc_eq]⟩
                calc
                  PTree.get (spc ctx pc1) c = PTree.get (spc ctx pc1) s2.st_code :=
                    hsame pc1 instr1 (by simp)
                  _ = PTree.get (spc ctx pc1) s1.st_code :=
                    iter_expand_instr_unchanged fe rec hrec_unchanged ctx (spc ctx pc1) l s1 () s2 i2 htail
                      hbelow1 hlt_head1 hnot_head hnr'
              have htr_head := inliningspec_expand_instr_spec_aux fenv stacksize fe hfe rec hrec_spec
                ctx pc1 instr1 s () s1 i1 c hstep hdefs_head hopc_head hreg hstk hdstk hsize1 hunch1 hsame1
              intro pc instr hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with hmem | hmem
              · have hp : (pc, instr) = (pc1, instr1) := by simpa using hmem
                rcases hp with ⟨rfl, rfl⟩
                exact htr_head
              · apply ih (s := s1) (x := ()) (s' := s2) (i := i2)
                · exact htail
                · exact hnr'
                · intro pc0 instr0 r hmem0 hr
                  exact hdefs pc0 instr0 r (by simp [hmem0]) hr
                · intro pc0 instr0 hmem0
                  exact Plt_Ple_trans (spc ctx pc0) s.st_nextnode s1.st_nextnode
                    (hopcs pc0 instr0 (by simp [hmem0])) i1.2
                · exact Ple_trans (PArith.BinPos.Pos.add ctx.dreg ctx.mreg)
                    s.st_nextreg s1.st_nextreg hreg i1.1
                · exact hsize
                · intro pc0 hpc0 hlt0
                  exact hunch pc0 (Ple_trans s.st_nextnode s1.st_nextnode pc0 i1.2 hpc0) hlt0
                · intro pc0 instr0 hmem0
                  exact hsame pc0 instr0 (by simp [hmem0])
                · exact hmem

end CompCert4Lean.Backend.Inliningspec

namespace CompCert4Lean.Backend.Inliningspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Inlining
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem expand_cfg_rec_spec : expand_cfg_rec_specStatement := by
  intro fenv stacksize fe hfe rec hrec_unchanged hrec_spec
  intro ctx f s x s' i c h
  intro hbelow hmreg hreg hstk hstk_eq hdiv hdstk hsize hunch
  unfold expand_cfg_rec at h
  cases hreq : request_stack (zAdd ctx.dstk ctx.mstk) s with
  | R u s0 i0 =>
      simp only [Inlining.bind] at h
      rw [hreq] at h
      cases hfold : ptree_mfold (expand_instr fe rec ctx) f.fn_code s0 with
      | R z s1 i1 =>
          simp [hfold] at h
          cases z
          subst s'
          have hcode : s0.st_code = s.st_code := by
            simpa [request_stack] using (congrArg (fun r => r.2.st_code) hreq).symm
          have hnext : s0.st_nextnode = s.st_nextnode := by
            simpa [request_stack] using (congrArg (fun r => r.2.st_nextnode) hreq).symm
          have hnextreg : s0.st_nextreg = s.st_nextreg := by
            simpa [request_stack] using (congrArg (fun r => r.2.st_nextreg) hreq).symm
          have hadd : Ple ctx.dpc (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) := by
            change posToNat ctx.dpc ≤ posToNat (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f))
            change posToNat ctx.dpc ≤ posToNat (posOfNat (posToNat ctx.dpc + posToNat (max_pc_function f)))
            rw [posToNat_posOfNat]
            · exact Nat.le_add_right _ _
            · exact Nat.add_pos_left (posToNat_positive ctx.dpc) _
          have hbelow0 : Ple ctx.dpc s0.st_nextnode := by
            rw [hnext]
            exact Ple_trans _ _ _ hadd hbelow
          have hbelow_add0 : Ple (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f))
              s0.st_nextnode := by
            rw [hnext]
            exact hbelow
          have hspec := ptree_mfold_spec _ _ f.fn_code s0 () s1 i1 hfold
          rcases hspec with ⟨i', hiter⟩
          apply tr_funbody.tr_funbody_intro
          · intro r hr
            rw [hmreg]
            exact max_reg_function_params f r hr
          · intro pc instr hget
            have hmem : (pc, instr) ∈ PTree.elements f.fn_code :=
              PTree.elements_correct_proof f.fn_code pc (v := instr) hget
            have hdefs : ∀ pc instr r, (pc, instr) ∈ PTree.elements f.fn_code →
                instr_defs instr = some r → Ple r ctx.mreg := by
              intro pc0 instr0 r hr hd
              rw [hmreg]
              exact max_reg_function_def f pc0 instr0 r
                (PTree.elements_complete_proof _ _ _ hr) hd
            have hopcs : ∀ pc instr, (pc, instr) ∈ PTree.elements f.fn_code →
                Plt (spc ctx pc) s0.st_nextnode := by
              intro pc0 instr0 hm
              have hc : Ple pc0 (max_pc_function f) :=
                max_pc_function_sound f pc0 instr0
                  (PTree.elements_complete_proof _ _ _ hm)
              have hlt : Plt (spc ctx pc0)
                  (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) := by
                unfold spc Plt PArith.BinPos.Pos.lt
                rw [shiftpos_posToNat_formula]
                rw [show posToNat (PArith.BinPos.Pos.add ctx.dpc (max_pc_function f)) =
                    posToNat ctx.dpc + posToNat (max_pc_function f) by
                  simpa [PArith.BinPos.Pos.add] using
                    posToNat_posOfNat (by
                      have hd := posToNat_positive ctx.dpc
                      have hm := posToNat_positive (max_pc_function f)
                      omega : 0 < posToNat ctx.dpc + posToNat (max_pc_function f))]
                change posToNat pc0 ≤ posToNat (max_pc_function f) at hc
                have hd := posToNat_positive ctx.dpc
                have hp := posToNat_positive pc0
                have hm := posToNat_positive (max_pc_function f)
                omega
              exact Plt_Ple_trans _ _ _ hlt hbelow_add0
            have hreg0 : Ple (PArith.BinPos.Pos.add ctx.dreg ctx.mreg)
                s0.st_nextreg := by
              rw [hnextreg]
              exact hreg
            have hunch0 : ∀ pc', Ple s0.st_nextnode pc' → Plt pc' s1.st_nextnode →
                PTree.get pc' c = PTree.get pc' s1.st_code := by
              intro pc' hp hlt
              exact hunch pc' (Ple_trans ctx.dpc s0.st_nextnode pc' hbelow0 hp) hlt
            have hsame0 : ∀ pc instr, (pc, instr) ∈ PTree.elements f.fn_code →
                PTree.get (spc ctx pc) c = PTree.get (spc ctx pc) s1.st_code := by
              intro pc0 instr0 hm
              have hh : Plt (spc ctx pc0) s1.st_nextnode :=
                Plt_Ple_trans _ _ _ (hopcs pc0 instr0 hm) i1.2
              exact hunch (spc ctx pc0) (shiftpos_above pc0 ctx.dpc) hh
            exact iter_expand_instr_spec fenv stacksize fe hfe rec hrec_unchanged hrec_spec
              ctx (PTree.elements f.fn_code) s0 () s1 i' c hiter
              (inliningspec_nodup_to_norepet _ (inliningspec_elements_nodup _))
              hdefs hopcs hreg0 hstk hdstk hsize hunch0 hsame0 pc instr hmem
          · exact hstk_eq
          · exact hdiv
          · exact hdstk
          · have hsum0 : zLe (zAdd ctx.dstk ctx.mstk) s0.st_stksize := by
              have hs0size : s0.st_stksize =
                  ZArith.BinInt.Z.max s.st_stksize (zAdd ctx.dstk ctx.mstk) := by
                simpa [request_stack] using
                  (congrArg (fun r => r.2.st_stksize) hreq).symm
              rw [hs0size]
              exact ZArith.BinInt.Z.le_max_r s.st_stksize (zAdd ctx.dstk ctx.mstk)
            exact Int.le_trans (Int.le_trans hsum0 i1.3) hsize

end CompCert4Lean.Backend.Inliningspec
