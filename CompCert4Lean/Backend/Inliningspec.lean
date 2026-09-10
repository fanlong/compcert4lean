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
