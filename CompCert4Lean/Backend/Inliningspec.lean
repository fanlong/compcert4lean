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
    zLe Z0 f'.fn_stacksize →
    zLt f'.fn_stacksize Ptrofs.max_unsigned →
    tr_function p f f'

export tr_instr (tr_builtin tr_call tr_call_inlined tr_cond tr_jumptable tr_load
  tr_nop tr_op tr_return tr_return_inlined tr_store tr_tailcall tr_tailcall_call
  tr_tailcall_inlined)
export tr_funbody (tr_funbody_intro)
export tr_function (tr_function_intro)
export tr_moves (tr_moves_cons tr_moves_nil)

abbrev tr_builtin := @tr_instr.tr_builtin
abbrev tr_call := @tr_instr.tr_call
abbrev tr_call_inlined := @tr_instr.tr_call_inlined
abbrev tr_cond := @tr_instr.tr_cond
abbrev tr_funbody_intro := @tr_funbody.tr_funbody_intro
abbrev tr_function_intro := @tr_function.tr_function_intro
abbrev tr_jumptable := @tr_instr.tr_jumptable
abbrev tr_load := @tr_instr.tr_load
abbrev tr_moves_cons := @tr_moves.tr_moves_cons
abbrev tr_moves_nil := @tr_moves.tr_moves_nil
abbrev tr_nop := @tr_instr.tr_nop
abbrev tr_op := @tr_instr.tr_op
abbrev tr_return := @tr_instr.tr_return
abbrev tr_return_inlined := @tr_instr.tr_return_inlined
abbrev tr_store := @tr_instr.tr_store
abbrev tr_tailcall := @tr_instr.tr_tailcall
abbrev tr_tailcall_call := @tr_instr.tr_tailcall_call
abbrev tr_tailcall_inlined := @tr_instr.tr_tailcall_inlined

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
