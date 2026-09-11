import CompCert4Lean.Backend.Renumber
import CompCert4Lean.Common.Linking

/-!
# Correctness surface for RTL postorder renumbering

Definition-bearing translation of CompCert's `backend/Renumberproof.v`.
Proofs assigned to the later proof-migration phase are represented by exact
transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Renumberproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

def match_prog (p tp : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
    (fun x y : Unit => x = y)
    p tp

def transf_program_matchStatement : Prop :=
  ∀ p : program,
    match_prog p (CompCert4Lean.Backend.Renumber.transf_program p)

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      Genv.find_funct (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.Renumber.transf_fundef f)

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) v = some f →
      Genv.find_funct_ptr (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.Renumber.transf_fundef f)

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ id : ident,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    Senv.equiv
      (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def sig_preservedStatement : Prop :=
  ∀ f : fundef,
    funsig (CompCert4Lean.Backend.Renumber.transf_fundef f) = funsig f

def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (ros : Sum reg ident) (rs : regset) (fd : fundef),
      find_function (Genv.globalenv prog) ros rs = some fd →
      find_function (Genv.globalenv tprog) ros rs =
        some (CompCert4Lean.Backend.Renumber.transf_fundef fd)

def pnum (f : function) : PTree.t positive :=
  CompCert4Lean.Lib.Postorder.postorder (successors_map f) f.fn_entrypoint

def reach (f : function) (pc : node) : Prop :=
  CompCert4Lean.Lib.Postorder.reachable (successors_map f) f.fn_entrypoint pc

def renum_cfg_nodesStatement : Prop :=
  ∀ (f : PTree.t positive),
    (∀ (x₁ x₂ y : positive),
      PTree.get x₁ f = some y → PTree.get x₂ f = some y → x₁ = x₂) →
    ∀ (c : code) (x y : positive) (i : instruction),
      PTree.get x c = some i →
      PTree.get x f = some y →
      PTree.get y (CompCert4Lean.Backend.Renumber.renum_cfg f c) =
        some (CompCert4Lean.Backend.Renumber.renum_instr f i)

def transf_function_atStatement : Prop :=
  ∀ (f : function) (pc : node) (i : instruction),
    PTree.get pc f.fn_code = some i →
    reach f pc →
    PTree.get
        (CompCert4Lean.Backend.Renumber.renum_pc (pnum f) pc)
        (CompCert4Lean.Backend.Renumber.transf_function f).fn_code =
      some (CompCert4Lean.Backend.Renumber.renum_instr (pnum f) i)

def reach_succStatement : Prop :=
  ∀ (f : function) (pc : positive) (i : instruction) (s : node),
    PTree.get pc f.fn_code = some i →
    s ∈ successors_instr i →
    reach f pc →
    reach f s

inductive match_frames : stackframe → stackframe → Prop where
  | match_frames_intro (res : reg) (f : function) (sp : val) (pc : node) (rs : regset)
      (hreach : reach f pc) :
      match_frames
        (Stackframe res f sp pc rs)
        (Stackframe res (CompCert4Lean.Backend.Renumber.transf_function f) sp
          (CompCert4Lean.Backend.Renumber.renum_pc (pnum f) pc) rs)

export match_frames (match_frames_intro)

inductive match_states : state → state → Prop where
  | match_regular_states (stk : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (stk' : List stackframe)
      (stacks : list_forall2 match_frames stk stk')
      (hreach : reach f pc) :
      match_states
        (State stk f sp pc rs m)
        (State stk' (CompCert4Lean.Backend.Renumber.transf_function f) sp
          (CompCert4Lean.Backend.Renumber.renum_pc (pnum f) pc) rs m)
  | match_callstates (stk : List stackframe) (f : fundef) (args : List val) (m : mem)
      (stk' : List stackframe)
      (stacks : list_forall2 match_frames stk stk') :
      match_states
        (Callstate stk f args m)
        (Callstate stk' (CompCert4Lean.Backend.Renumber.transf_fundef f) args m)
  | match_returnstates (stk : List stackframe) (v : val) (m : mem)
      (stk' : List stackframe)
      (stacks : list_forall2 match_frames stk stk') :
      match_states
        (Returnstate stk v m)
        (Returnstate stk' v m)

export match_states (match_regular_states match_callstates match_returnstates)

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program), match_prog prog tprog →
    ∀ (S1 : state) (t : trace) (S2 : state),
      step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) S1 t S2 →
      ∀ S1', match_states S1 S1' →
        ∃ S2',
          step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi (Genv.globalenv tprog) S1' t S2' ∧
          match_states S2 S2'

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ S1 : state, initial_state prog S1 →
      ∃ S2, initial_state tprog S2 ∧ match_states S1 S2

def transf_final_statesStatement : Prop :=
  ∀ (S1 S2 : state) (r : int),
    match_states S1 S2 → final_state S1 r → final_state S2 r

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    forward_simulation
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.Renumberproof

namespace CompCert4Lean.Backend.Renumberproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker (CompCert4Lean.Backend.RTL.fundef) :=
    Linker_fundef CompCert4Lean.Backend.RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker (CompCert4Lean.Backend.RTL.program) :=
    Linker_prog (CompCert4Lean.Backend.RTL.fundef) Unit
  intro p
  unfold match_prog CompCert4Lean.Backend.Renumber.transf_program
    CompCert4Lean.Common.AST.transform_program
  constructor
  · induction p.prog_defs with
    | nil => exact list_forall2.nil _
    | cons hd tl ih =>
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                change list_forall2 _
                  ((id, Gfun f) :: tl)
                  ((id, Gfun (CompCert4Lean.Backend.Renumber.transf_fundef f)) ::
                    List.map (transform_program_globdef
                      CompCert4Lean.Backend.Renumber.transf_fundef) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_fun (ctx' := p)
                    · exact linkorder_refl _
                    · rfl
                · exact ih
            | Gvar v =>
                change list_forall2 _
                  ((id, Gvar v) :: tl)
                  ((id, Gvar v) ::
                    List.map (transform_program_globdef
                      CompCert4Lean.Backend.Renumber.transf_fundef) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_var
                    exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                · exact ih
  · exact ⟨rfl, rfl⟩

end CompCert4Lean.Backend.Renumberproof
namespace CompCert4Lean.Backend.Renumberproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private def renum_globdef_rel : globdef fundef Unit -> globdef fundef Unit -> Prop
  | .Gfun f, .Gfun tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f
  | .Gvar v, .Gvar tv => tv = v
  | _, _ => False

private def renum_defs_rel (ge tge : Genv.t fundef Unit) : Prop :=
  ge.genv_next = tge.genv_next ∧
    ∀ b g, Genv.find_def ge b = some g →
      ∃ tg, Genv.find_def tge b = some tg ∧ renum_globdef_rel g tg

private theorem renum_globdef_rel_of_match
    [Linker fundef] [Linker Unit]
    {p : CompCert4Lean.Common.AST.program fundef Unit}
    {g tg : globdef fundef Unit}
    (h : match_globdef
      (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
      (fun x y : Unit => x = y) p g tg) :
    renum_globdef_rel g tg := by
  cases h with
  | match_globdef_fun ctx' f1 f2 hl ht => exact ht
  | match_globdef_var v1 v2 hv =>
      cases hv with
      | match_globvar_intro i1 i2 init ro vol heq => cases heq; rfl

private theorem renum_defs_rel_add
    [Linker fundef] [Linker Unit]
    {p : CompCert4Lean.Common.AST.program fundef Unit}
    {ge tge : Genv.t fundef Unit}
    {id tid : ident} {g tg : globdef fundef Unit}
    (hr : renum_defs_rel ge tge)
    (hi : match_ident_globdef
      (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
      (fun x y : Unit => x = y) p (id, g) (tid, tg)) :
    renum_defs_rel (Genv.add_global ge (id, g))
      (Genv.add_global tge (tid, tg)) := by
  rcases hr with ⟨hnext, hold⟩
  rcases hi with ⟨hid, hm⟩
  change id = tid at hid
  subst tid
  have hrel := renum_globdef_rel_of_match hm
  refine ⟨?_, ?_⟩
  · simp only [Genv.add_global]
    rw [hnext]
  · intro b gd hget
    change positive at b
    change PTree.get b (PTree.set ge.genv_next g ge.genv_defs) = some gd at hget
    have hset := PTree.gsspec_proof b ge.genv_next g ge.genv_defs
    cases hpeq : peq b ge.genv_next with
    | left hb =>
        subst b
        have hg : gd = g := by
          have hs : PTree.get ge.genv_next
              (PTree.set ge.genv_next g ge.genv_defs) = some g := by
            cases hp : peq ge.genv_next ge.genv_next with
            | left heq => simpa [hp] using hset
            | right heq => exact False.elim (heq rfl)
          exact Option.some.inj (hget.symm.trans hs)
        subst gd
        refine ⟨tg, ?_, hrel⟩
        unfold Genv.find_def Genv.add_global
        rw [hnext]
        have hs := PTree.gsspec_proof (show positive from tge.genv_next)
          (show positive from tge.genv_next) tg tge.genv_defs
        cases hp : peq (show positive from tge.genv_next)
            (show positive from tge.genv_next) with
        | left heq => simpa [hp] using hs
        | right heq => exact False.elim (heq rfl)
    | right hb =>
        have hgetold : Genv.find_def ge b = some gd := by
          unfold Genv.find_def
          have hs : PTree.get b (PTree.set ge.genv_next g ge.genv_defs) =
              PTree.get b ge.genv_defs := by
            cases hp : peq b ge.genv_next with
            | left heq => exact False.elim (hb heq)
            | right heq => simpa [hp] using hset
          exact hs.symm.trans hget
        rcases hold b gd hgetold with ⟨td, ht, htd⟩
        refine ⟨td, ?_, htd⟩
        unfold Genv.find_def Genv.add_global
        have hs := PTree.gsspec_proof b (show positive from tge.genv_next)
          tg tge.genv_defs
        cases hp : peq b (show positive from tge.genv_next) with
        | left hbt => exact False.elim (hb (by simpa [hnext] using hbt))
        | right hbt =>
            have hs' : PTree.get b
                (PTree.set tge.genv_next tg tge.genv_defs) =
                PTree.get b tge.genv_defs := by
              simpa [hp] using hs
            exact hs'.trans ht

private theorem renum_defs_rel_add_globals
    [Linker fundef] [Linker Unit]
    {p : CompCert4Lean.Common.AST.program fundef Unit}
    (gl tgl : List (ident × globdef fundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
        (fun x y : Unit => x = y) p) gl tgl) :
    ∀ ge tge, renum_defs_rel ge tge →
      renum_defs_rel (Genv.add_globals ge gl) (Genv.add_globals tge tgl) := by
  induction hlist with
  | nil =>
      intro ge tge hrel
      simpa [Genv.add_globals] using hrel
  | cons hd thd hhd htl ih =>
      intro ge tge hrel
      simp only [Genv.add_globals, List.foldl]
      apply ih
      exact renum_defs_rel_add hrel hhd

theorem function_ptr_translated : function_ptr_translatedStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro prog tprog hmatch b f hf
  unfold match_prog at hmatch
  rcases hmatch with ⟨hdefs, hmain, hpub⟩
  have hinit : renum_defs_rel
      (Genv.empty_genv fundef Unit prog.prog_public)
      (Genv.empty_genv fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro b g h
      simp [Genv.empty_genv, Genv.find_def, PTree.get, PTree.empty] at h
  have hrel := renum_defs_rel_add_globals prog.prog_defs tprog.prog_defs
    hdefs _ _ hinit
  unfold Genv.find_funct_ptr at hf ⊢
  cases hdef : Genv.find_def (Genv.globalenv prog) b with
  | none => simp [hdef] at hf
  | some gd =>
      rw [hdef] at hf
      cases gd with
      | Gfun f0 =>
          have hf0 : f0 = f := Option.some.inj hf
          subst f0
          rcases hrel.2 b (Gfun f) hdef with ⟨tg, htg, htgrel⟩
          cases tg with
          | Gfun tf =>
              cases htgrel
              rw [show Genv.globalenv tprog =
                Genv.add_globals (Genv.empty_genv fundef Unit tprog.prog_public)
                  tprog.prog_defs from rfl]
              rw [htg]
          | Gvar v => exact False.elim htgrel
      | Gvar v => simp at hf

theorem functions_translated : functions_translatedStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro prog tprog hmatch v f hf
  cases v with
  | Vptr b ofs =>
      by_cases hz : Ptrofs.eq ofs Ptrofs.zero = true
      · unfold Genv.find_funct at hf ⊢
        simp [hz] at hf ⊢
        exact function_ptr_translated prog tprog hmatch b f hf
      · unfold Genv.find_funct at hf
        simp [hz] at hf
  | _ =>
      unfold Genv.find_funct at hf
      simp at hf

private def renum_symb_next_rel (ge tge : Genv.t fundef Unit) : Prop :=
  tge.genv_symb = ge.genv_symb ∧ tge.genv_next = ge.genv_next

private theorem renum_symb_next_add
    [Linker fundef] [Linker Unit] [Linker program]
    {prog : program} {ge tge : Genv.t fundef Unit}
    {id tid : ident} {g tg : globdef fundef Unit}
    (hrel : renum_symb_next_rel ge tge)
    (hitem : match_ident_globdef
      (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
      (fun x y : Unit => x = y) prog (id, g) (tid, tg)) :
    renum_symb_next_rel (Genv.add_global ge (id, g))
      (Genv.add_global tge (tid, tg)) := by
  rcases hrel with ⟨hsymb, hnext⟩
  rcases hitem with ⟨hid, hmatch⟩
  change id = tid at hid
  subst tid
  constructor
  · simp only [Genv.add_global]
    rw [hsymb, hnext]
  · simp only [Genv.add_global]
    rw [hnext]

private theorem renum_symb_next_add_globals
    [Linker fundef] [Linker Unit] [Linker program]
    {prog : program}
    (gl tgl : List (ident × globdef fundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ ge tge, renum_symb_next_rel ge tge →
      renum_symb_next_rel (Genv.add_globals ge gl)
        (Genv.add_globals tge tgl) := by
  induction hlist with
  | nil =>
      intro ge tge hrel
      simpa [Genv.add_globals] using hrel
  | cons hd thd hhd htl ih =>
      intro ge tge hrel
      simp only [Genv.add_globals, List.foldl]
      apply ih
      exact renum_symb_next_add hrel hhd

theorem symbols_preserved : symbols_preservedStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro prog tprog hmatch id
  unfold match_prog at hmatch
  rcases hmatch with ⟨hdefs, hmain, hpub⟩
  have hinit : renum_symb_next_rel
      (Genv.empty_genv fundef Unit prog.prog_public)
      (Genv.empty_genv fundef Unit tprog.prog_public) := by
    constructor <;> rfl
  have hrel := renum_symb_next_add_globals prog.prog_defs tprog.prog_defs
    hdefs _ _ hinit
  unfold Genv.globalenv Genv.find_symbol
  rw [hrel.1]

private theorem renum_ptree_get_set_same {A : Type} (x : positive) (v : A)
    (m : PTree.t A) :
    PTree.get x (PTree.set x v m) = some v := by
  have h := PTree.gsspec_proof x x v m
  cases hpeq : peq x x with
  | left hx => simpa [hpeq] using h
  | right hx => exact False.elim (hx rfl)

private theorem renum_ptree_get_set_other {A : Type} (x k : positive) (v : A)
    (m : PTree.t A) (hneq : x ≠ k) :
    PTree.get x (PTree.set k v m) = PTree.get x m := by
  have h := PTree.gsspec_proof x k v m
  cases hpeq : peq x k with
  | left hx => exact False.elim (hneq hx)
  | right hx => simpa [hpeq] using h

theorem renum_cfg_nodes : renum_cfg_nodesStatement := by
  intro f hinj
  let P : code -> code -> Prop := fun c c' =>
    ∀ x y i, PTree.get x c = some i -> PTree.get x f = some y ->
      PTree.get y c' = some (CompCert4Lean.Backend.Renumber.renum_instr f i)
  intro c
  change P c (CompCert4Lean.Backend.Renumber.renum_cfg f c)
  unfold CompCert4Lean.Backend.Renumber.renum_cfg
  apply PTree_Properties.fold_rec_proof
  · intro m m' a heq hP x y i hget hf
    apply hP x y i
    · rw [heq x]
      exact hget
    · exact hf
  · intro x y i hget hf
    simp [PTree.get, PTree.empty] at hget
  · intro m a k v hkm hkc hP x y i hget hf
    have hset := PTree.gsspec_proof x k v m
    cases hpeq : peq x k with
    | left hxk =>
        subst x
        have hset' : PTree.get k (PTree.set k v m) = some v := by
          simpa [hpeq] using hset
        have hi : v = i := Option.some.inj (hset'.symm.trans hget)
        subst i
        unfold CompCert4Lean.Backend.Renumber.renum_node
        cases hfk : PTree.get k f with
        | none => simp [hfk] at hf
        | some y' =>
            have hy : y' = y := Option.some.inj (hfk.symm.trans hf)
            subst y'
            simpa [hfk] using (renum_ptree_get_set_same y
              (CompCert4Lean.Backend.Renumber.renum_instr f v) a)
    | right hxk =>
        have hset' : PTree.get x (PTree.set k v m) = PTree.get x m := by
          simpa [hpeq] using hset
        have hgetm : PTree.get x m = some i := hset'.symm.trans hget
        have hres := hP x y i hgetm hf
        unfold CompCert4Lean.Backend.Renumber.renum_node
        cases hfk : PTree.get k f with
        | none => simpa [hfk] using hres
        | some y' =>
            have hyy' : y ≠ y' := by
              intro heq
              subst y'
              exact hxk (hinj x k y hf hfk)
            simpa [hfk] using
              ((renum_ptree_get_set_other y y'
                (CompCert4Lean.Backend.Renumber.renum_instr f v) a hyy').trans hres)

end CompCert4Lean.Backend.Renumberproof

namespace CompCert4Lean.Backend.Renumberproof

theorem sig_preserved : sig_preservedStatement := by
  intro f
  cases f <;> rfl

end CompCert4Lean.Backend.Renumberproof

namespace CompCert4Lean.Backend.Renumberproof

private theorem renumberproof_map1_get {A B : Type} (f : A → B) (i : CompCert4Lean.Lib.Maps.PTree.elt)
    (m : CompCert4Lean.Lib.Maps.PTree.t A) :
    CompCert4Lean.Lib.Maps.PTree.get i (CompCert4Lean.Lib.Maps.PTree.map1 f m) =
      Option.map f (CompCert4Lean.Lib.Maps.PTree.get i m) := by
  cases m with
  | Empty => rfl
  | Nodes m =>
      revert i
      induction m with
      | Node001 r ih =>
          intro i
          cases i with
          | xH => rfl
          | xO q => rfl
          | xI q => exact ih q
      | Node010 x => intro i; cases i <;> rfl
      | Node011 x r ih =>
          intro i
          cases i with
          | xH => rfl
          | xO q => rfl
          | xI q => exact ih q
      | Node100 l ih =>
          intro i
          cases i with
          | xH => rfl
          | xO q => exact ih q
          | xI q => rfl
      | Node101 l r ihl ihr =>
          intro i
          cases i with
          | xH => rfl
          | xO q => exact ihl q
          | xI q => exact ihr q
      | Node110 l x ih =>
          intro i
          cases i with
          | xH => rfl
          | xO q => exact ih q
          | xI q => rfl
      | Node111 l x r ihl ihr =>
          intro i
          cases i with
          | xH => rfl
          | xO q => exact ihl q
          | xI q => exact ihr q

theorem reach_succ : reach_succStatement := by
  intro f pc i s hcode hsucc hreach
  apply CompCert4Lean.Lib.Postorder.reachable_succ pc
    (CompCert4Lean.Backend.RTL.successors_instr i) s hreach
  · unfold CompCert4Lean.Backend.RTL.successors_map
    change CompCert4Lean.Lib.Maps.PTree.get pc
      (CompCert4Lean.Lib.Maps.PTree.map1
        (fun j : CompCert4Lean.Backend.RTL.instruction =>
          (CompCert4Lean.Backend.RTL.successors_instr j :
            List CompCert4Lean.Lib.Postorder.node)) f.fn_code) =
      some (CompCert4Lean.Backend.RTL.successors_instr i :
        List CompCert4Lean.Lib.Postorder.node)
    have hmap := renumberproof_map1_get
      (fun j : CompCert4Lean.Backend.RTL.instruction =>
        (CompCert4Lean.Backend.RTL.successors_instr j :
          List CompCert4Lean.Lib.Postorder.node)) pc
      (show CompCert4Lean.Lib.Maps.PTree.tree
        CompCert4Lean.Backend.RTL.instruction from f.fn_code)
    simpa [hcode] using hmap
  · exact hsucc

end CompCert4Lean.Backend.Renumberproof

namespace CompCert4Lean.Backend.Renumberproof

theorem find_function_translated : find_function_translatedStatement := by
  intro prog tprog hmatch ros rs fd hfind
  cases ros with
  | inl r =>
      exact functions_translated prog tprog hmatch
        (CompCert4Lean.Backend.Registers.Regmap.get r rs) fd hfind
  | inr symb =>
      change
        (match CompCert4Lean.Common.Globalenvs.Genv.find_symbol
            (CompCert4Lean.Common.Globalenvs.Genv.globalenv prog) symb with
        | none => none
        | some b =>
            CompCert4Lean.Common.Globalenvs.Genv.find_funct_ptr
              (CompCert4Lean.Common.Globalenvs.Genv.globalenv prog) b) = some fd at hfind
      change
        (match CompCert4Lean.Common.Globalenvs.Genv.find_symbol
            (CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog) symb with
        | none => none
        | some b =>
            CompCert4Lean.Common.Globalenvs.Genv.find_funct_ptr
              (CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog) b) =
          some (CompCert4Lean.Backend.Renumber.transf_fundef fd)
      cases hs : CompCert4Lean.Common.Globalenvs.Genv.find_symbol
          (CompCert4Lean.Common.Globalenvs.Genv.globalenv prog) symb with
      | none => simp [hs] at hfind
      | some b =>
          have hs' := symbols_preserved prog tprog hmatch symb
          rw [hs', hs]
          exact function_ptr_translated prog tprog hmatch b fd
            (by simpa [hs] using hfind)

end CompCert4Lean.Backend.Renumberproof

namespace CompCert4Lean.Backend.Renumberproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private def renumberproof_volatile_next_rel
    (ge tge : CompCert4Lean.Common.Globalenvs.Genv.t fundef Unit) : Prop :=
  ge.genv_next = tge.genv_next ∧
    ∀ b, Genv.block_is_volatile ge b = Genv.block_is_volatile tge b

private theorem renumberproof_volatile_next_add
    [Linker program]
    {prog : program} {ge tge : CompCert4Lean.Common.Globalenvs.Genv.t fundef Unit}
    {id tid : ident} {g tg : globdef fundef Unit}
    (hrel : renumberproof_volatile_next_rel ge tge)
    (hitem : match_ident_globdef
      (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
      (fun x y : Unit => x = y) prog (id, g) (tid, tg)) :
    renumberproof_volatile_next_rel
      (Genv.add_global ge (id, g)) (Genv.add_global tge (tid, tg)) := by
  rcases hrel with ⟨hnext, hvol⟩
  rcases hitem with ⟨hid, hm⟩
  change id = tid at hid
  subst tid
  constructor
  · simp only [Genv.add_global]
    rw [hnext]
  · intro b
    change positive at b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def Genv.add_global
    by_cases hb : b = ge.genv_next
    · subst b
      have hs : PTree.get (show positive from ge.genv_next)
          (PTree.set ge.genv_next g ge.genv_defs) = some g :=
        renum_ptree_get_set_same (show positive from ge.genv_next) g ge.genv_defs
      have ht : PTree.get (show positive from tge.genv_next)
          (PTree.set tge.genv_next tg tge.genv_defs) = some tg :=
        renum_ptree_get_set_same (show positive from tge.genv_next) tg tge.genv_defs
      rw [hs]
      rw [hnext]
      rw [ht]
      cases hm with
      | match_globdef_fun ctx' f1 f2 horder htrans => rfl
      | match_globdef_var v1 v2 hvar =>
          cases hvar
          rfl
    · have htneq : b ≠ tge.genv_next := by
        intro heq
        apply hb
        rw [hnext]
        exact heq
      have hs : PTree.get b (PTree.set (show positive from ge.genv_next) g ge.genv_defs) =
          PTree.get b ge.genv_defs :=
        renum_ptree_get_set_other b (show positive from ge.genv_next) g ge.genv_defs hb
      have ht : PTree.get b (PTree.set (show positive from tge.genv_next) tg tge.genv_defs) =
          PTree.get b tge.genv_defs :=
        renum_ptree_get_set_other b (show positive from tge.genv_next) tg tge.genv_defs htneq
      rw [hs, ht]
      exact hvol b

private theorem renumberproof_volatile_next_add_globals
    [Linker program]
    {prog : program}
    (gl tgl : List (ident × globdef fundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ ge tge, renumberproof_volatile_next_rel ge tge →
      renumberproof_volatile_next_rel
        (Genv.add_globals ge gl) (Genv.add_globals tge tgl) := by
  induction hlist with
  | nil =>
      intro ge tge hrel
      simpa [Genv.add_globals] using hrel
  | cons hd thd hhd htl ih =>
      intro ge tge hrel
      simp only [Genv.add_globals, List.foldl]
      apply ih
      exact renumberproof_volatile_next_add hrel hhd

private theorem renumberproof_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

theorem senv_preserved : senv_preservedStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro prog tprog hmatch
  unfold Senv.equiv
  constructor
  · intro id
    exact symbols_preserved prog tprog hmatch id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact renumberproof_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact renumberproof_add_globals_public _ _
    unfold Genv.public_symbol
    rw [symbols_preserved prog tprog hmatch id, ht, hp]
    rw [hmatch.2.2]
  · intro b
    change positive at b
    have hinit : renumberproof_volatile_next_rel
        (Genv.empty_genv fundef Unit prog.prog_public)
        (Genv.empty_genv fundef Unit tprog.prog_public) := by
      constructor
      · rfl
      · intro b
        simp [Genv.empty_genv, Genv.block_is_volatile, Genv.find_var_info,
          Genv.find_def, PTree.get, PTree.empty]
    have hrel := renumberproof_volatile_next_add_globals
      prog.prog_defs tprog.prog_defs hmatch.1 _ _ hinit
    exact (hrel.2 b).symm

end CompCert4Lean.Backend.Renumberproof
