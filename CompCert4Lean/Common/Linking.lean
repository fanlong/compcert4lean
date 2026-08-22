import CompCert4Lean.Common.AST

/-!
# Separate compilation and syntactic linking

This module translates the definition-bearing surface selected from
CompCert's `common/Linking.v`.  Proofs assigned to the later proof-migration
phase are represented by transparent proposition descriptors.
-/

namespace CompCert4Lean.Common.Linking

open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List

private abbrev Res := CompCert4Lean.Common.Errors.res

/-! ## Syntactic linkers -/

class Linker (A : Type) where
  link : A → A → Option A
  linkorder : A → A → Prop
  linkorder_refl : ∀ x, linkorder x x
  linkorder_trans : ∀ x y z, linkorder x y → linkorder y z → linkorder x z
  link_linkorder : ∀ x y z, link x y = some z → linkorder x z ∧ linkorder y z

export Linker (link linkorder linkorder_refl linkorder_trans link_linkorder)

def link_fundef {F : Type} (fd1 fd2 : fundef F) : Option (fundef F) :=
  match fd1, fd2 with
  | .Internal _, .Internal _ => none
  | .External ef1, .External ef2 =>
      match external_function_eq ef1 ef2 with
      | .left _ => some (.External ef1)
      | .right _ => none
  | .Internal f, .External (.EF_external _ _) => some (.Internal f)
  | .External (.EF_external _ _), .Internal f => some (.Internal f)
  | _, _ => none

inductive linkorder_fundef {F : Type} : fundef F → fundef F → Prop where
  | linkorder_fundef_refl (fd : fundef F) : linkorder_fundef fd fd
  | linkorder_fundef_ext_int (f : F)
      (id : CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string)
      (sg : signature) :
      linkorder_fundef (.External (.EF_external id sg)) (.Internal f)

export linkorder_fundef (linkorder_fundef_refl linkorder_fundef_ext_int)

instance Linker_fundef (F : Type) : Linker (fundef F) where
  link := link_fundef
  linkorder := linkorder_fundef
  linkorder_refl := linkorder_fundef_refl
  linkorder_trans := by
    intro x y z hxy hyz
    cases hxy <;> cases hyz <;> constructor
  link_linkorder := by
    intro x y z h
    cases x with
    | Internal f1 =>
        cases y with
        | Internal f2 => simp [link_fundef] at h
        | External ef =>
            cases ef <;> simp [link_fundef] at h
            case EF_external id sg =>
              subst z
              exact ⟨linkorder_fundef_refl _, linkorder_fundef_ext_int f1 id sg⟩
    | External ef1 =>
        cases y with
        | Internal f2 =>
            cases ef1 <;> simp [link_fundef] at h
            case EF_external id sg =>
              subst z
              exact ⟨linkorder_fundef_ext_int f2 id sg, linkorder_fundef_refl _⟩
        | External ef2 =>
            cases hEq : external_function_eq ef1 ef2 with
            | left heq =>
                simp [link_fundef, hEq] at h
                subst ef2
                subst z
                exact ⟨linkorder_fundef_refl _, linkorder_fundef_refl _⟩
            | right _ => simp [link_fundef, hEq] at h

private inductive LinkClosure {A : Type} (op : A → A → Option A) : A → A → Prop where
  | refl (x : A) : LinkClosure op x x
  | left {x y z : A} : op x y = some z → LinkClosure op x z
  | right {x y z : A} : op x y = some z → LinkClosure op y z
  | trans {x y z : A} : LinkClosure op x y → LinkClosure op y z → LinkClosure op x z

private inductive InitClassification where
  | external
  | common (size : Z)
  | definitive

private def classifyInit : List init_data → InitClassification
  | [] => .external
  | [Init_space size] => .common size
  | _ => .definitive

private def initializerLink (i1 i2 : List init_data) : Option (List init_data) :=
  match classifyInit i1, classifyInit i2 with
  | .external, _ => some i2
  | _, .external => some i1
  | .common size1, _ =>
      match zeq size1 (init_data_list_size i2) with
      | .left _ => some i2
      | .right _ => none
  | _, .common size2 =>
      match zeq size2 (init_data_list_size i1) with
      | .left _ => some i1
      | .right _ => none
  | _, _ => none

private def initializerLinker : Linker (List init_data) where
  link := initializerLink
  linkorder := LinkClosure initializerLink
  linkorder_refl := LinkClosure.refl
  linkorder_trans := by
    intro x y z hxy hyz
    exact LinkClosure.trans hxy hyz
  link_linkorder := by
    intro x y z h
    exact ⟨LinkClosure.left h, LinkClosure.right h⟩

def link_vardef {V : Type} [LV : Linker V]
    (v1 v2 : globvar V) : Option (globvar V) :=
  match LV.link v1.gvar_info v2.gvar_info with
  | none => none
  | some info =>
      match initializerLinker.link v1.gvar_init v2.gvar_init with
      | none => none
      | some init =>
          if h : v1.gvar_readonly = v2.gvar_readonly ∧
              v1.gvar_volatile = v2.gvar_volatile then
            some
              { gvar_info := info
                gvar_init := init
                gvar_readonly := v1.gvar_readonly
                gvar_volatile := v1.gvar_volatile }
          else
            none

inductive linkorder_vardef {V : Type} [LV : Linker V] :
    globvar V → globvar V → Prop where
  | linkorder_vardef_intro (info1 info2 : V)
      (i1 i2 : List init_data) (ro vo : Bool) :
      LV.linkorder info1 info2 →
      initializerLinker.linkorder i1 i2 →
      linkorder_vardef
        { gvar_info := info1
          gvar_init := i1
          gvar_readonly := ro
          gvar_volatile := vo }
        { gvar_info := info2
          gvar_init := i2
          gvar_readonly := ro
          gvar_volatile := vo }

export linkorder_vardef (linkorder_vardef_intro)

instance Linker_vardef (V : Type) [LV : Linker V] : Linker (globvar V) where
  link := link_vardef
  linkorder := linkorder_vardef
  linkorder_refl := by
    intro v
    exact linkorder_vardef_intro _ _ _ _ _ _ (LV.linkorder_refl _) (initializerLinker.linkorder_refl _)
  linkorder_trans := by
    intro x y z hxy hyz
    cases hxy with
    | linkorder_vardef_intro xinfo yinfo xinit yinit ro vo hinfo hinit =>
        cases hyz with
        | linkorder_vardef_intro _ zinfo _ zinit _ _ hinfo' hinit' =>
            exact linkorder_vardef_intro _ _ _ _ _ _
              (LV.linkorder_trans _ _ _ hinfo hinfo')
              (initializerLinker.linkorder_trans _ _ _ hinit hinit')
  link_linkorder := by
    intro x y z h
    rcases x with ⟨xinfo, xinit, xro, xvo⟩
    rcases y with ⟨yinfo, yinit, yro, yvo⟩
    simp only [link_vardef] at h
    split at h <;> rename_i hinfo
    · contradiction
    · split at h <;> rename_i hinit
      · contradiction
      · split at h <;> rename_i hflags
        · cases h
          rcases hflags with ⟨rfl, rfl⟩
          rcases LV.link_linkorder _ _ _ hinfo with ⟨hx, hy⟩
          rcases initializerLinker.link_linkorder _ _ _ hinit with ⟨hix, hiy⟩
          exact ⟨
            linkorder_vardef_intro _ _ _ _ _ _ hx hix,
            linkorder_vardef_intro _ _ _ _ _ _ hy hiy
          ⟩
        · contradiction

instance Linker_unit : Linker Unit where
  link := fun _ _ => some ()
  linkorder := fun _ _ => True
  linkorder_refl := by simp
  linkorder_trans := by simp
  link_linkorder := by simp

def link_def {F V : Type} [LF : Linker F] [LV : Linker V]
    (gd1 gd2 : globdef F V) : Option (globdef F V) :=
  match gd1, gd2 with
  | .Gfun f1, .Gfun f2 =>
      match LF.link f1 f2 with
      | some f => some (.Gfun f)
      | none => none
  | .Gvar v1, .Gvar v2 =>
      match link_vardef v1 v2 with
      | some v => some (.Gvar v)
      | none => none
  | _, _ => none

inductive linkorder_def {F V : Type} [LF : Linker F] [LV : Linker V] :
    globdef F V → globdef F V → Prop where
  | linkorder_def_fun (fd1 fd2 : F) :
      linkorder fd1 fd2 →
      linkorder_def (.Gfun fd1) (.Gfun fd2)
  | linkorder_def_var (v1 v2 : globvar V) :
      linkorder v1 v2 →
      linkorder_def (.Gvar v1) (.Gvar v2)

export linkorder_def (linkorder_def_fun linkorder_def_var)

instance Linker_def (F V : Type) [LF : Linker F] [LV : Linker V] :
    Linker (globdef F V) where
  link := link_def
  linkorder := linkorder_def
  linkorder_refl := by
    intro gd
    cases gd with
    | Gfun f => exact linkorder_def_fun _ _ (LF.linkorder_refl f)
    | Gvar v => exact linkorder_def_var _ _ ((Linker_vardef V).linkorder_refl v)
  linkorder_trans := by
    intro x y z hxy hyz
    cases hxy with
    | linkorder_def_fun x y hxy =>
        cases hyz with
        | linkorder_def_fun _ z hyz =>
            exact linkorder_def_fun _ _ (LF.linkorder_trans _ _ _ hxy hyz)
    | linkorder_def_var x y hxy =>
        cases hyz with
        | linkorder_def_var _ z hyz =>
            exact linkorder_def_var _ _ ((Linker_vardef V).linkorder_trans _ _ _ hxy hyz)
  link_linkorder := by
    intro x y z h
    cases x with
    | Gfun f1 =>
        cases y with
        | Gfun f2 =>
            cases hf : LF.link f1 f2 with
            | none => simp [link_def, hf] at h
            | some f =>
                simp [link_def, hf] at h
                subst z
                rcases LF.link_linkorder _ _ _ hf with ⟨hx, hy⟩
                exact ⟨linkorder_def_fun _ _ hx, linkorder_def_fun _ _ hy⟩
        | Gvar _ => simp [link_def] at h
    | Gvar v1 =>
        cases y with
        | Gfun _ => simp [link_def] at h
        | Gvar v2 =>
            cases hv : link_vardef v1 v2 with
            | none => simp [link_def, hv] at h
            | some v =>
                simp [link_def, hv] at h
                subst z
                rcases (Linker_vardef V).link_linkorder _ _ _ hv with ⟨hx, hy⟩
                exact ⟨linkorder_def_var _ _ hx, linkorder_def_var _ _ hy⟩

/-! ## Linking compilation units -/

private def ptreeForall {A : Type} (m : CompCert4Lean.Lib.Maps.PTree.t A)
    (pred : ident → A → Bool) : Bool :=
  (CompCert4Lean.Lib.Maps.PTree.elements m).all (fun entry => pred entry.1 entry.2)

def link_prog_check {F V : Type} [LF : Linker F] [LV : Linker V]
    (p1 p2 : program F V) (x : ident) (gd1 : globdef F V) : Bool :=
  match CompCert4Lean.Lib.Maps.PTree.get x (prog_defmap p2) with
  | none => true
  | some gd2 =>
      match in_dec peq x p1.prog_public with
      | .right _ => false
      | .left _ =>
          match in_dec peq x p2.prog_public with
          | .right _ => false
          | .left _ => (link_def gd1 gd2).isSome

def link_prog_merge {F V : Type} [LF : Linker F] [LV : Linker V]
    (o1 o2 : Option (globdef F V)) : Option (globdef F V) :=
  match o1, o2 with
  | none, _ => o2
  | _, none => o1
  | some gd1, some gd2 => link_def gd1 gd2

def link_prog {F V : Type} [LF : Linker F] [LV : Linker V]
    (p1 p2 : program F V) : Option (program F V) :=
  match ident_eq p1.prog_main p2.prog_main with
  | .right _ => none
  | .left _ =>
      if ptreeForall (prog_defmap p1) (link_prog_check p1 p2) then
        some
          { prog_main := p1.prog_main
            prog_public := p1.prog_public ++ p2.prog_public
            prog_defs :=
              CompCert4Lean.Lib.Maps.PTree.elements
                (CompCert4Lean.Lib.Maps.PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)) }
      else
        none

def link_prog_invStatement : Prop :=
  ∀ {F V : Type} [LF : Linker F] [LV : Linker V]
    (p1 p2 p : program F V),
    link_prog p1 p2 = some p →
      p1.prog_main = p2.prog_main ∧
      (∀ id gd1 gd2,
        CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p1) = some gd1 →
        CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p2) = some gd2 →
        id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧
          ∃ gd, link_def gd1 gd2 = some gd) ∧
      p =
        { prog_main := p1.prog_main
          prog_public := p1.prog_public ++ p2.prog_public
          prog_defs :=
            CompCert4Lean.Lib.Maps.PTree.elements
              (CompCert4Lean.Lib.Maps.PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)) }

def prog_defmap_elementsStatement : Prop :=
  ∀ {F V : Type} (m : CompCert4Lean.Lib.Maps.PTree.t (globdef F V)) (pub : List ident)
    (mn x : ident),
    CompCert4Lean.Lib.Maps.PTree.get x
      (prog_defmap { prog_defs := CompCert4Lean.Lib.Maps.PTree.elements m, prog_public := pub, prog_main := mn }) =
        CompCert4Lean.Lib.Maps.PTree.get x m

instance Linker_prog (F V : Type) [LF : Linker F] [LV : Linker V] :
    Linker (program F V) where
  link := link_prog
  linkorder := LinkClosure link_prog
  linkorder_refl := LinkClosure.refl
  linkorder_trans := by
    intro x y z hxy hyz
    exact LinkClosure.trans hxy hyz
  link_linkorder := by
    intro x y z h
    exact ⟨LinkClosure.left h, LinkClosure.right h⟩

def prog_defmap_linkorderStatement : Prop :=
  ∀ {F V : Type} [LF : Linker F] [LV : Linker V]
    (p1 p2 : program F V) (id : ident) (gd1 : globdef F V),
    linkorder p1 p2 →
    CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p1) = some gd1 →
    ∃ gd2, CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p2) = some gd2 ∧ linkorder gd1 gd2

/-! ## Matching between programs -/

private def matchGlobvar {V1 V2 : Type} (match_varinfo : V1 → V2 → Prop)
    (v1 : globvar V1) (v2 : globvar V2) : Prop :=
  match_varinfo v1.gvar_info v2.gvar_info ∧
    v1.gvar_init = v2.gvar_init ∧
    v1.gvar_readonly = v2.gvar_readonly ∧
    v1.gvar_volatile = v2.gvar_volatile

inductive match_globdef {C F1 V1 F2 V2 : Type} [LC : Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) : globdef F1 V1 → globdef F2 V2 → Prop where
  | match_globdef_fun (ctx' : C) (f1 : F1) (f2 : F2) :
      LC.linkorder ctx' ctx →
      match_fundef ctx' f1 f2 →
      match_globdef match_fundef match_varinfo ctx (.Gfun f1) (.Gfun f2)
  | match_globdef_var (v1 : globvar V1) (v2 : globvar V2) :
      matchGlobvar match_varinfo v1 v2 →
      match_globdef match_fundef match_varinfo ctx (.Gvar v1) (.Gvar v2)

export match_globdef (match_globdef_fun match_globdef_var)

def match_ident_globdef {C F1 V1 F2 V2 : Type} [LC : Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (ig1 : ident × globdef F1 V1)
    (ig2 : ident × globdef F2 V2) : Prop :=
  ig1.1 = ig2.1 ∧ match_globdef match_fundef match_varinfo ctx ig1.2 ig2.2

def match_program_gen {C F1 V1 F2 V2 : Type} [LC : Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p1 : program F1 V1) (p2 : program F2 V2) : Prop :=
  list_forall2 (match_ident_globdef match_fundef match_varinfo ctx)
      p1.prog_defs p2.prog_defs ∧
    p2.prog_main = p1.prog_main ∧
    p2.prog_public = p1.prog_public

def match_program_defmapStatement : Prop :=
  ∀ {C F1 V1 F2 V2 : Type} [LC : Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p1 : program F1 V1) (p2 : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p1 p2 →
    ∀ id,
      option_rel (match_globdef match_fundef match_varinfo ctx)
        (CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p1)) (CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p2))

def match_program {F1 V1 F2 V2 : Type} [LF : Linker F1] [LV : Linker V1]
    (match_fundef : program F1 V1 → F1 → F2 → Prop)
    (match_varinfo : V1 → V2 → Prop)
    (p1 : program F1 V1) (p2 : program F2 V2) : Prop :=
  match_program_gen match_fundef match_varinfo p1 p1 p2

def match_program_mainStatement : Prop :=
  ∀ {F1 V1 F2 V2 : Type} [LF : Linker F1] [LV : Linker V1]
    {match_fundef : program F1 V1 → F1 → F2 → Prop}
    {match_varinfo : V1 → V2 → Prop}
    {p1 : program F1 V1} {p2 : program F2 V2},
    match_program match_fundef match_varinfo p1 p2 → p2.prog_main = p1.prog_main

def match_transform_partial_program2Statement : Prop :=
  ∀ {C F1 V1 F2 V2 : Type} [LC : Linker C] [LF : Linker F1] [LV : Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (transf_fun : ident → F1 → Res F2) (transf_var : ident → V1 → Res V2)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    transform_partial_program2 transf_fun transf_var p = .OK tp →
    (∀ i f tf, transf_fun i f = .OK tf → match_fundef ctx f tf) →
    (∀ i v tv, transf_var i v = .OK tv → match_varinfo v tv) →
    match_program_gen match_fundef match_varinfo ctx p tp

def match_transform_partial_program_contextualStatement : Prop :=
  ∀ {A B V : Type} [LA : Linker A] [LV : Linker V]
    (match_fundef : program A V → A → B → Prop)
    (transf_fun : A → Res B) (p : program A V) (tp : program B V),
    transform_partial_program transf_fun p = .OK tp →
    (∀ f tf, transf_fun f = .OK tf → match_fundef p f tf) →
    match_program match_fundef Eq p tp

def match_transform_program_contextualStatement : Prop :=
  ∀ {A B V : Type} [LA : Linker A] [LV : Linker V]
    (match_fundef : program A V → A → B → Prop)
    (transf_fun : A → B) (p : program A V),
    (∀ f, match_fundef p f (transf_fun f)) →
    match_program match_fundef Eq p (transform_program transf_fun p)

def match_transform_partial_programStatement : Prop :=
  ∀ {A B V : Type} [LA : Linker A] [LV : Linker V]
    (transf_fun : A → Res B) (p : program A V) (tp : program B V),
    transform_partial_program transf_fun p = .OK tp →
    match_program (fun _ f tf => transf_fun f = .OK tf) Eq p tp

def match_transform_programStatement : Prop :=
  ∀ {A B V : Type} [LA : Linker A] [LV : Linker V]
    (transf : A → B) (p : program A V),
    match_program (fun _ f tf => tf = transf f) Eq p (transform_program transf p)

/-! ## Linking-compatible transformations and pass composition -/

class TransfLink {A B : Type} [LA : Linker A] [LB : Linker B]
    (transf : A → B → Prop) : Prop where
  transf_link :
    ∀ (p1 p2 : A) (tp1 tp2 : B) (p : A),
      LA.link p1 p2 = some p →
      transf p1 tp1 → transf p2 tp2 →
      ∃ tp, LB.link tp1 tp2 = some tp ∧ transf p tp

export TransfLink (transf_link)

structure Language where
  lang_prog : Type
  lang_link : Linker lang_prog

export Language (lang_prog lang_link)

structure Pass (S T : Language) where
  pass_match : S.lang_prog → T.lang_prog → Prop
  pass_match_link :
    @TransfLink S.lang_prog T.lang_prog S.lang_link T.lang_link pass_match

export Pass (pass_match pass_match_link)

def pass_identity (l : Language) : Pass l l where
  pass_match := Eq
  pass_match_link := @TransfLink.mk l.lang_prog l.lang_prog l.lang_link l.lang_link Eq (by
      intro p1 p2 tp1 tp2 p h hp1 hp2
      subst tp1
      subst tp2
      exact ⟨p, h, rfl⟩
    )

def pass_compose {l1 l2 l3 : Language} (pass : Pass l1 l2) (pass' : Pass l2 l3) :
    Pass l1 l3 where
  pass_match := fun p1 p3 => ∃ p2, pass.pass_match p1 p2 ∧ pass'.pass_match p2 p3
  pass_match_link := @TransfLink.mk l1.lang_prog l3.lang_prog l1.lang_link l3.lang_link
    (fun p1 p3 => ∃ p2, pass.pass_match p1 p2 ∧ pass'.pass_match p2 p3) (by
      intro p1 p2 tp1 tp2 p h h1 h2
      rcases h1 with ⟨ip1, hp1, htp1⟩
      rcases h2 with ⟨ip2, hp2, htp2⟩
      rcases pass.pass_match_link.transf_link p1 p2 ip1 ip2 p h hp1 hp2 with
        ⟨ip, hip, hmip⟩
      rcases pass'.pass_match_link.transf_link ip1 ip2 tp1 tp2 ip hip htp1 htp2 with
        ⟨tp, htp, hmtp⟩
      exact ⟨tp, htp, ip, hmip, hmtp⟩
    )

inductive Passes : Language → Language → Type 1 where
  | pass_nil (l : Language) : Passes l l
  | pass_cons {l1 l2 l3 : Language} (head : Pass l1 l2) (tail : Passes l2 l3) :
      Passes l1 l3

export Passes (pass_nil pass_cons)

def compose_passes : (l l' : Language) → Passes l l' → Pass l l'
  | _, _, .pass_nil l => pass_identity l
  | _, _, .pass_cons head tail => pass_compose head (compose_passes _ _ tail)

end CompCert4Lean.Common.Linking
