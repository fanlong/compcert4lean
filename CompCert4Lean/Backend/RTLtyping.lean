import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.Unityping

/-!
# RTL type checking

Definition-bearing translation of CompCert's `backend/RTLtyping.v`.
Proofs assigned to later migration are represented by exact proposition
descriptors.

The integrated calling-convention API carries the immutable compiler
configuration explicitly, so it is threaded through the typing judgments and
the inference functions that check tail calls.
-/

namespace CompCert4Lean.Backend.RTLtyping

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def rocqStringOfBytes : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (rocqStringOfBytes rest)

private def badSuccessorText : RocqString :=
  rocqStringOfBytes [98, 97, 100, 32, 115, 117, 99, 99, 101, 115, 115, 111, 114, 32]

private def unexpectedTypeText : RocqString :=
  rocqStringOfBytes [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101]

private def builtinArityMismatchText : RocqString :=
  rocqStringOfBytes
    [98, 117, 105, 108, 116, 105, 110, 32, 97, 114, 105, 116, 121, 32, 109,
      105, 115, 109, 97, 116, 99, 104]

private def illFormedMoveText : RocqString :=
  rocqStringOfBytes
    [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 109, 111, 118, 101]

private def tailcallNotPossibleText : RocqString :=
  rocqStringOfBytes
    [116, 97, 105, 108, 99, 97, 108, 108, 32, 110, 111, 116, 32, 112, 111,
      115, 115, 105, 98, 108, 101]

private def badTailcallReturnText : RocqString :=
  rocqStringOfBytes
    [98, 97, 100, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101,
      32, 105, 110, 32, 116, 97, 105, 108, 99, 97, 108, 108]

private def jumptableTooBigText : RocqString :=
  rocqStringOfBytes
    [106, 117, 109, 112, 116, 97, 98, 108, 101, 32, 116, 111, 111, 32, 98,
      105, 103]

private def badReturnText : RocqString :=
  rocqStringOfBytes [98, 97, 100, 32, 114, 101, 116, 117, 114, 110]

private def atPCText : RocqString :=
  rocqStringOfBytes [65, 116, 32, 80, 67, 32]

private def colonSpaceText : RocqString :=
  rocqStringOfBytes [58, 32]

private def duplicateParametersText : RocqString :=
  rocqStringOfBytes
    [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 112, 97, 114, 97, 109,
      101, 116, 101, 114, 115]

private def typEq (x y : typ) : Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

namespace RTLtypes

abbrev t : Type := typ
def eq (x y : t) : Sumbool (x = y) (x ≠ y) := typEq x y
def default : t := Tint

def algebra : TYPE_ALGEBRA where
  t := t
  eq := eq
  default := default

end RTLtypes

private abbrev rtlTypeAlgebra : TYPE_ALGEBRA := RTLtypes.algebra

/-! Canonical generated surface for `Unityping.UniSolver(RTLtypes)`.  Only
the generated members consumed by the frozen RTLtyping source are promoted;
unreferenced generic recursion helpers remain deferred under DMC-006. -/
namespace S

abbrev typenv : Type :=
  CompCert4Lean.Common.Unityping.UniSolver.typenv rtlTypeAlgebra
abbrev typassign : Type :=
  CompCert4Lean.Common.Unityping.UniSolver.typassign rtlTypeAlgebra

def initial : typenv :=
  CompCert4Lean.Common.Unityping.UniSolver.initial rtlTypeAlgebra

def set (e : typenv) (x : positive) (ty : RTLtypes.t) : res typenv :=
  CompCert4Lean.Common.Unityping.UniSolver.set rtlTypeAlgebra e x ty

def set_list (e : typenv) (xs : List positive)
    (tys : List RTLtypes.t) : res typenv :=
  CompCert4Lean.Common.Unityping.UniSolver.set_list rtlTypeAlgebra e xs tys

def move (e : typenv) (r1 r2 : positive) : res (Bool × typenv) :=
  CompCert4Lean.Common.Unityping.UniSolver.move rtlTypeAlgebra e r1 r2

def solve (e : typenv) : res typassign :=
  CompCert4Lean.Common.Unityping.UniSolver.solve rtlTypeAlgebra e

def satisf (te : typassign) (e : typenv) : Prop :=
  CompCert4Lean.Common.Unityping.UniSolver.satisf rtlTypeAlgebra te e

def satisf_initial : Prop := ∀ te : typassign, satisf te initial

def set_sound : Prop :=
  ∀ (te : typassign) (x : positive) (ty : RTLtypes.t) (e e' : typenv),
    set e x ty = OK e' → satisf te e' → te x = ty

def set_complete : Prop :=
  ∀ (te : typassign) (e : typenv) (x : positive) (ty : RTLtypes.t),
    satisf te e → te x = ty →
      ∃ e', set e x ty = OK e' ∧ satisf te e'

def set_list_sound : Prop :=
  ∀ (te : typassign) (xs : List positive) (tys : List RTLtypes.t)
    (e e' : typenv), set_list e xs tys = OK e' →
    satisf te e' → List.map te xs = tys

def set_list_complete : Prop :=
  ∀ (te : typassign) (xs : List positive) (tys : List RTLtypes.t) (e : typenv),
    satisf te e → List.map te xs = tys →
      ∃ e', set_list e xs tys = OK e' ∧ satisf te e'

def move_sound : Prop :=
  ∀ (te : typassign) (e : typenv) (r1 r2 : positive)
    (e' : typenv) (changed : Bool), move e r1 r2 = OK (changed, e') →
    satisf te e' → te r1 = te r2

def move_complete : Prop :=
  ∀ (te : typassign) (e : typenv) (r1 r2 : positive),
    satisf te e → te r1 = te r2 →
      ∃ changed e', move e r1 r2 = OK (changed, e') ∧ satisf te e'

def solve_sound : Prop :=
  ∀ (e : typenv) (te : typassign), solve e = OK te → satisf te e

def solve_complete : Prop :=
  ∀ (te : typassign) (e : typenv), satisf te e →
    ∃ te', solve e = OK te'

end S

private abbrev InferEnv := S.typenv
private abbrev TypeAssign := S.typassign

/-! ## Typing judgments -/

def regenv : Type := reg → typ

def valid_successor (f : function) (s : node) : Prop :=
  ∃ i, PTree.get s f.fn_code = some i

def type_of_builtin_arg (env : regenv) : builtin_arg reg → typ
  | .BA r => env r
  | .BA_int _ => Tint
  | .BA_long _ => Tlong
  | .BA_float _ => Tfloat
  | .BA_single _ => Tsingle
  | .BA_loadstack chunk _ => type_of_chunk chunk
  | .BA_addrstack _ => Tptr
  | .BA_loadglobal chunk _ _ => type_of_chunk chunk
  | .BA_addrglobal _ _ => Tptr
  | .BA_splitlong _ _ => Tlong
  | .BA_addptr _ _ => Tptr

def type_of_builtin_res (env : regenv) : builtin_res reg → typ
  | .BR r => env r
  | _ => Tint

inductive wt_instr (cfg : CompilerConfig) (f : function) (env : regenv) :
    instruction → Prop where
  | wt_Inop (s : node)
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Inop s)
  | wt_Iopmove (r1 r : reg) (s : node)
      (hty : env r = env r1)
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Iop Omove [r1] r s)
  | wt_Iop (op : operation) (args : List reg) (res : reg) (s : node)
      (hop : op ≠ Omove)
      (hargs : List.map env args = (type_of_operation op).1)
      (hres : env res = (type_of_operation op).2)
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Iop op args res s)
  | wt_Iload (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (dst : reg) (s : node)
      (hargs : List.map env args = type_of_addressing addr)
      (hdst : env dst = type_of_chunk chunk)
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Iload chunk addr args dst s)
  | wt_Istore (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (src : reg) (s : node)
      (hargs : List.map env args = type_of_addressing addr)
      (hsrc : env src = type_of_chunk chunk)
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Istore chunk addr args src s)
  | wt_Icall (sg : signature) (ros : Sum reg ident) (args : List reg)
      (res : reg) (s : node)
      (hros : match ros with
        | .inl r => env r = Tptr
        | .inr _ => True)
      (hargs : List.map env args = proj_sig_args sg)
      (hres : env res = proj_sig_res sg)
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Icall sg ros args res s)
  | wt_Itailcall (sg : signature) (ros : Sum reg ident) (args : List reg)
      (hros : match ros with
        | .inl r => env r = Tptr
        | .inr _ => True)
      (hargs : List.map env args = proj_sig_args sg)
      (hres : sg.sig_res = f.fn_sig.sig_res)
      (hpossible : tailcall_possible cfg sg) :
      wt_instr cfg f env (Itailcall sg ros args)
  | wt_Ibuiltin (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (s : node)
      (hargs : match ef with
        | .EF_annot _ _ _ | .EF_debug _ _ _ => True
        | _ => List.map (type_of_builtin_arg env) args = proj_sig_args (ef_sig ef))
      (hres : type_of_builtin_res env res = proj_sig_res (ef_sig ef))
      (hsucc : valid_successor f s) :
      wt_instr cfg f env (Ibuiltin ef args res s)
  | wt_Icond (cond : condition) (args : List reg) (s1 s2 : node)
      (hargs : List.map env args = type_of_condition cond)
      (hsucc1 : valid_successor f s1)
      (hsucc2 : valid_successor f s2) :
      wt_instr cfg f env (Icond cond args s1 s2)
  | wt_Ijumptable (arg : reg) (tbl : List node)
      (harg : env arg = Tint)
      (hsucc : ∀ s, s ∈ tbl → valid_successor f s)
      (hsize : ZArith.BinInt.Z.le
        (ZArith.BinInt.Z.mul (list_length_z tbl) (ZArith.BinInt.Z.of_nat 4))
        Int.max_unsigned) :
      wt_instr cfg f env (Ijumptable arg tbl)
  | wt_Ireturn_none
      (hres : f.fn_sig.sig_res = Xvoid) :
      wt_instr cfg f env (Ireturn none)
  | wt_Ireturn_some (arg : reg) (ty : typ)
      (hres : f.fn_sig.sig_res ≠ Xvoid)
      (harg : env arg = proj_sig_res f.fn_sig)
      (hty : env arg = ty) :
      wt_instr cfg f env (Ireturn (some arg))

export wt_instr
  (wt_Inop wt_Iopmove wt_Iop wt_Iload wt_Istore wt_Icall wt_Itailcall
   wt_Ibuiltin wt_Icond wt_Ijumptable wt_Ireturn_none wt_Ireturn_some)

structure wt_function (cfg : CompilerConfig) (f : function) (env : regenv) : Prop where
  mk_wt_function ::
  wt_params : List.map env f.fn_params = proj_sig_args f.fn_sig
  wt_norepet : list_norepet f.fn_params
  wt_instrs :
    ∀ pc instr, PTree.get pc f.fn_code = some instr → wt_instr cfg f env instr
  wt_entrypoint : valid_successor f f.fn_entrypoint

export wt_function (mk_wt_function wt_params wt_norepet wt_instrs wt_entrypoint)

inductive wt_fundef (cfg : CompilerConfig) : fundef → Prop where
  | wt_fundef_external (ef : external_function) :
      wt_fundef cfg (.External ef)
  | wt_function_internal (f : function) (env : regenv)
      (hwt : wt_function cfg f env) :
      wt_fundef cfg (.Internal f)

export wt_fundef (wt_fundef_external wt_function_internal)

def wt_program (cfg : CompilerConfig) (p : program) : Prop :=
  ∀ i fd, (i, Gfun fd) ∈ p.prog_defs → wt_fundef cfg fd

/-! ## Type inference -/

def check_successor (f : function) (s : node) : res Unit :=
  match PTree.get s f.fn_code with
  | none => Error (MSG badSuccessorText :: POS s :: [])
  | some _ => OK ()

def check_successors (f : function) : List node → res Unit
  | [] => OK ()
  | s :: rest =>
      match check_successor f s with
      | Error message => Error message
      | OK _ => check_successors f rest

def type_ros (e : InferEnv) : Sum reg ident → res InferEnv
  | .inl r => S.set e r Tptr
  | .inr _ => OK e

def is_move : operation → Bool
  | .Omove => true
  | _ => false

def type_expect (e : InferEnv) (t1 t2 : typ) : res InferEnv :=
  match typEq t1 t2 with
  | .left _ => OK e
  | .right _ => Error (msg unexpectedTypeText)

def type_builtin_arg (e : InferEnv) (a : builtin_arg reg) (ty : typ) :
    res InferEnv :=
  match a with
  | .BA r => S.set e r ty
  | .BA_int _ => type_expect e ty Tint
  | .BA_long _ => type_expect e ty Tlong
  | .BA_float _ => type_expect e ty Tfloat
  | .BA_single _ => type_expect e ty Tsingle
  | .BA_loadstack chunk _ => type_expect e ty (type_of_chunk chunk)
  | .BA_addrstack _ => type_expect e ty Tptr
  | .BA_loadglobal chunk _ _ => type_expect e ty (type_of_chunk chunk)
  | .BA_addrglobal _ _ => type_expect e ty Tptr
  | .BA_splitlong _ _ => type_expect e ty Tlong
  | .BA_addptr _ _ => type_expect e ty Tptr

def type_builtin_args : InferEnv → List (builtin_arg reg) → List typ → res InferEnv
  | e, [], [] => OK e
  | e, a :: args, ty :: tys =>
      match type_builtin_arg e a ty with
      | Error message => Error message
      | OK e1 => type_builtin_args e1 args tys
  | _, _, _ => Error (msg builtinArityMismatchText)

def type_builtin_res (e : InferEnv) (a : builtin_res reg) (ty : typ) :
    res InferEnv :=
  match a with
  | .BR r => S.set e r ty
  | _ => type_expect e ty Tint

def type_instr (cfg : CompilerConfig) (f : function) (e : InferEnv) :
    instruction → res InferEnv
  | .Inop s =>
      match check_successor f s with
      | Error message => Error message
      | OK _ => OK e
  | .Iop op args res s =>
      match check_successor f s with
      | Error message => Error message
      | OK _ =>
          if is_move op then
            match args with
            | [arg] =>
                match S.move e res arg with
                | Error message => Error message
                | OK (_, e') => OK e'
            | _ => Error (msg illFormedMoveText)
          else
            let (targs, tres) := type_of_operation op
            match S.set_list e args targs with
            | Error message => Error message
            | OK e1 => S.set e1 res tres
  | .Iload chunk addr args dst s =>
      match check_successor f s with
      | Error message => Error message
      | OK _ =>
          match S.set_list e args (type_of_addressing addr) with
          | Error message => Error message
          | OK e1 => S.set e1 dst (type_of_chunk chunk)
  | .Istore chunk addr args src s =>
      match check_successor f s with
      | Error message => Error message
      | OK _ =>
          match S.set_list e args (type_of_addressing addr) with
          | Error message => Error message
          | OK e1 => S.set e1 src (type_of_chunk chunk)
  | .Icall sg ros args res s =>
      match check_successor f s with
      | Error message => Error message
      | OK _ =>
          match type_ros e ros with
          | Error message => Error message
          | OK e1 =>
              match S.set_list e1 args (proj_sig_args sg) with
              | Error message => Error message
              | OK e2 => S.set e2 res (proj_sig_res sg)
  | .Itailcall sg ros args =>
      match type_ros e ros with
      | Error message => Error message
      | OK e1 =>
          match S.set_list e1 args (proj_sig_args sg) with
          | Error message => Error message
          | OK e2 =>
              if sg.sig_res = f.fn_sig.sig_res then
                if tailcall_is_possible cfg sg then OK e2
                else Error (msg tailcallNotPossibleText)
              else Error (msg badTailcallReturnText)
  | .Ibuiltin ef args res s =>
      let sg := ef_sig ef
      match check_successor f s with
      | Error message => Error message
      | OK _ =>
          match (match ef with
            | .EF_annot _ _ _ | .EF_debug _ _ _ => OK e
            | _ => type_builtin_args e args (proj_sig_args sg)) with
          | Error message => Error message
          | OK e1 => type_builtin_res e1 res (proj_sig_res sg)
  | .Icond cond args s1 s2 =>
      match check_successor f s1 with
      | Error message => Error message
      | OK _ =>
          match check_successor f s2 with
          | Error message => Error message
          | OK _ => S.set_list e args (type_of_condition cond)
  | .Ijumptable arg tbl =>
      match check_successors f tbl with
      | Error message => Error message
      | OK _ =>
          match S.set e arg Tint with
          | Error message => Error message
          | OK e1 =>
              match zle
                  (ZArith.BinInt.Z.mul
                    (list_length_z tbl) (ZArith.BinInt.Z.of_nat 4))
                  Int.max_unsigned with
              | .left _ => OK e1
              | .right _ => Error (msg jumptableTooBigText)
  | .Ireturn none =>
      if f.fn_sig.sig_res = Xvoid then OK e else Error (msg badReturnText)
  | .Ireturn (some r) =>
      if f.fn_sig.sig_res = Xvoid then Error (msg badReturnText)
      else S.set e r (proj_sig_res f.fn_sig)

def type_code (cfg : CompilerConfig) (f : function) (e : InferEnv) :
    res InferEnv :=
  PTree.fold
    (fun re pc instr =>
      match re with
      | Error _ => re
      | OK env =>
          match type_instr cfg f env instr with
          | Error message => Error (MSG atPCText :: POS pc :: MSG colonSpaceText :: message)
          | OK env' => OK env')
    f.fn_code (OK e)

def check_params_norepet (params : List reg) : res Unit :=
  match CompCert4Lean.Lib.Coqlib.list_norepet_dec Reg.eq params with
  | .left _ => OK ()
  | .right _ => Error (msg duplicateParametersText)

def type_function (cfg : CompilerConfig) (f : function) : res regenv :=
  match type_code cfg f (S.initial) with
  | Error message => Error message
  | OK e1 =>
      match S.set_list e1 f.fn_params (proj_sig_args f.fn_sig) with
      | Error message => Error message
      | OK e2 =>
          match S.solve e2 with
          | Error message => Error message
          | OK te =>
              match check_params_norepet f.fn_params with
              | Error message => Error message
              | OK _ =>
                  match check_successor f f.fn_entrypoint with
                  | Error message => Error message
                  | OK _ => OK te

/-! ## Exact statement descriptors for later inference proofs -/

def type_ros_soundStatement : Prop :=
  ∀ (e : InferEnv) (ros : Sum reg ident) (e' : InferEnv) (te : TypeAssign),
    type_ros e ros = OK e' →
      S.satisf te e' →
        match ros with
        | .inl r => te r = Tptr
        | .inr _ => True

def check_successors_soundStatement : Prop :=
  ∀ (f : function) (sl : List node) (x : Unit),
    check_successors f sl = OK x →
      ∀ s, s ∈ sl → valid_successor f s

def type_expect_soundStatement : Prop :=
  ∀ (e : InferEnv) (ty1 ty2 : typ) (e' : InferEnv),
    type_expect e ty1 ty2 = OK e' → ty1 = ty2

def type_builtin_arg_soundStatement : Prop :=
  ∀ (e : InferEnv) (a : builtin_arg reg) (ty : typ)
    (e' : InferEnv) (te : TypeAssign),
    type_builtin_arg e a ty = OK e' →
      S.satisf te e' →
        type_of_builtin_arg te a = ty

def type_builtin_args_soundStatement : Prop :=
  ∀ (al : List (builtin_arg reg)) (tyl : List typ)
    (e e' : InferEnv) (te : TypeAssign),
    type_builtin_args e al tyl = OK e' →
      S.satisf te e' →
        List.map (type_of_builtin_arg te) al = tyl

def type_builtin_res_soundStatement : Prop :=
  ∀ (e : InferEnv) (a : builtin_res reg) (ty : typ)
    (e' : InferEnv) (te : TypeAssign),
    type_builtin_res e a ty = OK e' →
      S.satisf te e' →
        type_of_builtin_res te a = ty

def type_instr_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (e : InferEnv) (i : instruction)
    (e' : InferEnv) (te : TypeAssign),
    type_instr cfg f e i = OK e' →
      S.satisf te e' →
        S.satisf te e

def type_instr_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (e : InferEnv) (i : instruction)
    (e' : InferEnv) (te : TypeAssign),
    type_instr cfg f e i = OK e' →
      S.satisf te e' → wt_instr cfg f te i

def type_code_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (pc : node) (i : instruction)
    (e e' : InferEnv) (te : TypeAssign),
    type_code cfg f e = OK e' →
      PTree.get pc f.fn_code = some i →
        S.satisf te e' → wt_instr cfg f te i

def type_function_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (env : regenv),
    type_function cfg f = OK env → wt_function cfg f env

/-! ## Type preservation invariants -/

def wt_regset (env : regenv) (rs : regset) : Prop :=
  ∀ r, Val.has_type (Regmap.get r rs) (env r)

def wt_regset_assignStatement : Prop :=
  ∀ (env : regenv) (rs : regset) (v : val) (r : reg),
    wt_regset env rs →
      Val.has_type v (env r) → wt_regset env (Regmap.set r v rs)

def wt_regset_listStatement : Prop :=
  ∀ (env : regenv) (rs : regset),
    wt_regset env rs →
      ∀ rl, Val.has_type_list
        (List.map (fun r => Regmap.get r rs) rl) (List.map env rl)

def wt_regset_setresStatement : Prop :=
  ∀ (env : regenv) (rs : regset) (v : val) (res : builtin_res reg),
    wt_regset env rs →
      Val.has_type v (type_of_builtin_res env res) →
        wt_regset env (regmap_setres res v rs)

def wt_init_regsStatement : Prop :=
  ∀ (env : regenv) (rl : List reg) (args : List val),
    Val.has_type_list args (List.map env rl) →
      wt_regset env (init_regs args rl)

def wt_exec_IopStatement
    [binary64_certificate :
      BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (ge : genv) (env : regenv) (f : function)
    (sp : val) (op : operation) (args : List reg) (res : reg) (s : node)
    (rs : regset) (m : mem) (v : val),
    wt_instr cfg f env (Iop op args res s) →
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp op (List.map (fun r => Regmap.get r rs) args) m = some v →
        wt_regset env rs → wt_regset env (Regmap.set res v rs)

def wt_exec_IloadStatement : Prop :=
  ∀ (cfg : CompilerConfig) (env : regenv) (f : function)
    (chunk : memory_chunk) (addr : addressing) (args : List reg)
    (dst : reg) (s : node) (m : mem) (a v : val) (rs : regset),
    wt_instr cfg f env (Iload chunk addr args dst s) →
      Mem.loadv chunk m a = some v →
        wt_regset env rs → wt_regset env (Regmap.set dst v rs)

def wt_exec_IbuiltinStatement
    [binary64_certificate :
      BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (env : regenv) (f : function)
    (ef : external_function) (ge : genv) (args : List (builtin_arg reg))
    (res : builtin_res reg) (s : node) (vargs : List val) (m : mem)
    (t : trace) (vres : val) (m' : mem) (rs : regset),
    wt_instr cfg f env (Ibuiltin ef args res s) →
      external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m' →
        wt_regset env rs → wt_regset env (regmap_setres res vres rs)

def wt_instr_atStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (env : regenv)
    (pc : node) (i : instruction),
    wt_function cfg f env →
      PTree.get pc f.fn_code = some i → wt_instr cfg f env i

inductive wt_stackframes (cfg : CompilerConfig) :
    List stackframe → signature → Prop where
  | wt_stackframes_nil (sg : signature)
      (hres : sg.sig_res = Xint) :
      wt_stackframes cfg [] sg
  | wt_stackframes_cons (s : List stackframe) (res : reg) (f : function)
      (sp : val) (pc : node) (rs : regset) (env : regenv) (sg : signature)
      (hfunction : wt_function cfg f env)
      (hregset : wt_regset env rs)
      (hres : env res = proj_sig_res sg)
      (hstack : wt_stackframes cfg s f.fn_sig) :
      wt_stackframes cfg (Stackframe res f sp pc rs :: s) sg

export wt_stackframes (wt_stackframes_nil wt_stackframes_cons)

inductive wt_state (cfg : CompilerConfig) : state → Prop where
  | wt_state_intro (s : List stackframe) (f : function) (sp : val)
      (pc : node) (rs : regset) (m : mem) (env : regenv)
      (WT_STK : wt_stackframes cfg s f.fn_sig)
      (WT_FN : wt_function cfg f env)
      (WT_RS : wt_regset env rs) :
      wt_state cfg (State s f sp pc rs m)
  | wt_state_call (s : List stackframe) (fd : fundef) (args : List val) (m : mem)
      (hstack : wt_stackframes cfg s (funsig fd))
      (hfunction : wt_fundef cfg fd)
      (hargs : Val.has_type_list args (proj_sig_args (funsig fd))) :
      wt_state cfg (Callstate s fd args m)
  | wt_state_return (s : List stackframe) (v : val) (m : mem) (sg : signature)
      (hstack : wt_stackframes cfg s sg)
      (hres : Val.has_type v (proj_sig_res sg)) :
      wt_state cfg (Returnstate s v m)

export wt_state (wt_state_intro wt_state_call wt_state_return)

def wt_stackframes_change_sigStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List stackframe) (sg1 sg2 : signature),
    sg1.sig_res = sg2.sig_res →
      wt_stackframes cfg s sg1 → wt_stackframes cfg s sg2

def subject_reductionStatement
    [binary64_certificate :
      BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p : program),
    wt_program cfg p →
      ∀ (st1 : state) (t : trace) (st2 : state),
        step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv p) st1 t st2 →
          wt_state cfg st1 → wt_state cfg st2

def wt_initial_stateStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p : program),
    wt_program cfg p → ∀ s, initial_state p s → wt_state cfg s

end CompCert4Lean.Backend.RTLtyping

namespace CompCert4Lean.Backend.RTLtyping.S

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Unityping.UniSolver
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Common.Errors

private theorem rtl_pget_set_same {A : Type}
    (i : positive) (v : A) (m : PTree.t A) :
    PTree.get i (PTree.set i v m) = some v := by
  have h := CompCert4Lean.Lib.Maps.PTree.gsspec_proof i i v m
  cases hpeq : peq i i with
  | left hEq => simpa [hpeq] using h
  | right hNe => exact False.elim (hNe rfl)

private theorem rtl_pget_set_other {A : Type}
    (i j : positive) (v : A) (m : PTree.t A) (hne : i ≠ j) :
    PTree.get i (PTree.set j v m) = PTree.get i m := by
  have h := CompCert4Lean.Lib.Maps.PTree.gsspec_proof i j v m
  cases hpeq : peq i j with
  | left hEq => exact False.elim (hne hEq)
  | right hNe => simpa [hpeq] using h

private theorem rtl_move_sound_aux : move_sound := by
  intro te e r1 r2 e' changed h hs
  unfold S.move CompCert4Lean.Common.Unityping.UniSolver.move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      cases h
      exact hEq ▸ rfl
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              apply hs.2 r1 r2
              change (r1, r2) ∈ (r1, r2) :: te_equ e
              exact List.mem_cons_self
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
              have hu1 := rtl_pget_set_same r1 ty2 (te_typ e)
              have hu2 := rtl_pget_set_other r2 r1 ty2 (te_typ e) hNe.symm
              have htr1 : te r1 = ty2 := hs.1 r1 ty2 (by
                change PTree.get r1 (PTree.set r1 ty2 (te_typ e)) = some ty2
                exact hu1)
              have htr2 : te r2 = ty2 := hs.1 r2 ty2 (by
                change PTree.get r2 (PTree.set r1 ty2 (te_typ e)) = some ty2
                exact hu2.trans h2)
              exact htr1.trans htr2.symm
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              have hu1 := rtl_pget_set_other r1 r2 ty1 (te_typ e) hNe
              have hu2 := rtl_pget_set_same r2 ty1 (te_typ e)
              have htr1 : te r1 = ty1 := hs.1 r1 ty1 (by
                change PTree.get r1 (PTree.set r2 ty1 (te_typ e)) = some ty1
                exact hu1.trans h1)
              have htr2 : te r2 = ty1 := hs.1 r2 ty1 (by
                change PTree.get r2 (PTree.set r2 ty1 (te_typ e)) = some ty1
                exact hu2)
              exact htr1.trans htr2.symm
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : rtlTypeAlgebra.eq ty1 ty2 with
              | left hty =>
                simp [hEq] at h
                have he' : e' = e := h.2.symm
                subst e'
                have htr1 := hs.1 r1 ty1 (by exact h1)
                have htr2 := hs.1 r2 ty2 (by exact h2)
                exact htr1.trans (hty.trans htr2.symm)
              | right hty =>
                simp [hEq] at h

end CompCert4Lean.Backend.RTLtyping.S

namespace CompCert4Lean.Backend.RTLtyping.S

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Unityping.UniSolver
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Common.Errors

private theorem rtl_move_incr_aux :
    ∀ (te : typassign) (e : typenv) (r1 r2 : positive)
      (e' : typenv) (changed : Bool),
      move e r1 r2 = OK (changed, e') → satisf te e' → satisf te e := by
  intro te e r1 r2 e' changed h hs
  unfold S.move CompCert4Lean.Common.Unityping.UniSolver.move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      exact hs
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                exact hs.1 x ty hx
              · intro x y hxy
                exact hs.2 x y (List.mem_cons_of_mem _ hxy)
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                by_cases hxr : x = r1
                · subst x
                  rw [h1] at hx
                  cases hx
                · exact hs.1 x ty (by
                    rw [rtl_pget_set_other x r1 ty2 (te_typ e) hxr]
                    exact hx)
              · intro x y hxy
                exact hs.2 x y hxy
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                by_cases hxr : x = r2
                · subst x
                  rw [h2] at hx
                  cases hx
                · exact hs.1 x ty (by
                    rw [rtl_pget_set_other x r2 ty1 (te_typ e) hxr]
                    exact hx)
              · intro x y hxy
                exact hs.2 x y hxy
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : rtlTypeAlgebra.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact hs
              | right hty =>
                  simp [hEq] at h

private theorem rtl_solve_rec_incr_aux :
    ∀ (te : typassign) (q : List (positive × positive))
      (e : typenv) (changed : Bool) (e' : typenv) (changed' : Bool),
      CompCert4Lean.Common.Unityping.UniSolver.solve_rec rtlTypeAlgebra
        e changed q = OK (e', changed') →
      satisf te e' → satisf te e := by
  intro te q
  induction q with
  | nil =>
      intro e changed e' changed' h hs
      simp [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      rcases h with ⟨rfl, rfl⟩
      exact hs
  | cons a q ih =>
      rcases a with ⟨r1, r2⟩
      intro e changed e' changed' h hs
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        exact rtl_move_incr_aux te e r1 r2 e1 changed1 hmove
          (ih e1 (changed || changed1) e' changed' h hs)

private theorem rtl_solve_rec_sound_aux :
    ∀ (te : typassign) (r1 r2 : positive)
      (q : List (positive × positive)) (e : typenv) (changed : Bool)
      (e' : typenv) (changed' : Bool),
      CompCert4Lean.Common.Unityping.UniSolver.solve_rec rtlTypeAlgebra
        e changed q = OK (e', changed') →
      (r1, r2) ∈ q → satisf te e' → te r1 = te r2 := by
  intro te r1 r2 q
  induction q generalizing r1 r2 with
  | nil =>
      intro e changed e' changed' h hmem hs
      cases hmem
  | cons a q ih =>
      rcases a with ⟨a1, a2⟩
      intro e changed e' changed' h hmem hs
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · injection hmem with hr1 hr2
          subst r1
          subst r2
          exact rtl_move_sound_aux te e a1 a2 e1 changed1 hmove
            (rtl_solve_rec_incr_aux te q e1 (changed || changed1) e' changed' h hs)
        · exact ih r1 r2 e1 (changed || changed1) e' changed' h hmem hs

private theorem rtl_move_false_aux :
    ∀ (e : typenv) (r1 r2 : positive) (e' : typenv),
      move e r1 r2 = OK (false, e') →
      te_typ e' = te_typ e ∧
        makeassign rtlTypeAlgebra e r1 = makeassign rtlTypeAlgebra e r2 := by
  intro e r1 r2 e' h
  unfold S.move CompCert4Lean.Common.Unityping.UniSolver.move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, hEq ▸ rfl⟩
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              rcases h with ⟨rfl, rfl⟩
              constructor
              · rfl
              · simp [CompCert4Lean.Common.Unityping.UniSolver.makeassign, h1, h2]
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : rtlTypeAlgebra.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  constructor
                  · rfl
                  · simp [CompCert4Lean.Common.Unityping.UniSolver.makeassign, h1, h2, hty]
              | right hty =>
                  simp [hEq] at h

private theorem rtl_solve_rec_false_aux :
    ∀ (r1 r2 : positive) (q : List (positive × positive))
      (e : typenv) (changed : Bool) (e' : typenv),
      CompCert4Lean.Common.Unityping.UniSolver.solve_rec rtlTypeAlgebra
        e changed q = OK (e', false) →
      changed = false ∧
        ((r1, r2) ∈ q →
          makeassign rtlTypeAlgebra e r1 = makeassign rtlTypeAlgebra e r2) := by
  intro r1 r2 q
  induction q with
  | nil =>
      intro e changed e' h
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      cases changed with
      | false =>
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, by intro hmem; cases hmem⟩
      | true =>
          cases h
  | cons a q ih =>
      rcases a with ⟨a1, a2⟩
      intro e changed e' h
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        have htail := ih e1 (changed || changed1) e' h
        rcases htail with ⟨hchanged, hmem⟩
        have hc : changed = false := by
          cases changed <;> cases changed1 <;> simp_all
        have hc1 : changed1 = false := by
          cases changed <;> cases changed1 <;> simp_all
        subst changed
        subst changed1
        have hmf := rtl_move_false_aux e a1 a2 e1 hmove
        constructor
        · rfl
        · intro hmem'
          simp only [List.mem_cons] at hmem'
          rcases hmem' with hhead | htailmem
          · rcases hhead with ⟨rfl, rfl⟩
            exact hmf.2
          · have hEq := hmem htailmem
            unfold CompCert4Lean.Common.Unityping.UniSolver.makeassign at hEq ⊢
            rw [hmf.1] at hEq
            exact hEq

private theorem rtl_solve_constraints_incr_aux :
    ∀ (te : typassign) (e e' : typenv),
      CompCert4Lean.Common.Unityping.UniSolver.solve_constraints rtlTypeAlgebra e =
        OK e' → satisf te e' → satisf te e := by
  intro te e e' h hs
  let P : typenv → res typenv → Prop := fun e r =>
    ∀ e', r = OK e' → satisf te e' → satisf te e
  have hind :=
    CompCert4Lean.Common.Unityping.UniSolver.solve_constraints_ind
      rtlTypeAlgebra P
      (by
        intro e e' hrec e'' heq hs'
        cases heq
        exact hs')
      (by
        intro e e' hrec ih e'' heq hs'
        have hsbase := ih e'' heq hs'
        have hsorig : satisf te e := by
          have hs0 := rtl_solve_rec_incr_aux te (te_equ e)
            { te_typ := te_typ e, te_equ := [] } false e' true hrec hsbase
          constructor
          · intro x ty hx
            exact hs0.1 x ty hx
          · intro x y hxy
            exact rtl_solve_rec_sound_aux te x y (te_equ e)
              { te_typ := te_typ e, te_equ := [] } false e' true hrec hxy hsbase
        exact hsorig)
      (by
        intro e message hrec e'' heq hs'
        cases heq)
      e
  exact hind e' h hs

private theorem rtl_solve_constraints_sound_aux :
    ∀ (e e' : typenv),
      CompCert4Lean.Common.Unityping.UniSolver.solve_constraints rtlTypeAlgebra e =
        OK e' →
      satisf (makeassign rtlTypeAlgebra e') e' := by
  intro e e' h
  let P : typenv → res typenv → Prop := fun _ r =>
    ∀ e', r = OK e' →
      satisf (makeassign rtlTypeAlgebra e') e'
  have hind :=
    CompCert4Lean.Common.Unityping.UniSolver.solve_constraints_ind
      rtlTypeAlgebra P
      (by
        intro e e' hrec e'' heq
        cases heq
        constructor
        · intro x ty hx
          simp [CompCert4Lean.Common.Unityping.UniSolver.makeassign, hx]
        · intro x y hxy
          have hf := rtl_solve_rec_false_aux x y (te_equ e)
            { te_typ := te_typ e, te_equ := [] } false e' hrec
          have heq' := hf.2 hxy
          simpa [CompCert4Lean.Common.Unityping.UniSolver.makeassign] using heq')
      (by
        intro e e' hrec ih e'' heq
        have hs := ih e'' heq
        exact hs)
      (by
        intro e message hrec e' heq
        cases heq)
      e
  exact hind e' h

theorem solve_sound_proof : solve_sound := by
  intro e te h
  unfold S.solve CompCert4Lean.Common.Unityping.UniSolver.solve at h
  split at h
  · cases h
  · rename_i e' hconstraints
    rcases h with ⟨rfl⟩
    exact rtl_solve_constraints_incr_aux (makeassign rtlTypeAlgebra e') e e'
      hconstraints (rtl_solve_constraints_sound_aux e e' hconstraints)

end CompCert4Lean.Backend.RTLtyping.S
