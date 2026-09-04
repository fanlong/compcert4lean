import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Cfrontend.Csem
import CompCert4Lean.Cfrontend.Cstrategy
import CompCert4Lean.Cfrontend.SimplExprspec

/-!
# Correctness surface for expression simplification

This module contains the executable definitions and exact proposition
descriptors selected from CompCert's `cfrontend/SimplExprproof.v`.  Proofs are
intentionally left to the later proof-migration phase; no theorem stubs are
introduced here.
-/

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev cprogram := CompCert4Lean.Cfrontend.Csyntax.program
private abbrev tprogram := CompCert4Lean.Cfrontend.Clight.program
private abbrev cfunction := CompCert4Lean.Cfrontend.Csyntax.function
private abbrev cexpr := CompCert4Lean.Cfrontend.Csyntax.expr
private abbrev cexprlist := CompCert4Lean.Cfrontend.Csyntax.exprlist
private abbrev cstatement := CompCert4Lean.Cfrontend.Csyntax.statement
private abbrev clabeled_statements :=
  CompCert4Lean.Cfrontend.Csyntax.labeled_statements
private abbrev cfundef := CompCert4Lean.Cfrontend.Csyntax.fundef
private abbrev tfundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev tfunction := CompCert4Lean.Cfrontend.Clight.function
private abbrev cgenv := CompCert4Lean.Cfrontend.Csem.genv
private abbrev tgenv := CompCert4Lean.Cfrontend.Clight.genv
private abbrev cstate := CompCert4Lean.Cfrontend.Csem.state
private abbrev tstate := CompCert4Lean.Cfrontend.Clight.machine_state
private abbrev ccont := CompCert4Lean.Cfrontend.Csem.cont
private abbrev tcont := CompCert4Lean.Cfrontend.Clight.cont
private abbrev cenv := CompCert4Lean.Cfrontend.Csem.env
private abbrev tenv := CompCert4Lean.Cfrontend.Clight.env
private abbrev ttemp_env := CompCert4Lean.Cfrontend.Clight.temp_env
private abbrev ctype := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev trace := CompCert4Lean.Common.Events.trace
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev Included {A : Type} (xs ys : List A) : Prop :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl xs ys

def match_prog
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) (tp : tprogram) : Prop :=
  (list_forall2
      (fun idg tidg =>
        idg.1 = tidg.1 ∧
          match idg.2, tidg.2 with
          | .Gfun f, .Gfun tf =>
              ∃ cu, Ctypes.linkorder_program cu p ∧
                @tr_fundef binary64_certificate binary32_certificate cu f tf
          | .Gvar v, .Gvar tv =>
              v.gvar_info = tv.gvar_info ∧
                v.gvar_init = tv.gvar_init ∧
                v.gvar_readonly = tv.gvar_readonly ∧
                v.gvar_volatile = tv.gvar_volatile
          | _, _ => False)
      (Ctypes.program_of_program p).prog_defs
      (Ctypes.program_of_program tp).prog_defs ∧
    (Ctypes.program_of_program tp).prog_main =
      (Ctypes.program_of_program p).prog_main ∧
    (Ctypes.program_of_program tp).prog_public =
      (Ctypes.program_of_program p).prog_public) ∧
    tp.prog_types = p.prog_types

def Kseqlist : List Clight.statement → Clight.cont → Clight.cont
  | [], k => k
  | s :: rest, k => .Kseq s (Kseqlist rest k)

mutual
  def esize : cexpr → Nat
    | .Eloc _ _ _ _ => 1
    | .Evar _ _ => 1
    | .Ederef r _ => Nat.succ (esize r)
    | .Efield l _ _ => Nat.succ (esize l)
    | .Eval _ _ => 0
    | .Evalof l _ => Nat.succ (esize l)
    | .Eaddrof l _ => Nat.succ (esize l)
    | .Eunop _ r _ => Nat.succ (esize r)
    | .Ebinop _ r1 r2 _ => Nat.succ (esize r1 + esize r2)
    | .Ecast r _ => Nat.succ (esize r)
    | .Eseqand r _ _ => Nat.succ (esize r)
    | .Eseqor r _ _ => Nat.succ (esize r)
    | .Econdition r _ _ _ => Nat.succ (esize r)
    | .Esizeof _ _ => 1
    | .Ealignof _ _ => 1
    | .Eassign l r _ => Nat.succ (esize l + esize r)
    | .Eassignop _ l r _ _ => Nat.succ (esize l + esize r)
    | .Epostincr _ l _ => Nat.succ (esize l)
    | .Ecomma r1 r2 _ => Nat.succ (esize r1 + esize r2)
    | .Ecall r1 rl _ => Nat.succ (esize r1 + esizelist rl)
    | .Ebuiltin _ _ rl _ => Nat.succ (esizelist rl)
    | .Eparen r _ _ => Nat.succ (esize r)

  def esizelist : cexprlist → Nat
    | .Enil => 0
    | .Econs r rest => esize r + esizelist rest
end

def measure : cstate → Nat
  | .ExprState _ r _ _ _ => esize r + 1
  | .State _ .Sskip _ _ _ => 0
  | .State _ (.Sdo r) _ _ _ => esize r + 2
  | .State _ (.Sifthenelse r _ _) _ _ _ => esize r + 2
  | _ => 0

mutual
  inductive match_cont
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (prog : cprogram) (tprog : tprogram) :
      composite_env → ccont → tcont → Prop where
    | match_Kstop (ce : composite_env) :
        match_cont prog tprog ce .Kstop .Kstop
    | match_Kseq (ce : composite_env) (s : cstatement) (k : ccont)
        (ts : Clight.statement) (tk : tcont)
        (hstmt : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kseq s k) (.Kseq ts tk)
    | match_Kwhile2 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kwhile2 r s k)
          (.Kloop1 (.Ssequence s' ts) .Sskip tk)
    | match_Kdowhile1 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kdowhile1 r s k) (.Kloop1 ts s' tk)
    | match_Kfor3 (ce : composite_env) (r : cexpr) (s3 s : cstatement)
        (k : ccont) (ts3 s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs3 : tr_stmt ce s3 ts3)
        (hs : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kfor3 r s3 s k)
          (.Kloop1 (.Ssequence s' ts) ts3 tk)
    | match_Kfor4 (ce : composite_env) (r : cexpr) (s3 s : cstatement)
        (k : ccont) (ts3 s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs3 : tr_stmt ce s3 ts3)
        (hs : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kfor4 r s3 s k)
          (.Kloop2 (.Ssequence s' ts) ts3 tk)
    | match_Kswitch2 (ce : composite_env) (k : ccont) (tk : tcont)
        (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kswitch2 k) (.Kswitch tk)
    | match_Kcall (f : cfunction) (e : tenv) (C : cexpr → cexpr)
        (ty : ctype) (k : ccont) (optid : Option ident) (tf : tfunction)
        (le : ttemp_env) (sl : List Clight.statement) (tk : tcont)
        (a : Clight.expr) (dest : destination) (tmps : List ident)
        (cu : cprogram) (ce : composite_env)
        (hlink : Ctypes.linkorder_program cu prog)
        (htrf : tr_function cu.prog_comp_env f tf)
        (hctx : leftcontext .RV .RV C)
        (htr : ∀ v m, tr_top cu.prog_comp_env (Clight.globalenv tprog) e
          (Clight.set_opttemp optid v le) m dest
          (C (.Eval v ty)) sl a tmps)
        (hmc : match_cont_exp prog tprog cu.prog_comp_env dest a k tk) :
        match_cont prog tprog ce (.Kcall f e C ty k)
          (.Kcall optid tf e le (Kseqlist sl tk))

  inductive match_cont_exp
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (prog : cprogram) (tprog : tprogram) :
      composite_env → destination → Clight.expr → ccont → tcont → Prop where
    | match_Kdo (ce : composite_env) (k : ccont) (a : Clight.expr) (tk : tcont)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_effects a (.Kdo k) tk
    | match_Kifthenelse_empty (ce : composite_env) (a : Clight.expr)
        (k : ccont) (tk : tcont) (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a
          (.Kifthenelse .Sskip .Sskip k) (.Kseq .Sskip tk)
    | match_Kifthenelse_1 (ce : composite_env) (a : Clight.expr)
        (s1 s2 : cstatement) (k : ccont) (ts1 ts2 : Clight.statement)
        (tk : tcont) (h1 : tr_stmt ce s1 ts1) (h2 : tr_stmt ce s2 ts2)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a
          (.Kifthenelse s1 s2 k) (.Kseq (.Sifthenelse a ts1 ts2) tk)
    | match_Kwhile1 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' : Clight.statement) (a : Clight.expr)
        (ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kwhile1 r s k)
          (.Kseq (makeif a .Sskip .Sbreak)
            (.Kseq ts (.Kloop1 (.Ssequence s' ts) .Sskip tk)))
    | match_Kdowhile2 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' : Clight.statement) (a : Clight.expr)
        (ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kdowhile2 r s k)
          (.Kseq (makeif a .Sskip .Sbreak) (.Kloop2 ts s' tk))
    | match_Kfor2 (ce : composite_env) (r : cexpr) (s3 s : cstatement)
        (k : ccont) (s' : Clight.statement) (a : Clight.expr)
        (ts3 ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs3 : tr_stmt ce s3 ts3)
        (hs : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kfor2 r s3 s k)
          (.Kseq (makeif a .Sskip .Sbreak)
            (.Kseq ts (.Kloop1 (.Ssequence s' ts) ts3 tk)))
    | match_Kswitch1 (ce : composite_env) (ls : clabeled_statements)
        (k : ccont) (a : Clight.expr) (tls : Clight.labeled_statements)
        (tk : tcont) (hls : tr_lblstmts ce ls tls)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kswitch1 ls k)
          (.Kseq (.Sswitch a tls) tk)
    | match_Kreturn (ce : composite_env) (k : ccont) (a : Clight.expr)
        (tk : tcont) (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kreturn k)
          (.Kseq (.Sreturn (some a)) tk)
end

inductive match_states
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (prog : cprogram) (tprog : tprogram) :
    cstate → tstate → Prop where
  | match_exprstates (f : cfunction) (r : cexpr) (k : ccont) (e : cenv)
      (m : mem) (tf : tfunction) (sl : List Clight.statement) (tk : tcont)
      (le : ttemp_env) (dest : destination) (a : Clight.expr)
      (tmps : List ident) (cu : cprogram)
      (hlink : Ctypes.linkorder_program cu prog)
      (htrf : tr_function cu.prog_comp_env f tf)
      (htr : tr_top cu.prog_comp_env (Clight.globalenv tprog) e le m dest r sl a tmps)
      (hmc : match_cont_exp prog tprog cu.prog_comp_env dest a k tk) :
      match_states prog tprog (.ExprState f r k e m)
        (.State tf .Sskip (Kseqlist sl tk) e le m)
  | match_regularstates (f : cfunction) (s : cstatement) (k : ccont)
      (e : cenv) (m : mem) (tf : tfunction) (ts : Clight.statement)
      (tk : tcont) (le : ttemp_env) (cu : cprogram)
      (hlink : Ctypes.linkorder_program cu prog)
      (htrf : tr_function cu.prog_comp_env f tf)
      (htr : tr_stmt cu.prog_comp_env s ts)
      (hmc : match_cont prog tprog cu.prog_comp_env k tk) :
      match_states prog tprog (.State f s k e m)
        (.State tf ts tk e le m)
  | match_callstates (fd : cfundef) (args : List val) (k : ccont) (m : mem)
      (tfd : tfundef) (tk : tcont) (cu : cprogram)
      (hlink : Ctypes.linkorder_program cu prog)
      (htr : tr_fundef cu fd tfd)
      (hmc : ∀ ce, match_cont prog tprog ce k tk) :
      match_states prog tprog (.Callstate fd args k m)
        (.Callstate tfd args tk m)
  | match_returnstates (res : val) (k : ccont) (m : mem) (tk : tcont)
      (hmc : ∀ ce, match_cont prog tprog ce k tk) :
      match_states prog tprog (.Returnstate res k m)
        (.Returnstate res tk m)
  | match_stuckstate (S : tstate) :
      match_states prog tprog .Stuckstate S

export match_states (match_exprstates)

/-! Exact descriptors for later proof migration. -/

def transf_program_matchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ctx p tp, SimplExpr.transl_program ctx p = .OK tp → match_prog p tp

def comp_env_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    (Clight.globalenv tp).genv_cenv = (Csem.globalenv p).genv_cenv

def symbols_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp → ∀ s,
    Genv.find_symbol (Clight.globalenv tp).genv_genv s =
      Genv.find_symbol (Csem.globalenv p).genv_genv s

def senv_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    Senv.equiv (Genv.to_senv (Csem.globalenv p).genv_genv)
      (Genv.to_senv (Clight.globalenv tp).genv_genv)

def function_ptr_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp → ∀ b f,
    Genv.find_funct_ptr (Csem.globalenv p).genv_genv b = some f →
      ∃ cu tf,
        Genv.find_funct_ptr (Clight.globalenv tp).genv_genv b = some tf ∧
          tr_fundef cu f tf ∧ Ctypes.linkorder_program cu p

def functions_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp → ∀ v f,
    Genv.find_funct (Csem.globalenv p).genv_genv v = some f →
      ∃ cu tf,
        Genv.find_funct (Clight.globalenv tp).genv_genv v = some tf ∧
          tr_fundef cu f tf ∧ Ctypes.linkorder_program cu p
def type_of_fundef_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cu f tf, tr_fundef cu f tf → Clight.type_of_fundef tf = Csyntax.type_of_fundef f
def function_return_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce f tf, tr_function ce f tf → tf.fn_return = f.fn_return
def eval_Ederef'Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tge : tgenv) e le m a t l ofs,
    Clight.eval_expr tge e le m a (.Vptr l ofs) →
      Clight.eval_lvalue tge e le m (Ederef' a t) l ofs .Full
def typeof_Ederef'Statement : Prop :=
  ∀ a t, Clight.typeof (Ederef' a t) = t
def eval_Eaddrof'Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tge : tgenv) e le m a t l ofs,
    Clight.eval_lvalue tge e le m a l ofs .Full →
      Clight.eval_expr tge e le m (Eaddrof' a t) (.Vptr l ofs)
def typeof_Eaddrof'Statement : Prop :=
  ∀ a t, Clight.typeof (Eaddrof' a t) = t
def eval_make_normalizeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tge : tgenv) e le m a n sz sg sg1 attr (width : Z),
    ZArith.BinInt.Z.lt .Z0 width →
    ZArith.BinInt.Z.le width (bitsize_intsize sz) →
    Clight.typeof a = .Tint sz sg1 attr →
    Clight.eval_expr tge e le m a (.Vint n) →
    Clight.eval_expr tge e le m
      (make_normalize sz sg width a)
      (.Vint (bitfield_normalize sz sg width n))

def eval_simpl_expr_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ tp e le m a v,
    Clight.eval_expr (Clight.globalenv tp) e le m a v →
      match SimplExpr.eval_simpl_expr a with
      | some v' => v' = v
      | none => True

def tr_simple_nilStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cunit : cprogram,
  (∀ le dst r sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
      (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []) ∧
  (∀ le rl sl al tmps, tr_exprlist cunit.prog_comp_env le rl sl al tmps →
      Cstrategy.simplelist rl = true → sl = [])

def tr_simple_expr_nilStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cunit : cprogram) le dst r sl a tmps,
    tr_expr cunit.prog_comp_env le dst r sl a tmps →
    (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []

def deref_loc_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ ty m b ofs bf t v,
    Csem.deref_loc (Csem.globalenv p) ty m b ofs bf t v →
      match chunk_for_volatile_type ty bf with
      | none => t = E0 ∧ Clight.deref_loc ty m b ofs bf v
      | some chunk => bf = .Full ∧
          volatile_load (Genv.to_senv (Clight.globalenv tp).genv_genv)
            chunk m b ofs t v

def assign_loc_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ ty m b ofs bf v t m' v',
    Csem.assign_loc (Csem.globalenv p) ty m b ofs bf v t m' v' →
      match chunk_for_volatile_type ty bf with
      | none => t = E0 ∧
          Clight.assign_loc (Clight.globalenv tp).genv_cenv ty m b ofs bf v m'
      | some chunk => bf = .Full ∧
          volatile_store (Genv.to_senv (Clight.globalenv tp).genv_genv)
            chunk m b ofs v t m'

def is_bitfield_access_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ cunit : cprogram, Ctypes.linkorder_program cunit p →
    ∀ e le m a b ofs bf bf',
    Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf →
    tr_is_bitfield_access cunit.prog_comp_env a bf' → bf' = bf

def make_assign_value_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p ty m b ofs bf v t m' v',
    Csem.assign_loc (Csem.globalenv p) ty m b ofs bf v t m' v' →
    ∀ (tge : tgenv) e le m'' r, Clight.typeof r = ty →
      Clight.eval_expr tge e le m'' r v →
      Clight.eval_expr tge e le m''
        (make_assign_value bf r) v'
def typeof_make_assign_valueStatement : Prop :=
  ∀ bf r, Clight.typeof (make_assign_value bf r) = Clight.typeof r
def tr_simpleStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) e m,
    (∀ r v, Cstrategy.eval_simple_rvalue (Csem.globalenv p) e m r v →
      ∀ le dst sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
        match dst with
        | .For_val => sl = [] ∧ Csyntax.typeof r = Clight.typeof a ∧
            Clight.eval_expr (Clight.globalenv tp) e le m a v
        | .For_effects => sl = []
        | .For_set sd => ∃ b, sl = do_set sd b ∧
            Csyntax.typeof r = Clight.typeof b ∧
            Clight.eval_expr (Clight.globalenv tp) e le m b v) ∧
    (∀ l b ofs bf,
      Cstrategy.eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf →
      ∀ le sl a tmps, tr_expr cunit.prog_comp_env le .For_val l sl a tmps →
        sl = [] ∧ Csyntax.typeof l = Clight.typeof a ∧
          Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf)

def tr_simple_rvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) e m r v,
    Cstrategy.eval_simple_rvalue (Csem.globalenv p) e m r v →
    ∀ le dst sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
      match dst with
      | .For_val => sl = [] ∧ Csyntax.typeof r = Clight.typeof a ∧
          Clight.eval_expr (Clight.globalenv tp) e le m a v
      | .For_effects => sl = []
      | .For_set sd => ∃ b, sl = do_set sd b ∧
          Csyntax.typeof r = Clight.typeof b ∧
          Clight.eval_expr (Clight.globalenv tp) e le m b v

def tr_simple_lvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) e m l b ofs bf,
    Cstrategy.eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf →
    ∀ le sl a tmps, tr_expr cunit.prog_comp_env le .For_val l sl a tmps →
      sl = [] ∧ Csyntax.typeof l = Clight.typeof a ∧
        Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf

def tr_simple_exprlistStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) le rl sl al tmps,
    tr_exprlist cunit.prog_comp_env le rl sl al tmps →
    ∀ e m tyl vl,
      Cstrategy.eval_simple_list (Csem.globalenv p) e m rl tyl vl →
      sl = [] ∧ Clight.eval_exprlist (Clight.globalenv tp) e le m al tyl vl

def typeof_contextStatement : Prop :=
  ∀ k1 k2 C, leftcontext k1 k2 C →
    ∀ e1 e2, Csyntax.typeof e1 = Csyntax.typeof e2 →
      Csyntax.typeof (C e1) = Csyntax.typeof (C e2)

def tr_expr_leftcontext_recStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cunit : cprogram,
  (∀ kfrom kto C, leftcontext kfrom kto C →
    ∀ le e dst sl a tmps, tr_expr cunit.prog_comp_env le dst (C e) sl a tmps →
      ∃ dst' sl1 sl2 a' tmp',
        tr_expr cunit.prog_comp_env le dst' e sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' e' sl3,
          tr_expr cunit.prog_comp_env le' dst' e' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof e' = Csyntax.typeof e →
          tr_expr cunit.prog_comp_env le' dst (C e') (sl3 ++ sl2) a tmps)) ∧
  (∀ kfrom C, leftcontextlist kfrom C →
    ∀ le e sl a tmps, tr_exprlist cunit.prog_comp_env le (C e) sl a tmps →
      ∃ dst' sl1 sl2 a' tmp',
        tr_expr cunit.prog_comp_env le dst' e sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' e' sl3,
          tr_expr cunit.prog_comp_env le' dst' e' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof e' = Csyntax.typeof e →
          tr_exprlist cunit.prog_comp_env le' (C e') (sl3 ++ sl2) a tmps))

def tr_expr_leftcontextStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cunit : cprogram) C le r dst sl a tmps, leftcontext .RV .RV C →
    tr_expr cunit.prog_comp_env le dst (C r) sl a tmps →
      ∃ dst' sl1 sl2 a' tmp',
        tr_expr cunit.prog_comp_env le dst' r sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' r' sl3,
          tr_expr cunit.prog_comp_env le' dst' r' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof r' = Csyntax.typeof r →
          tr_expr cunit.prog_comp_env le' dst (C r') (sl3 ++ sl2) a tmps)

def tr_top_leftcontextStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tprog : tprogram) (cunit : cprogram) e le m dst rtop sl a tmps,
    tr_top cunit.prog_comp_env (Clight.globalenv tprog) e le m dst rtop sl a tmps →
    ∀ r C, rtop = C r → leftcontext .RV .RV C →
      ∃ dst' sl1 sl2 a' tmp',
        tr_top cunit.prog_comp_env (Clight.globalenv tprog)
          e le m dst' r sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' m' r' sl3,
          tr_expr cunit.prog_comp_env le' dst' r' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof r' = Csyntax.typeof r →
          tr_top cunit.prog_comp_env (Clight.globalenv tprog)
            e le' m' dst (C r') (sl3 ++ sl2) a tmps)

def sem_cast_deterministicStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty ty' m1 v1 m2 v2,
    sem_cast v ty ty' m1 = some v1 → sem_cast v ty ty' m2 = some v2 → v1 = v2

def static_bool_val_soundStatement : Prop :=
  ∀ v t m b, bool_val v t Mem.empty = some b → bool_val v t m = some b

def step_makeifStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) tp f a s1 s2 k e le m v1 b,
    Clight.eval_expr (Clight.globalenv tp) e le m a v1 →
    bool_val v1 (Clight.typeof a) m = some b →
    star (Clight.step1 xi) (Clight.globalenv tp)
      (Clight.State f (makeif a s1 s2) k e le m) E0
      (Clight.State f (if b then s1 else s2) k e le m)

def step_make_setStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) p tp, match_prog p tp →
    ∀ id a ty m b ofs bf t v e le f k,
    Csem.deref_loc (Csem.globalenv p) ty m b ofs bf t v →
    Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf →
    Clight.typeof a = ty →
    Clight.step1 xi
      (Clight.globalenv tp) (Clight.State f (make_set bf id a) k e le m)
      t (Clight.State f .Sskip k e (PTree.set id v le) m)

def step_make_assignStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) p tp, match_prog p tp →
    ∀ a1 a2 ty m b ofs bf t v m' v' v2 e le f k,
    Csem.assign_loc (Csem.globalenv p) ty m b ofs bf v t m' v' →
    Clight.eval_lvalue (Clight.globalenv tp) e le m a1 b ofs bf →
    Clight.eval_expr (Clight.globalenv tp) e le m a2 v2 →
    sem_cast v2 (Clight.typeof a2) ty m = some v →
    Clight.typeof a1 = ty →
    Clight.step1 xi
      (Clight.globalenv tp) (Clight.State f (make_assign bf a1 a2) k e le m)
      t (Clight.State f .Sskip k e le m')
def Kseqlist_appStatement : Prop :=
  ∀ sl1 sl2 k, Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k)

def push_seqStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tp : tprogram) f sl k e le m,
    star (Clight.step1 xi) (Clight.globalenv tp)
      (.State f (SimplExpr.makeseq sl) k e le m) E0
      (.State f .Sskip (Kseqlist sl k) e le m)

def step_tr_rvalofStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ (cu : cprogram), Ctypes.linkorder_program cu p →
    ∀ ty m b ofs bf t v e le a sl a' tmp f k,
      Csem.deref_loc (Csem.globalenv p) ty m b ofs bf t v →
      Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf →
      tr_rvalof cu.prog_comp_env ty a sl a' tmp →
      Clight.typeof a = ty →
      ∃ le',
        star (Clight.step1 xi) (Clight.globalenv tp)
          (.State f .Sskip (Kseqlist sl k) e le m) t
          (.State f .Sskip k e le' m) ∧
        Clight.eval_expr (Clight.globalenv tp) e le' m a' v ∧
        Clight.typeof a' = Clight.typeof a ∧
        ∀ x, x ∉ tmp → PTree.get x le' = PTree.get x le

def match_cont_call_contStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) ce k tk,
    match_cont p tp ce k tk →
    ∀ ce', match_cont p tp ce' (Csem.call_cont k) (Clight.call_cont tk)

def match_cont_is_call_contStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) ce k tk,
    match_cont p tp ce k tk → Csem.is_call_cont k →
    ∀ ce', match_cont p tp ce' k tk

def tr_select_switchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce n ls tls, tr_lblstmts ce ls tls →
    tr_lblstmts ce (Csem.select_switch n ls) (Clight.select_switch n tls)

def tr_seq_of_labeled_statementStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce ls tls, tr_lblstmts ce ls tls →
    tr_stmt ce (Csem.seq_of_labeled_statement ls)
      (Clight.seq_of_labeled_statement tls)

def tr_find_labelStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) ce lbl s k ts tk,
    tr_stmt ce s ts → match_cont p tp ce k tk →
    match Csem.find_label lbl s k with
    | none => Clight.find_label lbl ts tk = none
    | some (s', k') =>
        ∃ ts' tk', Clight.find_label lbl ts tk = some (ts', tk') ∧
          tr_stmt ce s' ts' ∧ match_cont p tp ce k' tk'

def leftcontext_sizeStatement : Prop :=
  ∀ kfrom kto C, leftcontext kfrom kto C →
    ∀ e1 e2, esize e1 < esize e2 → esize (C e1) < esize (C e2)

def tr_val_genStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce le dst v ty a tmp,
    Clight.typeof a = ty →
    (∀ tge e le' m,
      (∀ id, id ∈ tmp → PTree.get id le' = PTree.get id le) →
      Clight.eval_expr tge e le' m a v) →
    tr_expr ce le dst (.Eval v ty) (SimplExprspec.final dst a) a tmp

def estep_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ S1 t S2, Cstrategy.estep xi (Csem.globalenv p) S1 t S2 →
    ∀ S1', match_states p tp S1 S1' →
      ∃ S2',
        (plus (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∨
          (star (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∧
            measure S2 < measure S1)) ∧
        match_states p tp S2 S2'

def tr_top_val_for_val_invStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tp : tprogram) ce e le m v ty sl a tmps,
    tr_top ce (Clight.globalenv tp) e le m .For_val (.Eval v ty) sl a tmps →
    sl = [] ∧ Clight.typeof a = ty ∧
      Clight.eval_expr (Clight.globalenv tp) e le m a v

def alloc_variables_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ e m params e' m',
      Csem.alloc_variables (Csem.globalenv p) e m params e' m' →
      Clight.alloc_variables (Clight.globalenv tp) e m params e' m'

def bind_parameters_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ e m params args m',
      Csem.bind_parameters (Csem.globalenv p) e m params args m' →
      Clight.bind_parameters (Clight.globalenv tp) e m params args m'

def blocks_of_env_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ e, Clight.blocks_of_env (Clight.globalenv tp) e =
      Csem.blocks_of_env (Csem.globalenv p) e

def sstep_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ S1 t S2, Csem.sstep xi (Csem.globalenv p) S1 t S2 →
    ∀ S1', match_states p tp S1 S1' →
      ∃ S2',
        (plus (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∨
          (star (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∧
            measure S2 < measure S1)) ∧
        match_states p tp S2 S2'

def simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ S1 t S2, Cstrategy.step xi (Csem.globalenv p) S1 t S2 →
    ∀ S1', match_states p tp S1 S1' →
      ∃ S2',
        (plus (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∨
          (star (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∧
            measure S2 < measure S1)) ∧
        match_states p tp S2 S2'

def transl_initial_statesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ S, Csem.initial_state p S →
      ∃ S', Clight.initial_state tp S' ∧ match_states p tp S S'

def transl_final_statesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) S S' r,
    match_states p tp S S' → Csem.final_state S r → Clight.final_state S' r

def transl_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    forward_simulation (Cstrategy.semantics xi p) (Clight.semantics1 xi tp)

def TransfSimplExprLinkStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations) : Prop :=
  @CompCert4Lean.Common.Linking.TransfLink cprogram tprogram
    (Ctypes.Linker_program cfunction csyntaxLinkerCertificate)
    (Ctypes.Linker_program tfunction clightLinkerCertificate)
    (fun p tp => match_prog p tp)

end CompCert4Lean.Cfrontend.SimplExprproof
