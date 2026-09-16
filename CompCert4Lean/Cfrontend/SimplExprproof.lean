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

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem typeof_make_assign_value : typeof_make_assign_valueStatement := by
  intro bf r
  cases bf with
  | Full => rfl
  | Bits size signed pos width =>
      unfold SimplExpr.make_assign_value SimplExpr.make_normalize
      by_cases h : size = .IBool ∨ signed = .Unsigned
      · simp [h, Clight.typeof]
      · simp [h, Clight.typeof]

theorem typeof_context : typeof_contextStatement := by
  intro k1 k2 C h
  cases h <;> intro e1 e2 heq <;> simp_all [Csyntax.typeof]

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem comp_env_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      comp_env_preservedStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp hmatch
  have htypes : tp.prog_types = p.prog_types := hmatch.2
  change tp.prog_comp_env = p.prog_comp_env
  have hp : Ctypes.build_composite_env p.prog_types = .OK p.prog_comp_env :=
    p.prog_comp_env_eq
  have htp : Ctypes.build_composite_env tp.prog_types = .OK tp.prog_comp_env :=
    tp.prog_comp_env_eq
  rw [htypes] at htp
  apply CompCert4Lean.Common.Errors.res.OK.inj
  exact htp.symm.trans hp

private theorem simplexpr_symbol_add_global
    {A B V W : Type} (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
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

private theorem simplexpr_match_genvs_add_global
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (g1 : globdef A V) (g2 : globdef B W)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact simplexpr_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation (globdef A V) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation (globdef B W) b ge2.genv_next g2 ge2.genv_defs
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

private theorem simplexpr_match_genvs_add_globals
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (xs : List (ident × globdef A V)) (ys : List (ident × globdef B W))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (hm : Genv.match_genvs R ge1 ge2) :
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
      exact simplexpr_match_genvs_add_global R ge1 ge2 aid ag bg hm hab

private theorem simplexpr_globalenv_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) (tp : tprogram) (hmatch : match_prog p tp) :
    Genv.match_genvs
      (fun gd1 gd2 => match gd1, gd2 with
        | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧
            @tr_fundef binary64_certificate binary32_certificate cu f tf
        | .Gvar v, .Gvar tv =>
            v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
              v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
        | _, _ => False)
      (Genv.globalenv (Ctypes.program_of_program p))
      (Genv.globalenv (Ctypes.program_of_program tp)) := by
  let R : globdef cfundef type → globdef tfundef type → Prop :=
    fun gd1 gd2 => match gd1, gd2 with
      | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧
          @tr_fundef binary64_certificate binary32_certificate cu f tf
      | .Gvar v, .Gvar tv =>
          v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
            v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
      | _, _ => False
  have hempty : Genv.match_genvs R
      (Genv.empty_genv cfundef type p.prog_public)
      (Genv.empty_genv tfundef type tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none R
  have hlist : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2)
      (Ctypes.program_of_program p).prog_defs
      (Ctypes.program_of_program tp).prog_defs := by
    change list_forall2 (fun a b => a.1 = b.1 ∧
      (match a.2, b.2 with
        | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧
            @tr_fundef binary64_certificate binary32_certificate cu f tf
        | .Gvar v, .Gvar tv =>
            v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
              v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
        | _, _ => False))
      (Ctypes.program_of_program p).prog_defs
      (Ctypes.program_of_program tp).prog_defs
    exact hmatch.1.1
  exact simplexpr_match_genvs_add_globals R
    (Ctypes.program_of_program p).prog_defs
    (Ctypes.program_of_program tp).prog_defs hlist _ _ hempty

private theorem simplexpr_add_globals_public
    {A V : Type} (ge : Genv.t A V) (gl : List (ident × globdef A V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons idg gl ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge idg)

theorem symbols_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      symbols_preservedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch s
  exact (simplexpr_globalenv_match p tp hmatch).mge_symb s

theorem senv_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      senv_preservedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch
  have hg := simplexpr_globalenv_match p tp hmatch
  unfold Senv.equiv
  constructor
  · intro id
    exact hg.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program tp)) id =
      Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program p)) id
    have ht0 := simplexpr_add_globals_public
      (Genv.empty_genv tfundef type tp.prog_public)
      (Ctypes.program_of_program tp).prog_defs
    have hp0 := simplexpr_add_globals_public
      (Genv.empty_genv cfundef type p.prog_public)
      (Ctypes.program_of_program p).prog_defs
    have ht : (Genv.globalenv (Ctypes.program_of_program tp)).genv_public = tp.prog_public := by
      unfold Genv.globalenv
      exact ht0
    have hp : (Genv.globalenv (Ctypes.program_of_program p)).genv_public = p.prog_public := by
      unfold Genv.globalenv
      exact hp0
    have hpub : tp.prog_public = p.prog_public := by
      simpa [Ctypes.program_of_program] using hmatch.1.2.2
    unfold Genv.public_symbol
    cases hs : Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program tp)) id with
    | none =>
        have hs' : Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program p)) id = none := by
          exact (hg.mge_symb id).symm.trans hs
        simp [hs']
    | some b =>
        have hs' : Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program p)) id = some b := by
          exact (hg.mge_symb id).symm.trans hs
        simp [hs', ht, hp, hpub]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program tp)) b =
      Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program p)) b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv (Ctypes.program_of_program p)).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            rw [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            rw [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            rw [h1, h2] at hd
            cases hd with
            | some hrel =>
                cases gd1 <;> cases gd2 <;> simp_all

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Coqlib

theorem function_ptr_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      function_ptr_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch b f hfind
  have hg := simplexpr_globalenv_match p tp hmatch
  have hsrc : Genv.find_def (Genv.globalenv (Ctypes.program_of_program p)) b =
      some (.Gfun f) :=
    (Genv.find_funct_ptr_iff _ _
      (Genv.globalenv (Ctypes.program_of_program p)) b f).mp hfind
  cases htarget : Genv.find_def (Genv.globalenv (Ctypes.program_of_program tp)) b with
  | none =>
      have hd := hg.mge_defs b
      change option_rel _
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program p)) b)
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program tp)) b) at hd
      rw [hsrc, htarget] at hd
      cases hd
  | some gd' =>
      have hd := hg.mge_defs b
      change option_rel _
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program p)) b)
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program tp)) b) at hd
      rw [hsrc, htarget] at hd
      cases gd' with
      | Gfun tf =>
          cases hd with
          | some _ _ hrel =>
              rcases hrel with ⟨cu, hcu, htr⟩
              refine ⟨cu, tf, ?_, htr, hcu⟩
              change Genv.find_funct_ptr
                (Genv.globalenv (Ctypes.program_of_program tp)) b = some tf
              simp [Genv.find_funct_ptr, htarget]
      | Gvar _ =>
          cases hd with
          | some _ _ hrel => cases hrel

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Globalenvs

theorem functions_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      functions_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch v f hfind
  cases v with
  | Vptr b ofs =>
      simp only [Genv.find_funct] at hfind ⊢
      split at hfind <;> rename_i heq
      · have hptr : Genv.find_funct_ptr (Csem.globalenv p).genv_genv b = some f := by
          simpa [heq] using hfind
        obtain ⟨cu, tf, hptrt, htrans, hlink⟩ :=
          function_ptr_translated p tp hmatch b f hptr
        exact ⟨cu, tf, by simpa [heq, hptrt], htrans, hlink⟩
      · cases hfind
  | Vundef => simp [Genv.find_funct] at hfind
  | Vint n => simp [Genv.find_funct] at hfind
  | Vfloat n => simp [Genv.find_funct] at hfind
  | Vlong n => simp [Genv.find_funct] at hfind
  | Vsingle n => simp [Genv.find_funct] at hfind

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem function_return_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      function_return_preservedStatement := by
  intro binary64_certificate binary32_certificate ce f tf h
  cases h with
  | tr_function_intro _ hreturn _ _ _ => exact hreturn

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem eval_Ederef' :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_Ederef'Statement := by
  intro binary64_certificate binary32_certificate ge e le m a t l ofs h
  unfold Ederef'
  cases a with
  | Eaddrof a' ty' =>
      change Clight.eval_lvalue ge e le m
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Ederef (.Eaddrof a' ty') t) l ofs .Full
      by_cases hc : CompCert4Lean.Lib.Coqlib.proj_sumbool
          (Ctypes.type_eq t (Clight.typeof a')) = true
      · simp [hc]
        cases h with
        | eval_Eaddrof _ _ _ _ hlvalue => exact hlvalue
        | eval_Elvalue _ _ _ _ _ hlvalue hderef => cases hlvalue
      · simp [hc]
        exact Clight.eval_lvalue.eval_Ederef _ _ _ _ h
  | _ => exact Clight.eval_lvalue.eval_Ederef _ _ _ _ h

theorem eval_Eaddrof' :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_Eaddrof'Statement := by
  intro binary64_certificate binary32_certificate ge e le m a t l ofs h
  unfold Eaddrof'
  cases a with
  | Ederef a' ty' =>
      change Clight.eval_expr ge e le m
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Eaddrof (.Ederef a' ty') t) (.Vptr l ofs)
      by_cases hc : CompCert4Lean.Lib.Coqlib.proj_sumbool
          (Ctypes.type_eq t (Clight.typeof a')) = true
      · simp [hc]
        cases h with
        | eval_Ederef _ _ _ _ ha => exact ha
      · simp [hc]
        exact Clight.eval_expr.eval_Eaddrof _ _ _ _ h
  | _ => exact Clight.eval_expr.eval_Eaddrof _ _ _ _ h

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem typeof_Ederef' : typeof_Ederef'Statement := by
  intro a t
  unfold Ederef'
  cases a with
  | Eaddrof a' ty' =>
      change Clight.typeof
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Ederef (.Eaddrof a' ty') t) = t
      cases hte : Ctypes.type_eq t (Clight.typeof a') with
      | left heq =>
          simp [hte, CompCert4Lean.Lib.Coqlib.proj_sumbool, heq]
      | right hneq =>
          simp [CompCert4Lean.Lib.Coqlib.proj_sumbool]
          rfl
  | _ => rfl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem typeof_Eaddrof' : typeof_Eaddrof'Statement := by
  intro a t
  unfold Eaddrof'
  cases a with
  | Ederef a' ty' =>
      change Clight.typeof
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Eaddrof (.Ederef a' ty') t) = t
      cases hte : Ctypes.type_eq t (Clight.typeof a') with
      | left heq =>
          simp [hte, CompCert4Lean.Lib.Coqlib.proj_sumbool, heq]
      | right hneq =>
          simp [CompCert4Lean.Lib.Coqlib.proj_sumbool]
          rfl
  | _ => rfl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem tr_simple_nil :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_nilStatement := by
  intro binary64_certificate binary32_certificate cunit
  constructor
  · intro le dst r sl a tmps h
    let P1 := fun (dst : destination) (r : cexpr) (sl : List Clight.statement)
        (a : Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_expr cunit.prog_comp_env le dst r sl a tmps) =>
        (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []
    let P2 := fun (rl : cexprlist) (sl : List Clight.statement)
        (al : List Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_exprlist cunit.prog_comp_env le rl sl al tmps) =>
        Cstrategy.simplelist rl = true → sl = []
    refine SimplExprspec.tr_expr.rec (motive_1 := P1) (motive_2 := P2)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      h
    all_goals
      intros <;> dsimp [P1, P2] at * <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      rintro (rfl | rfl) <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      try (intro hs hv; cases ‹SimplExprspec.tr_rvalof _ _ _ _ _ _› <;> simp_all)
  · intro le rl sl al tmps h
    let P1 := fun (dst : destination) (r : cexpr) (sl : List Clight.statement)
        (a : Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_expr cunit.prog_comp_env le dst r sl a tmps) =>
        (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []
    let P2 := fun (rl : cexprlist) (sl : List Clight.statement)
        (al : List Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_exprlist cunit.prog_comp_env le rl sl al tmps) =>
        Cstrategy.simplelist rl = true → sl = []
    refine SimplExprspec.tr_exprlist.rec (motive_1 := P1) (motive_2 := P2)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    all_goals
      intros <;> dsimp [P1, P2] at * <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      rintro (rfl | rfl) <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      try (intro hs hv; cases ‹SimplExprspec.tr_rvalof _ _ _ _ _ _› <;> simp_all)

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem tr_simple_expr_nil :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_expr_nilStatement := by
  intro binary64_certificate binary32_certificate cunit le dst r sl a tmps h hdst hsimple
  exact (tr_simple_nil (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cunit).1
    le dst r sl a tmps h hdst hsimple

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

private theorem simplexpr_volatile_store_preserved
    (ge1 ge2 : CompCert4Lean.Common.Globalenvs.Senv.t)
    (chunk : CompCert4Lean.Common.AST.memory_chunk)
    (m1 : mem) (b : block) (ofs : ptrofs) (v : val) (t : trace) (m2 : mem)
    (heq : CompCert4Lean.Common.Globalenvs.Senv.equiv ge1 ge2)
    (hstore : CompCert4Lean.Common.Events.volatile_store ge1 chunk m1 b ofs v t m2) :
    CompCert4Lean.Common.Events.volatile_store ge2 chunk m1 b ofs v t m2 := by
  cases hstore with
  | volatile_store_vol id ev v is_volatile find_symbol eventval_matches =>
      apply CompCert4Lean.Common.Events.volatile_store_vol
      · rw [heq.2.2 b]
        exact is_volatile
      · rw [heq.1 _]
        exact find_symbol
      · exact CompCert4Lean.Common.Events.eventval_match_preserved
          ge1 ge2 heq.2.1 heq.1 ev _
            (CompCert4Lean.Common.Values.Val.load_result chunk v) eventval_matches
  | volatile_store_nonvol v m' not_volatile store =>
      apply CompCert4Lean.Common.Events.volatile_store_nonvol
      · rw [heq.2.2 b]
        exact not_volatile
      · exact store

theorem assign_loc_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      assign_loc_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch ty m b ofs bf v t m' v' h
  cases h with
  | value hmode hvol hstore =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact Clight.assign_loc_value _ _ _ hmode hstore
  | volatile hmode hvol hstore =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact simplexpr_volatile_store_preserved _ _ _ _ _ _ _ _ _
        (senv_preserved (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) p tp hmatch)
        hstore
  | copy hmode halignSource halignTarget hseparated hload hstore =>
      have henv : (Clight.globalenv tp).genv_cenv = (Csem.globalenv p).genv_cenv := by
        exact comp_env_preserved (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) p tp hmatch
      simp [chunk_for_volatile_type, Ctypes.type_is_volatile, hmode]
      rw [henv]
      apply Clight.assign_loc_copy _ _ _ _ hmode
      · intro hsize
        exact halignSource
      · intro hsize
        exact halignTarget
      · exact hseparated
      · exact hload
      · exact hstore
  | bitfield hstore =>
      unfold chunk_for_volatile_type
      by_cases hvol : Ctypes.type_is_volatile ty = true
      · simp [hvol]
        cases hmode : Ctypes.access_mode ty <;> simp [hmode]
        all_goals exact Clight.assign_loc_bitfield _ _ _ _ _ _ _ hstore
      · simp [hvol]
        exact Clight.assign_loc_bitfield _ _ _ _ _ _ _ hstore

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem deref_loc_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      deref_loc_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch ty m b ofs bf t v h
  cases h with
  | value hmode hvol hload =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact Clight.deref_loc_value _ _ hmode hload
  | volatile hmode hvol hload =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact CompCert4Lean.Common.Events.volatile_load_preserved
        (ge1 := CompCert4Lean.Common.Globalenvs.Genv.to_senv (Csem.globalenv p).genv_genv)
        (ge2 := CompCert4Lean.Common.Globalenvs.Genv.to_senv (Clight.globalenv tp).genv_genv)
        (chunk := _) (m := m) (b := b) (ofs := ofs) (t := t) (v := v)
        (senv_preserved (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) p tp hmatch)
        hload
  | reference hmode =>
      simp [chunk_for_volatile_type, hmode]
      exact Clight.deref_loc_reference hmode
  | copy hmode =>
      simp [chunk_for_volatile_type, hmode]
      exact Clight.deref_loc_copy hmode
  | bitfield hload =>
      cases hvol : Ctypes.type_is_volatile ty with
      | false =>
          simp [chunk_for_volatile_type, hvol]
          exact Clight.deref_loc_bitfield _ _ _ _ _ hload
      | true =>
          cases hmode : Ctypes.access_mode ty with
          | By_value chunk =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload
          | By_reference =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload
          | By_copy =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload
          | By_nothing =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

private theorem simplexpr_add_composite_defs_consistent :
    ∀ (defs : List Ctypes.composite_definition) (env1 env2 : Ctypes.composite_env),
      Ctypes.add_composite_definitions env1 defs = .OK env2 →
      Ctypes.composite_env_consistent env1 →
      Ctypes.composite_env_consistent env2 := by
  intro defs
  induction defs with
  | nil =>
      intro env1 env2 hadd hbase
      simp only [Ctypes.add_composite_definitions] at hadd
      cases hadd
      exact hbase
  | cons d defs ih =>
      intro env1 env2 hadd hbase
      change PTree.tree Ctypes.composite at env1 env2
      cases d with
      | Composite id su ms a =>
          cases hco : Ctypes.composite_of_def env1 id su ms a with
          | Error msg =>
              simp [Ctypes.add_composite_definitions, hco] at hadd
          | OK co =>
              have hrest :
                  Ctypes.add_composite_definitions (PTree.set id co env1) defs =
                    .OK env2 := by
                simpa [Ctypes.add_composite_definitions, hco] using hadd
              have hco_cons : Ctypes.composite_consistent env1 co :=
                Ctypes.composite_of_def_consistent env1 id su ms a co hco
              have hnone : PTree.get
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  env1 = none := by
                unfold Ctypes.composite_of_def at hco
                split at hco
                · rename_i hdup
                  cases hco
                · rename_i hnone
                  exact hnone
              have hincr : ∀ j cj, PTree.get j env1 = some cj →
                  PTree.get j (PTree.set id co env1) = some cj := by
                intro j cj hj
                have hs := PTree.getSet_equation (A := Ctypes.composite)
                  j (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  co env1
                rw [hs]
                split
                · rename_i hEq
                  exfalso
                  cases hEq
                  have hbad : (none : Option Ctypes.composite) = some cj :=
                    hnone.symm.trans hj
                  cases hbad
                · exact hj
              have hset : Ctypes.composite_env_consistent (PTree.set id co env1) := by
                intro j cj hj
                have hspec := PTree.getSet_equation (A := Ctypes.composite)
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from j)
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  co env1
                rw [hspec] at hj
                split at hj
                · rename_i hEq
                  cases hEq
                  cases hj
                  exact Ctypes.composite_consistent_stable env1
                    (PTree.set id co env1) hincr co hco_cons
                · exact Ctypes.composite_consistent_stable env1
                    (PTree.set id co env1) hincr cj (hbase j cj hj)
              exact ih (PTree.set id co env1) env2 hrest hset

private theorem simplexpr_cenv_consistent
    (cunit : cprogram) :
    Ctypes.composite_env_consistent cunit.prog_comp_env := by
  have hempty : Ctypes.composite_env_consistent
      (show Ctypes.composite_env from PTree.empty Ctypes.composite) := by
    intro id co hget
    change PTree.get (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
      (PTree.empty Ctypes.composite) = some co at hget
    simp only [PTree.empty, PTree.get] at hget
    cases hget
  exact simplexpr_add_composite_defs_consistent cunit.prog_types
    (show Ctypes.composite_env from PTree.empty Ctypes.composite)
    cunit.prog_comp_env cunit.prog_comp_env_eq hempty

private theorem simplexpr_cenv_inclusion_for_bitfield
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) (tp : tprogram) (cunit : cprogram)
    (hmatch : match_prog p tp)
    (hlink : Ctypes.linkorder_program cunit p) :
    ∀ id co, PTree.get id cunit.prog_comp_env = some co →
      PTree.get id (Clight.globalenv tp).genv_cenv = some co := by
  intro id co hget
  have hp := hlink.2 id co hget
  have henv : (Clight.globalenv tp).genv_cenv =
      (Csem.globalenv p).genv_cenv :=
    comp_env_preserved (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) p tp hmatch
  rw [henv]
  exact hp

private theorem simplexpr_bitfield_composite_lookup
    (cunit : cprogram)
    (tp : tprogram)
    (hinc : ∀ id co, PTree.get id cunit.prog_comp_env = some co →
      PTree.get id (Clight.globalenv tp).genv_cenv = some co)
    (id : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (co co' : Ctypes.composite)
    (hget : PTree.get id (Clight.globalenv tp).genv_cenv = some co)
    (hget' : PTree.get id cunit.prog_comp_env = some co') :
    co' = co ∧ complete_members cunit.prog_comp_env co'.co_members = true := by
  have hget'' := hinc id co' hget'
  have heq : co' = co := Option.some.inj (hget''.symm.trans hget)
  have hconsistent : composite_env_consistent cunit.prog_comp_env :=
    simplexpr_cenv_consistent cunit
  have hco := hconsistent id co' hget'
  exact ⟨heq, hco.co_consistent_complete⟩

theorem is_bitfield_access_sound :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      is_bitfield_access_soundStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit hlink
  have hinc := simplexpr_cenv_inclusion_for_bitfield
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp cunit hmatch hlink
  intro e le m a b ofs bf bf' hEval htr
  cases hEval with
  | eval_Evar_local id loc ty hfind =>
      simpa [tr_is_bitfield_access] using htr
  | eval_Evar_global id loc ty hlocal hglobal =>
      simpa [tr_is_bitfield_access] using htr
  | eval_Ederef a ty loc ofs ha =>
      simpa [tr_is_bitfield_access] using htr
  | eval_Efield_struct a id ty loc ofs structId co att delta bf ha htype hcomposite hoffset =>
      simp only [tr_is_bitfield_access] at htr
      rw [htype] at htr
      rcases htr with ⟨co', ofs', hcomposite', hoffset'⟩
      rcases simplexpr_bitfield_composite_lookup cunit tp hinc structId co co'
        hcomposite hcomposite' with ⟨hEq, hcomplete⟩
      subst co'
      have hstable := Ctypes.field_offset_stable
        cunit.prog_comp_env (Clight.globalenv tp).genv_cenv hinc id
        (Ctypes.composite.co_members co)
        hcomplete
      have hpairs : (delta, bf) = (ofs', bf') :=
        CompCert4Lean.Common.Errors.res.OK.inj
          (hoffset.symm.trans (hstable.trans hoffset'))
      exact (congrArg Prod.snd hpairs).symm
  | eval_Efield_union a id ty loc ofs unionId co att delta bf ha htype hcomposite hoffset =>
      simp only [tr_is_bitfield_access] at htr
      rw [htype] at htr
      rcases htr with ⟨co', ofs', hcomposite', hoffset'⟩
      rcases simplexpr_bitfield_composite_lookup cunit tp hinc unionId co co'
        hcomposite hcomposite' with ⟨hEq, hcomplete⟩
      subst co'
      have hstable := Ctypes.union_field_offset_stable
        cunit.prog_comp_env (Clight.globalenv tp).genv_cenv hinc id
        (Ctypes.composite.co_members co)
        hcomplete
      have hpairs : (delta, bf) = (ofs', bf') :=
        CompCert4Lean.Common.Errors.res.OK.inj
          (hoffset.symm.trans (hstable.trans hoffset'))
      exact (congrArg Prod.snd hpairs).symm

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Cop

theorem tr_simple_rvalue :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_rvalueStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit e m r v hEval
  let P1 := fun (l : cexpr) (b : block) (ofs : ptrofs) (bf : bitfield)
      (_ : Cstrategy.eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf) =>
      ∀ le sl a tmps, tr_expr cunit.prog_comp_env le .For_val l sl a tmps →
        sl = [] ∧ Csyntax.typeof l = Clight.typeof a ∧
          Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf
  let P2 := fun (r : cexpr) (v : val)
      (_ : Cstrategy.eval_simple_rvalue (Csem.globalenv p) e m r v) =>
      ∀ le dst sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
      match dst with
      | .For_val => sl = [] ∧ Csyntax.typeof r = Clight.typeof a ∧
          Clight.eval_expr (Clight.globalenv tp) e le m a v
      | .For_effects => sl = []
      | .For_set sd => ∃ b, sl = do_set sd b ∧
          Csyntax.typeof r = Clight.typeof b ∧
          Clight.eval_expr (Clight.globalenv tp) e le m b v
  have hrec : P2 r v hEval := by
    refine Cstrategy.eval_simple_rvalue.rec (motive_1 := P1) (motive_2 := P2)
      (esl_loc := by
        intro b ofs ty bf
        dsimp [P1]
        intro le sl a tmps htr
        cases htr)
      (esl_var_local := by
        intro x ty b hfind
        dsimp [P1]
        intro le sl a tmps htr
        cases htr with
        | tr_var =>
            simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
            exact Clight.eval_lvalue.eval_Evar_local _ _ _ hfind)
      (esl_var_global := by
        intro x ty b hlocal hglobal
        dsimp [P1]
        intro le sl a tmps htr
        cases htr with
        | tr_var =>
            simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
            apply Clight.eval_lvalue.eval_Evar_global _ _ _ hlocal
            have hs := symbols_preserved
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) p tp hmatch
              (show CompCert4Lean.Common.AST.ident from x)
            rw [hs]
            exact hglobal)
      (esl_deref := by
        intro r ty b ofs heval ih
        dsimp [P1]
        intro le sl a tmps htr
        cases htr with
        | tr_deref le dst ty' sl1 a1 tmp h1 =>
          have hi := ih le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · simp only [Csyntax.typeof]
              exact (typeof_Ederef' _ _).symm
            · apply eval_Ederef'
              exact hev)
      (esl_field_struct := by
        intro r f ty b ofs id co att delta bf heval htype hcomp hoffset ih
        dsimp [P1]
        intro le sl a tmps htr
        cases htr
        case tr_field =>
          have hi := ih le .For_val _ _ _ (by assumption)
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof _ = .Tstruct id att :=
                hty.symm.trans htype
              have hcomp' : PTree.get id (Clight.globalenv tp).genv_cenv = some co := by
                rw [henv]
                exact hcomp
              have hoffset' : field_offset (Clight.globalenv tp).genv_cenv
                  f co.co_members = .OK (delta, bf) := by
                rw [henv]
                exact hoffset
              apply Clight.eval_lvalue.eval_Efield_struct
              · exact hev
              · exact htype'
              · exact hcomp'
              · exact hoffset')
      (esl_field_union := by
        intro r f ty b ofs id co att delta bf heval htype hoffset hcomp ih
        dsimp [P1]
        intro le sl a tmps htr
        cases htr
        case tr_field =>
          have hi := ih le .For_val _ _ _ (by assumption)
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof _ = .Tunion id att :=
                hty.symm.trans htype
              have hcomp' : PTree.get id (Clight.globalenv tp).genv_cenv = some co := by
                rw [henv]
                exact hcomp
              have hoffset' : union_field_offset (Clight.globalenv tp).genv_cenv
                  f co.co_members = .OK (delta, bf) := by
                rw [henv]
                exact hoffset
              apply Clight.eval_lvalue.eval_Efield_union
              · exact hev
              · exact htype'
              · exact hcomp'
              · exact hoffset')
      (esr_val := by
        intro v ty
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_val_effect => simp
        | tr_val_value =>
            simp
            constructor
            · exact (by assumption : Clight.typeof _ = _).symm
            · apply_assumption
              intro id hid
              rfl
        | tr_val_set le sd a0 any tmp htype heval =>
            simp
            refine ⟨any, rfl, ?_, ?_⟩
            · exact heval.symm
            · apply_assumption
              intro id hid
              rfl)
      (esr_rvalof := by
        intro b ofs bf l ty v heval hty hvol hderef ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_valof le dst ty' tmp sl1 a1 tmp1 sl2 a2 tmp2 h1 h2 hdisjoint hincl1 hincl2 =>
          cases h2 with
          | tr_rvalof_nonvol =>
            have hi := ih le sl1 a tmp1 h1
            rcases hi with ⟨hsl, htype, hlval⟩
            have hd := deref_loc_translated
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) p tp hmatch
              ty m b ofs bf CompCert4Lean.Common.Events.E0 v hderef
            simp [chunk_for_volatile_type, hvol] at hd
            cases dst
            · rw [hsl]
              simp only [SimplExprspec.final, List.nil_append]
              have hta : Clight.typeof a = ty := htype.symm.trans hty.symm
              constructor
              · simp
              · constructor
                · simp only [Csyntax.typeof]
                  exact hta.symm
                · apply Clight.eval_expr.eval_Elvalue
                  · exact hlval
                  · simpa [hta] using hd
            · rw [hsl]
              simp only [SimplExprspec.final, List.nil_append]
            · rw [hsl]
              simp only [SimplExprspec.final, List.nil_append]
              refine ⟨a, rfl, ?_, ?_⟩
              · exact hty.trans htype
              · apply Clight.eval_expr.eval_Elvalue
                · exact hlval
                · have hta : Clight.typeof a = ty := htype.symm.trans hty.symm
                  simpa [hta] using hd
          | tr_rvalof_vol =>
            simp_all)
      (esr_addrof := by
        intro b ofs l ty heval ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr
        case tr_addrof =>
          have hi := ih le _ _ _ (by assumption)
          rcases hi with ⟨hsl, htype, hlval⟩
          cases dst
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            constructor
            · simp
            · constructor
              · exact (typeof_Eaddrof' _ _).symm
              · apply eval_Eaddrof'
                exact hlval
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            refine ⟨_, rfl, ?_, ?_⟩
            · exact (typeof_Eaddrof' _ _).symm
            · apply eval_Eaddrof'
              exact hlval)
      (esr_unop := by
        intro op r1 ty v1 v heval hsem ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_unop le dst op' ty' tmp sl1 a1 h1 =>
          have hi := ih le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, htype, hev⟩
          have hsem' : sem_unary_operation op v1 (Clight.typeof a1) m = some v := by
            rw [← htype]
            exact hsem
          cases dst
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            constructor
            · simp
            · constructor
              · rfl
              · apply Clight.eval_expr.unary
                · exact hev
                · exact hsem'
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · apply Clight.eval_expr.unary
              · exact hev
              · exact hsem')
      (esr_binop := by
        intro op r1 r2 ty v1 v2 v heval1 heval2 hsem ih1 ih2
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_binop le dst op' e2 ty' sl1 a1 tmp1 sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 =>
          have hi1 := ih1 le .For_val sl1 a1 tmp1 h1
          have hi2 := ih2 le .For_val sl2 a2 tmp2 h2
          rcases hi1 with ⟨hsl1, htype1, hev1⟩
          rcases hi2 with ⟨hsl2, htype2, hev2⟩
          have henv := comp_env_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
          have hsem' : sem_binary_operation (Clight.globalenv tp).genv_cenv
              op v1 (Clight.typeof a1) v2 (Clight.typeof a2) m = some v := by
            rw [henv, ← htype1, ← htype2]
            exact hsem
          cases dst
          · rw [hsl1, hsl2]
            simp only [SimplExprspec.final, List.nil_append, List.append_nil]
            constructor
            · simp
            · constructor
              · rfl
              · apply Clight.eval_expr.binary
                · exact hev1
                · exact hev2
                · exact hsem'
          · rw [hsl1, hsl2]
            simp only [SimplExprspec.final, List.nil_append, List.append_nil]
          · rw [hsl1, hsl2]
            simp only [SimplExprspec.final, List.nil_append, List.append_nil]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · apply Clight.eval_expr.binary
              · exact hev1
              · exact hev2
              · exact hsem')
      (esr_cast := by
        intro ty r1 v1 v heval hsem ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_cast_effects le ty' sl1 a1 any tmp h1 =>
          simpa using (ih le .For_effects sl a1 tmps h1)
        | tr_cast_val le dst ty' sl1 a1 tmp h1 =>
          have hi := ih le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, htype, hev⟩
          have hsem' : sem_cast v1 (Clight.typeof a1) ty m = some v := by
            rw [← htype]
            exact hsem
          cases dst
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            constructor
            · simp
            · constructor
              · rfl
              · apply Clight.eval_expr.cast
                · exact hev
                · exact hsem'
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · apply Clight.eval_expr.cast
              · exact hev
              · exact hsem')
      (esr_sizeof := by
        intro ty1 ty
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr
        case tr_sizeof =>
          have henv := comp_env_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
          cases dst
          · simp only [SimplExprspec.final]
            constructor
            · simp
            · constructor
              · rfl
              · simpa only [henv] using
                  (Clight.eval_expr.sizeof_type
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    (ge := Clight.globalenv tp)
                    (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty)
          · simp only [SimplExprspec.final]
          · simp only [SimplExprspec.final]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · simpa only [henv] using
                (Clight.eval_expr.sizeof_type
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (ge := Clight.globalenv tp)
                  (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty))
      (esr_alignof := by
        intro ty1 ty
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr
        case tr_alignof =>
          have henv := comp_env_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
          cases dst
          · simp only [SimplExprspec.final]
            constructor
            · simp
            · constructor
              · rfl
              · simpa only [henv] using
                  (Clight.eval_expr.alignof_type
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    (ge := Clight.globalenv tp)
                    (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty)
          · simp only [SimplExprspec.final]
          · simp only [SimplExprspec.final]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · simpa only [henv] using
                (Clight.eval_expr.alignof_type
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (ge := Clight.globalenv tp)
                  (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty))
      hEval
  simpa [P2] using hrec

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

theorem tr_simple_lvalue :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_lvalueStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit e m l b ofs bf hEval
  intro le sl a tmps htr
  cases hEval with
  | esl_loc =>
      cases htr
  | esl_var_local hfind =>
      cases htr with
      | tr_var =>
          simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
          exact Clight.eval_lvalue.eval_Evar_local _ _ _ hfind
  | @esl_var_global x ty b hlocal hglobal =>
      cases htr with
      | tr_var =>
          simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
          apply Clight.eval_lvalue.eval_Evar_global _ _ _ hlocal
          have hs := symbols_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            (show CompCert4Lean.Common.AST.ident from x)
          rw [hs]
          exact hglobal
  | esl_deref heval =>
      cases htr with
      | tr_deref le dst ty' sl1 a1 tmp h1 =>
          have hi := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m _ _ heval) le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, htype, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · simp only [Csyntax.typeof]
              exact (typeof_Ederef' _ _).symm
            · apply eval_Ederef'
              exact hev
  | esl_field_struct heval htype hcomp hoffset =>
      cases htr with
      | tr_field le dst f ty' sl1 a1 tmp h1 =>
          have hi := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m _ _ heval) le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof a1 = .Tstruct _ _ :=
                hty.symm.trans htype
              apply Clight.eval_lvalue.eval_Efield_struct
              · exact hev
              · exact htype'
              · rw [henv]
                exact hcomp
              · rw [henv]
                exact hoffset
  | esl_field_union heval htype hoffset hcomp =>
      cases htr with
      | tr_field le dst f ty' sl1 a1 tmp h1 =>
          have hi := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m _ _ heval) le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof a1 = .Tunion _ _ :=
                hty.symm.trans htype
              apply Clight.eval_lvalue.eval_Efield_union
              · exact hev
              · exact htype'
              · rw [henv]
                exact hcomp
              · rw [henv]
                exact hoffset

end CompCert4Lean.Cfrontend.SimplExprproof
namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

theorem tr_simple_exprlist :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_exprlistStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit le rl sl al tmps htr
  intro e m tyl vl hEval
  induction hEval generalizing sl al tmps with
  | esrl_nil =>
      cases htr
      constructor
      · rfl
      · exact Clight.eval_exprlist.nil
  | @esrl_cons r rl ty tyl v vl v' hr hcast hrest ih =>
      cases htr with
      | tr_cons x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
          have hi1 := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m r v' hr) le .For_val x3 x4 x5 x10
          have hi2 := ih x6 x7 x8 x11
          rcases hi1 with ⟨hs1, htype1, hev1⟩
          rcases hi2 with ⟨hs2, hev2⟩
          constructor
          · simp [hs1, hs2]
          · apply Clight.eval_exprlist.cons
            · exact hev1
            · rw [← htype1]
              exact hcast
            · exact hev2

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.Cop

theorem sem_cast_deterministic
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sem_cast_deterministicStatement := by
  intro v ty ty' m1 v1 m2 v2 h1 h2
  unfold sem_cast at h1 h2
  cases hclass : classify_cast ty ty' <;>
    cases v <;>
    simp [hclass] at h1 h2
  all_goals
    first
    | exact h1.symm.trans h2
    | exact h1.2.symm.trans h2.2
    | exact h1.2.2.symm.trans h2.2.2
    | rcases h1 with ⟨a, ha, h1⟩
      rcases h2 with ⟨b, hb, h2⟩
      have hab : a = b := Option.some.inj (ha.symm.trans hb)
      subst b
      exact h1.symm.trans h2

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Memory

theorem eval_simpl_expr_sound :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_simpl_expr_soundStatement := by
  intro binary64_certificate binary32_certificate tp e le m a v hEval
  let P : Clight.expr → val → Prop := fun a v =>
    match eval_simpl_expr a with
    | some v' => v' = v
    | none => True
  let P0 : Clight.expr → block → ptrofs → Ctypes.bitfield → Prop :=
    fun a _ _ _ => eval_simpl_expr a = none
  have hP : P a v := by
    refine Clight.eval_expr.rec
      (motive_1 := fun a v _ => P a v)
      (motive_2 := fun a _ _ _ _ => eval_simpl_expr a = none)
      (const_int := by intro i ty; simp [P, eval_simpl_expr])
      (const_float := by intro f ty; simp [P, eval_simpl_expr])
      (const_single := by intro f ty; simp [P, eval_simpl_expr])
      (const_long := by intro i ty; simp [P, eval_simpl_expr])
      (eval_Etempvar := by intro id ty v hfind; simp [P, eval_simpl_expr])
      (eval_Eaddrof := by intro a ty loc ofs hl ih; simp [P, eval_simpl_expr])
      (unary := by intro op a ty v1 v ha hop ih; simp [P, eval_simpl_expr])
      (binary := by
        intro op a1 a2 ty v1 v2 v ha1 ha2 hop ih1 ih2
        simp [P, eval_simpl_expr])
      (cast := by
        intro a ty v1 v ha hcast ih
        change match eval_simpl_expr (.Ecast a ty) with
          | some v' => v' = v
          | none => True
        simp only [eval_simpl_expr]
        cases h : eval_simpl_expr a with
        | none => simp [h]
        | some v' =>
            have hv : v' = v1 := by simpa [P, h] using ih
            subst v1
            cases hc : sem_cast v' (Clight.typeof a) ty Mem.empty with
            | none => simp [h, hc]
            | some v'' =>
                simp [h, hc]
                exact (sem_cast_deterministic v' (Clight.typeof a) ty m v Mem.empty v'' hcast hc).symm)
      (sizeof_type := by intro ty1 ty; simp [P, eval_simpl_expr])
      (alignof_type := by intro ty1 ty; simp [P, eval_simpl_expr])
      (eval_Elvalue := by
        intro a loc ofs bf v hl hd ih
        simp [P, ih])
      (eval_Evar_local := by intro id loc ty h; rfl)
      (eval_Evar_global := by intro id loc ty h1 h2; rfl)
      (eval_Ederef := by intro a ty loc ofs ha ih; rfl)
      (eval_Efield_struct := by
        intro a id ty loc ofs sid co att delta bf ha ht hc ho ih; rfl)
      (eval_Efield_union := by
        intro a id ty loc ofs uid co att delta bf ha ht hc ho ih; rfl)
      hEval
  simpa [P] using hP

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.Cop

private theorem empty_weak_valid_pointer_false (b : CompCert4Lean.Common.Values.block)
    (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    CompCert4Lean.Common.Memory.Mem.weak_valid_pointer
      CompCert4Lean.Common.Memory.Mem.empty b ofs = false := by
  simp [CompCert4Lean.Common.Memory.Mem.weak_valid_pointer,
    CompCert4Lean.Common.Memory.Mem.valid_pointer,
    CompCert4Lean.Common.Memory.Mem.empty,
    CompCert4Lean.Common.Memory.Mem.perm_dec,
    CompCert4Lean.Common.Memory.Mem.perm_order'_dec,
    CompCert4Lean.Lib.Maps.PMap.get,
    CompCert4Lean.Lib.Maps.PMap.init,
    CompCert4Lean.Lib.Maps.PTree.get,
    CompCert4Lean.Lib.Maps.PTree.empty]
  constructor <;> rfl

theorem static_bool_val_sound : static_bool_val_soundStatement := by
  intro v t m b h
  cases hc : classify_bool t <;>
    cases v <;>
      simp [bool_val, hc, CompCert4Lean.X86_64.Archi.ptr64] at h ⊢ <;>
    try exact h
  · rw [empty_weak_valid_pointer_false] at h
    simp at h

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem Kseqlist_app : Kseqlist_appStatement := by
  intro sl1 sl2 k
  induction sl1 with
  | nil => rfl
  | cons s sl ih => simp [Kseqlist, ih]

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem step_make_set :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_make_setStatement := by
  intro binary64_certificate binary32_certificate xi p tp hmatch
  intro id a ty m b ofs bf t v e le f k hd hl hty
  have hd' := deref_loc_translated
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp hmatch ty m b ofs bf t v hd
  unfold make_set
  cases hchunk : chunk_for_volatile_type (Clight.typeof a) bf with
  | none =>
      simp only [hchunk]
      have hnone : t = CompCert4Lean.Common.Events.E0 ∧
          Clight.deref_loc ty m b ofs bf v := by
        simpa [← hty, hchunk] using hd'
      have hde : Clight.deref_loc (Clight.typeof a) m b ofs bf v := by
        simpa [hty] using hnone.2
      rw [hnone.1]
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_set
      exact Clight.eval_Elvalue a b ofs bf v hl hde
  | some chunk =>
      simp only [hchunk]
      have hsome : bf = .Full ∧
          CompCert4Lean.Common.Events.volatile_load
            (CompCert4Lean.Common.Globalenvs.Genv.to_senv
              (Clight.globalenv tp).genv_genv)
            chunk m b ofs t v := by
        simpa [← hty, hchunk] using hd'
      rcases hsome with ⟨rfl, hload⟩
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_builtin
      · refine Clight.eval_exprlist.cons
          (a := .Eaddrof a (.Tpointer (Clight.typeof a) Ctypes.noattr))
          (rest := [])
          (ty := .Tpointer (Clight.typeof a) Ctypes.noattr)
          (types := [])
          (v1 := .Vptr b ofs) (v2 := .Vptr b ofs) (values := []) ?_ ?_
          Clight.eval_exprlist.nil
        · exact Clight.eval_Eaddrof a
            (.Tpointer (Clight.typeof a) Ctypes.noattr) b ofs hl
        · simp [Cop.sem_cast, Cop.classify_cast, Clight.typeof,
            CompCert4Lean.X86_64.Archi.ptr64]
      · exact CompCert4Lean.Common.Events.volatile_load_sem_intro _ _ _ _ _ hload

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem step_make_assign :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_make_assignStatement := by
  intro binary64_certificate binary32_certificate xi p tp hmatch
  intro a1 a2 ty m b ofs bf t v m' v' v2 e le f k hassign hlvalue hrvalue hcast htype
  have hassign' := assign_loc_translated
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp hmatch ty m b ofs bf v t m' v' hassign
  unfold make_assign
  cases hchunk : chunk_for_volatile_type (Clight.typeof a1) bf with
  | none =>
      simp only [hchunk]
      have hnone : t = CompCert4Lean.Common.Events.E0 ∧
          Clight.assign_loc (Clight.globalenv tp).genv_cenv ty m b ofs bf v m' := by
        simpa [← htype, hchunk] using hassign'
      rcases hnone with ⟨ht, hass⟩
      rw [ht]
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_assign
      · exact hlvalue
      · exact hrvalue
      · simpa [htype] using hcast
      · simpa [htype] using hass
  | some chunk =>
      simp only [hchunk]
      have hsome : bf = .Full ∧
          CompCert4Lean.Common.Events.volatile_store
            (CompCert4Lean.Common.Globalenvs.Genv.to_senv
              (Clight.globalenv tp).genv_genv)
            chunk m b ofs v t m' := by
        simpa [← htype, hchunk] using hassign'
      rcases hsome with ⟨rfl, hstore⟩
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_builtin
      · refine Clight.eval_exprlist.cons
          (a := .Eaddrof a1 (.Tpointer (Clight.typeof a1) Ctypes.noattr))
          (rest := [a2])
          (ty := .Tpointer (Clight.typeof a1) Ctypes.noattr)
          (types := [Clight.typeof a1])
          (v1 := .Vptr b ofs) (v2 := .Vptr b ofs) (values := [v]) ?_ ?_ ?_
        · exact Clight.eval_Eaddrof a1
            (.Tpointer (Clight.typeof a1) Ctypes.noattr) b ofs hlvalue
        · simp [Cop.sem_cast, Cop.classify_cast, Clight.typeof,
            CompCert4Lean.X86_64.Archi.ptr64]
        · refine Clight.eval_exprlist.cons
            (a := a2) (rest := [])
            (ty := Clight.typeof a1) (types := [])
            (v1 := v2) (v2 := v) (values := []) ?_ ?_
            Clight.eval_exprlist.nil
          · exact hrvalue
          · simpa [htype] using hcast
      · exact CompCert4Lean.Common.Events.volatile_store_sem_intro _ _ _ _ _ _ hstore

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events

theorem push_seq :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      push_seqStatement := by
  intro binary64_certificate binary32_certificate
  intro xi tp f sl k e le m
  have aux :
      ∀ (seed : Clight.statement) (sl : List Clight.statement) (k : Clight.cont),
        star (Clight.step1 xi) (Clight.globalenv tp)
          (Clight.State f (SimplExpr.makeseq_rec seed sl) k e le m) E0
          (Clight.State f seed (Kseqlist sl k) e le m) := by
    intro seed sl
    revert seed
    induction sl with
    | nil =>
        intro seed k
        apply star_refl
    | cons s rest ih =>
        intro seed k
        simp only [SimplExpr.makeseq_rec, Kseqlist]
        refine @CompCert4Lean.Common.Smallstep.star_right _ _ _ _ _ E0
          (Clight.State f (.Ssequence seed s) (Kseqlist rest k) e le m) E0 _ E0 ?_ ?_ ?_
        · exact ih (.Ssequence seed s) k
        · exact Clight.step.step_seq f seed s (Kseqlist rest k) e le m
        · rfl
  simpa [SimplExpr.makeseq] using aux Clight.Sskip sl k
      
end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Maps

theorem step_tr_rvalof :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_tr_rvalofStatement := by
  intro binary64_certificate binary32_certificate xi p tp hmatch
  intro cu hlink ty m b ofs bf t v e le a sl a' tmp f k hderef hlvalue htr htype
  cases htr with
  | tr_rvalof_nonvol _ hvolatile =>
      have hderef_translated := deref_loc_translated
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        p tp hmatch ty m b ofs bf t v hderef
      have hnonvol : t = CompCert4Lean.Common.Events.E0 ∧
          Clight.deref_loc ty m b ofs bf v := by
        simpa [chunk_for_volatile_type, hvolatile] using hderef_translated
      rcases hnonvol with ⟨rfl, hderef_clight⟩
      refine ⟨le, ?_, ?_, rfl, ?_⟩
      · apply star_refl
      · exact Clight.eval_expr.eval_Elvalue a b ofs bf v hlvalue
          (by simpa [htype] using hderef_clight)
      · intro x hx
        rfl
  | tr_rvalof_vol id bf' _ hvolatile htmp haccess =>
      have hbf : bf' = bf := is_bitfield_access_sound
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        p tp hmatch cu hlink e le m a b ofs bf bf' hlvalue haccess
      subst bf'
      refine ⟨PTree.set id v le, ?_, ?_, htype.symm, ?_⟩
      · simp only [Kseqlist]
        apply star_two
        · exact Clight.step_skip_seq f (make_set bf id a) k e le m
        · exact step_make_set
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi p tp hmatch id a ty m b ofs bf t v e le f k hderef hlvalue htype
        · rfl
      · exact Clight.eval_expr.eval_Etempvar id ty v (PTree.gss id v le)
      · intro x hx
        apply PTree.gso
        intro heq
        subst x
        exact hx htmp

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem match_cont_is_call_cont :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      match_cont_is_call_contStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp ce k tk hmatch hcall ce'
  cases hmatch <;> simp [Csem.is_call_cont] at hcall ⊢ <;>
    try contradiction
  all_goals
    constructor <;> assumption

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem match_cont_call_cont :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      match_cont_call_contStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp ce k tk hmatch
  induction hmatch using match_cont.rec
      (motive_2 := fun _ _ _ _ _ _ => True) with
  | match_Kstop ce =>
      intro ce'
      simp [Csem.call_cont, Clight.call_cont]
      exact match_cont.match_Kstop ce'
  | @match_Kseq ce s k ts tk hstmt hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kwhile2 ce r s k s' ts tk hr hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kdowhile1 ce r s k s' ts tk hr hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kfor3 ce r s3 s k ts3 s' ts tk hr hs3 hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kfor4 ce r s3 s k ts3 s' ts tk hr hs3 hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kswitch2 ce k tk hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kcall f e C ty k optid tf le sl tk a dest tmps cu ce hlink htrf hctx htr hmc =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using
        (match_cont.match_Kcall (prog := p) (tprog := tp)
          f e C ty k optid tf le sl tk a dest tmps cu ce'
          hlink htrf hctx htr hmc)
  | match_Kdo => exact True.intro
  | match_Kifthenelse_empty => exact True.intro
  | match_Kifthenelse_1 => exact True.intro
  | match_Kwhile1 => exact True.intro
  | match_Kdowhile2 => exact True.intro
  | match_Kfor2 => exact True.intro
  | match_Kswitch1 => exact True.intro
  | match_Kreturn => exact True.intro

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_select_switch :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_select_switchStatement := by
  intro binary64_certificate binary32_certificate ce
  have hdefault : ∀ ls tls,
      tr_lblstmts ce ls tls →
      tr_lblstmts ce (Csem.select_switch_default ls)
        (Clight.select_switch_default tls) := by
    intro ls tls htr
    induction htr using tr_lblstmts.rec
        (motive_1 := fun _ _ _ => True) <;> try trivial
    case tr_ls_nil => exact tr_lblstmts.tr_ls_nil
    case tr_ls_cons c s ls ts tls hs hls ihs ih =>
      cases c with
      | none => exact tr_lblstmts.tr_ls_cons none s ls ts tls hs hls
      | some z => exact ih
  have hcase : ∀ n ls tls,
      tr_lblstmts ce ls tls →
      match Csem.select_switch_case n ls with
      | none => Clight.select_switch_case n tls = none
      | some ls' => ∃ tls', Clight.select_switch_case n tls = some tls' ∧
          tr_lblstmts ce ls' tls' := by
    intro n ls tls htr
    induction htr using tr_lblstmts.rec
        (motive_1 := fun _ _ _ => True) <;> try trivial
    case tr_ls_cons c s ls ts tls hs hls ihs ih =>
      cases c with
      | none => exact ih
      | some z =>
          simp only [Csem.select_switch_case, Clight.select_switch_case]
          cases hz : CompCert4Lean.Lib.Coqlib.zeq z n with
          | left heq =>
              exact ⟨Clight.LScons (some z) ts tls, rfl,
                tr_lblstmts.tr_ls_cons (some z) s ls ts tls hs hls⟩
          | right hne => exact ih
  intro n ls tls htr
  unfold Csem.select_switch Clight.select_switch
  have hinfo := hcase n ls tls htr
  cases hsel : Csem.select_switch_case n ls with
  | some ls' =>
      rw [hsel] at hinfo
      rcases hinfo with ⟨tls', htls, hselected⟩
      rw [htls]
      exact hselected
  | none =>
      rw [hsel] at hinfo
      rw [hinfo]
      exact hdefault ls tls htr

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_seq_of_labeled_statement :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_seq_of_labeled_statementStatement := by
  intro binary64_certificate binary32_certificate ce ls tls htr
  induction htr using tr_lblstmts.rec
      (motive_1 := fun _ _ _ => True) <;> try trivial
  case tr_ls_nil => exact tr_stmt.tr_skip
  case tr_ls_cons c s ls ts tls hs hls ihs ih =>
    exact tr_stmt.tr_seq s (Csem.seq_of_labeled_statement ls)
      ts (Clight.seq_of_labeled_statement tls) hs ih

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

private def pgNoLabel (s : Clight.statement) : Prop :=
  ∀ lbl k, Clight.find_label lbl s k = none

private def pgNoLabelList (sl : List Clight.statement) : Prop :=
  ∀ s, s ∈ sl → pgNoLabel s

private theorem pgNoLabel_sequence {s1 s2 : Clight.statement}
    (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) :
    pgNoLabel (.Ssequence s1 s2) := by
  intro lbl k
  simp only [Clight.find_label]
  rw [h1 lbl (.Kseq s2 k)]
  exact h2 lbl k

private theorem pgNoLabel_ifthenelse {a : Clight.expr}
    {s1 s2 : Clight.statement} (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) :
    pgNoLabel (.Sifthenelse a s1 s2) := by
  intro lbl k
  simp only [Clight.find_label]
  rw [h1 lbl k]
  exact h2 lbl k

private theorem pgNoLabel_makeif
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] {a : Clight.expr}
    {s1 s2 : Clight.statement} (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) :
    pgNoLabel (SimplExpr.makeif a s1 s2) := by
  cases heval : SimplExpr.eval_simpl_expr a with
  | none =>
      simpa [SimplExpr.makeif, heval] using pgNoLabel_ifthenelse h1 h2
  | some v =>
      cases hbool : Cop.bool_val v (Clight.typeof a)
          CompCert4Lean.Common.Memory.Mem.empty with
      | none =>
          simpa [SimplExpr.makeif, heval, hbool] using pgNoLabel_ifthenelse h1 h2
      | some b =>
          cases b <;> simp [SimplExpr.makeif, heval, hbool, h1, h2]

private theorem pgNoLabel_make_set (bf : bitfield) (id : ident)
    (a : Clight.expr) : pgNoLabel (SimplExpr.make_set bf id a) := by
  unfold SimplExpr.make_set
  cases SimplExpr.chunk_for_volatile_type (Clight.typeof a) bf <;>
    intro lbl k <;> rfl

private theorem pgNoLabel_make_assign (bf : bitfield) (a1 a2 : Clight.expr) :
    pgNoLabel (SimplExpr.make_assign bf a1 a2) := by
  unfold SimplExpr.make_assign
  cases SimplExpr.chunk_for_volatile_type (Clight.typeof a1) bf <;>
    intro lbl k <;> rfl

private theorem pgNoLabelList_do_set (sd : SimplExpr.set_destination)
    (a : Clight.expr) : pgNoLabelList (SimplExpr.do_set sd a) := by
  induction sd generalizing a with
  | SDbase =>
      intro s hs
      simp only [SimplExpr.do_set, List.mem_singleton] at hs
      subst s
      intro lbl k
      rfl
  | SDcons tycast ty tmp sd ih =>
      intro s hs
      simp only [SimplExpr.do_set, List.mem_cons] at hs
      rcases hs with rfl | hs
      · intro lbl k
        rfl
      · exact ih _ _ hs

private theorem pgNoLabelList_final (dst : SimplExpr.destination)
    (a : Clight.expr) : pgNoLabelList (SimplExprspec.final dst a) := by
  cases dst with
  | For_val => simp [SimplExprspec.final, pgNoLabelList]
  | For_effects => simp [SimplExprspec.final, pgNoLabelList]
  | For_set sd => exact pgNoLabelList_do_set sd a

private theorem pgNoLabelList_rvalof {ce : composite_env} {ty : Ctypes.type}
    {a : Clight.expr} {sl : List Clight.statement} {a' : Clight.expr}
    {tmp : List ident} (h : SimplExprspec.tr_rvalof ce ty a sl a' tmp) :
    pgNoLabelList sl := by
  cases h with
  | tr_rvalof_nonvol => simp [pgNoLabelList]
  | tr_rvalof_vol =>
      intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact pgNoLabel_make_set _ _ _

private theorem pgNoLabel_makeseq_rec (s : Clight.statement)
    (hs : pgNoLabel s) (sl : List Clight.statement)
    (hsl : pgNoLabelList sl) : pgNoLabel (SimplExpr.makeseq_rec s sl) := by
  induction sl generalizing s with
  | nil => simpa [SimplExpr.makeseq_rec]
  | cons s' sl ih =>
      apply ih (.Ssequence s s') (pgNoLabel_sequence hs (hsl s' (by simp)))
      intro s'' hs''
      exact hsl s'' (by simp [hs''])

private theorem pgNoLabel_makeseq (sl : List Clight.statement)
    (hsl : pgNoLabelList sl) : pgNoLabel (SimplExpr.makeseq sl) := by
  apply pgNoLabel_makeseq_rec .Sskip
  · intro lbl k
    rfl
  · exact hsl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

private theorem pgNoLabel_skip : pgNoLabel Clight.Sskip := by
  intro lbl k
  rfl

private theorem pgNoLabel_assign (a1 a2 : Clight.expr) :
    pgNoLabel (.Sassign a1 a2) := by
  intro lbl k
  rfl

private theorem pgNoLabel_set (id : ident) (a : Clight.expr) :
    pgNoLabel (.Sset id a) := by
  intro lbl k
  rfl

private theorem pgNoLabel_call (id : Option ident) (a : Clight.expr)
    (args : List Clight.expr) : pgNoLabel (.Scall id a args) := by
  intro lbl k
  rfl

private theorem pgNoLabel_builtin (id : Option ident)
    (ef : CompCert4Lean.Common.AST.external_function) (tys : List Ctypes.type)
    (args : List Clight.expr) : pgNoLabel (.Sbuiltin id ef tys args) := by
  intro lbl k
  rfl

private theorem pgNoLabelList_nil : pgNoLabelList [] := by
  intro s hs
  simp at hs

private theorem pgNoLabelList_cons (s : Clight.statement)
    (sl : List Clight.statement) :
    pgNoLabelList (s :: sl) ↔ pgNoLabel s ∧ pgNoLabelList sl := by
  constructor
  · intro h
    constructor
    · exact h s (by simp)
    · intro s' hs'
      exact h s' (by simp [hs'])
  · rintro ⟨hs, hsl⟩ s' hs'
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · exact hs
    · exact hsl s' hs'

private theorem pgNoLabelList_append (sl1 sl2 : List Clight.statement) :
    pgNoLabelList (sl1 ++ sl2) ↔ pgNoLabelList sl1 ∧ pgNoLabelList sl2 := by
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (List.mem_append_left sl2 hs)
    · intro s hs
      exact h s (List.mem_append_right sl1 hs)
  · rintro ⟨h1, h2⟩ s hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · exact h1 s hs
    · exact h2 s hs

private theorem pgTrExprNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {ce : composite_env} {le : Clight.temp_env} {dst : SimplExpr.destination}
    {r : cexpr} {sl : List Clight.statement} {a : Clight.expr}
    {tmps : List ident} (h : SimplExprspec.tr_expr ce le dst r sl a tmps) :
    pgNoLabelList sl := by
  let P1 := fun (_dst : SimplExpr.destination) (_r : cexpr)
      (sl : List Clight.statement) (_a : Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_expr ce le _dst _r sl _a _tmps) =>
      pgNoLabelList sl
  let P2 := fun (_rl : cexprlist) (sl : List Clight.statement)
      (_al : List Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_exprlist ce le _rl sl _al _tmps) =>
      pgNoLabelList sl
  refine SimplExprspec.tr_expr.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2] at * <;>
      simp_all [pgNoLabelList_nil, pgNoLabelList_cons,
        pgNoLabelList_append, pgNoLabelList_final, pgNoLabelList_do_set,
        pgNoLabelList_rvalof, pgNoLabel_make_assign, pgNoLabel_make_set,
        pgNoLabel_makeif, pgNoLabel_makeseq, pgNoLabel_skip,
        pgNoLabel_assign, pgNoLabel_set, pgNoLabel_call, pgNoLabel_builtin]
  all_goals
    apply pgNoLabelList_rvalof
    assumption

private theorem pgTrExprListNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {ce : composite_env} {le : Clight.temp_env} {rl : cexprlist}
    {sl : List Clight.statement} {al : List Clight.expr} {tmps : List ident}
    (h : SimplExprspec.tr_exprlist ce le rl sl al tmps) :
    pgNoLabelList sl := by
  let P1 := fun (_dst : SimplExpr.destination) (_r : cexpr)
      (sl : List Clight.statement) (_a : Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_expr ce le _dst _r sl _a _tmps) =>
      pgNoLabelList sl
  let P2 := fun (_rl : cexprlist) (sl : List Clight.statement)
      (_al : List Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_exprlist ce le _rl sl _al _tmps) =>
      pgNoLabelList sl
  refine SimplExprspec.tr_exprlist.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2] at * <;>
      simp_all [pgNoLabelList_nil, pgNoLabelList_cons,
        pgNoLabelList_append, pgNoLabelList_final, pgNoLabelList_do_set,
        pgNoLabelList_rvalof, pgNoLabel_make_assign, pgNoLabel_make_set,
        pgNoLabel_makeif, pgNoLabel_makeseq, pgNoLabel_skip,
        pgNoLabel_assign, pgNoLabel_set, pgNoLabel_call, pgNoLabel_builtin]
  all_goals
    apply pgNoLabelList_rvalof
    assumption

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

private theorem pgTrTopNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {ce : composite_env} {ge : Clight.genv} {e : Clight.env}
    {le : Clight.temp_env} {m : mem} {dst : SimplExpr.destination}
    {r : cexpr} {sl : List Clight.statement} {a : Clight.expr}
    {tmps : List ident} (h : SimplExprspec.tr_top ce ge e le m dst r sl a tmps) :
    pgNoLabelList sl := by
  cases h with
  | tr_top_val_val => exact pgNoLabelList_nil
  | tr_top_base _ _ _ _ _ htr => exact pgTrExprNoLabel htr

private theorem pgTrExpressionNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (tp : tprogram) {ce : composite_env} {r : cexpr}
    {s : Clight.statement} {a : Clight.expr}
    (h : SimplExprspec.tr_expression ce r s a) : pgNoLabel s := by
  cases h with
  | tr_expression_intro sl a tmps htop =>
      apply pgNoLabel_makeseq
      apply pgTrTopNoLabel
      exact htop (Clight.globalenv tp) Clight.empty_env
        (CompCert4Lean.Lib.Maps.PTree.empty val)
        CompCert4Lean.Common.Memory.Mem.empty

private theorem pgTrExprStmtNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (tp : tprogram) {ce : composite_env} {r : cexpr}
    {s : Clight.statement} (h : SimplExprspec.tr_expr_stmt ce r s) :
    pgNoLabel s := by
  cases h with
  | tr_expr_stmt_intro sl a tmps htop =>
      apply pgNoLabel_makeseq
      apply pgTrTopNoLabel
      exact htop (Clight.globalenv tp) Clight.empty_env
        (CompCert4Lean.Lib.Maps.PTree.empty val)
        CompCert4Lean.Common.Memory.Mem.empty

private theorem pgTrIfNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (tp : tprogram) {ce : composite_env} {r : cexpr}
    {s1 s2 ts : Clight.statement} (h : SimplExprspec.tr_if ce r s1 s2 ts)
    (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) : pgNoLabel ts := by
  cases h with
  | tr_if_intro sl a tmps htop =>
      apply pgNoLabel_makeseq
      rw [pgNoLabelList_append]
      constructor
      · apply pgTrTopNoLabel
        exact htop (Clight.globalenv tp) Clight.empty_env
          (CompCert4Lean.Lib.Maps.PTree.empty val)
          CompCert4Lean.Common.Memory.Mem.empty
      · rw [pgNoLabelList_cons]
        exact ⟨pgNoLabel_makeif h1 h2, pgNoLabelList_nil⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_find_label :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_find_labelStatement := by
  intro binary64_certificate binary32_certificate p tp ce lbl s k ts tk htr hmc
  let P1 := fun (s : cstatement)
      (ts : Clight.statement) (_ : tr_stmt ce s ts) =>
      ∀ lbl k tk, match_cont p tp ce k tk →
        match Csem.find_label lbl s k with
        | none => Clight.find_label lbl ts tk = none
        | some (s', k') =>
            ∃ ts' tk', Clight.find_label lbl ts tk = some (ts', tk') ∧
              tr_stmt ce s' ts' ∧ match_cont p tp ce k' tk'
  let P2 := fun (s : clabeled_statements)
      (ts : Clight.labeled_statements) (_ : tr_lblstmts ce s ts) =>
      ∀ lbl k tk, match_cont p tp ce k tk →
        match Csem.find_label_ls lbl s k with
        | none => Clight.find_label_ls lbl ts tk = none
        | some (s', k') =>
            ∃ ts' tk', Clight.find_label_ls lbl ts tk = some (ts', tk') ∧
              tr_stmt ce s' ts' ∧ match_cont p tp ce k' tk'
  refine (SimplExprspec.tr_stmt.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htr) lbl k tk hmc
  · intro lbl k tk hmc
    rfl
  · intro r s h lbl k tk hmc
    exact pgTrExprStmtNoLabel tp h lbl tk
  · intro s1 s2 ts1 ts2 h1 h2 ih1 ih2 lbl k tk hmc
    have hmc1 : match_cont p tp ce (Csem.Kseq s2 k) (Clight.Kseq ts2 tk) :=
      match_cont.match_Kseq ce s2 k ts2 tk h2 hmc
    have hi1 := ih1 lbl (Csem.Kseq s2 k) (Clight.Kseq ts2 tk) hmc1
    simp only [Csem.find_label, Clight.find_label]
    cases hc : Csem.find_label lbl s1 (Csem.Kseq s2 k) with
    | none =>
        rw [hc] at hi1
        rw [hi1]
        exact ih2 lbl k tk hmc
    | some sk =>
        rcases sk with ⟨s', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s' a h lbl k tk hmc
    change Clight.find_label lbl (.Ssequence s' .Sskip) tk = none
    exact pgNoLabel_sequence (pgTrExpressionNoLabel tp h) pgNoLabel_skip lbl tk
  · intro r s1 s2 s' a ts1 ts2 hr h1 h2 ih1 ih2 lbl k tk hmc
    have hpref := pgTrExpressionNoLabel tp hr
    have hi1 := ih1 lbl k tk hmc
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq (.Sifthenelse a ts1 ts2) tk)]
    simp only [Clight.find_label]
    cases hc : Csem.find_label lbl s1 k with
    | none =>
        rw [hc] at hi1
        rw [hi1]
        exact ih2 lbl k tk hmc
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s1 s' ts1 hr h1 ih1 lbl k tk hmc
    have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
    have hmc1 : match_cont p tp ce (Csem.Kwhile2 r s1 k)
        (Clight.Kloop1 (.Ssequence s' ts1) .Sskip tk) :=
      match_cont.match_Kwhile2 ce r s1 k s' ts1 tk hr h1 hmc
    have hi1 := ih1 lbl (Csem.Kwhile2 r s1 k)
      (Clight.Kloop1 (.Ssequence s' ts1) .Sskip tk) hmc1
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq ts1 (.Kloop1 (.Ssequence s' ts1) .Sskip tk))]
    cases hc : Csem.find_label lbl s1 (Csem.Kwhile2 r s1 k) with
    | none =>
        rw [hc] at hi1
        rw [hi1]
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s1 s' ts1 hr h1 ih1 lbl k tk hmc
    have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
    have hmc1 : match_cont p tp ce (Csem.Kdowhile1 r s1 k)
        (Clight.Kloop1 ts1 s' tk) :=
      match_cont.match_Kdowhile1 ce r s1 k s' ts1 tk hr h1 hmc
    have hi1 := ih1 lbl (Csem.Kdowhile1 r s1 k)
      (Clight.Kloop1 ts1 s' tk) hmc1
    simp only [Csem.find_label, Clight.find_label]
    cases hc : Csem.find_label lbl s1 (Csem.Kdowhile1 r s1 k) with
    | none =>
        rw [hc] at hi1
        rw [hi1]
        exact hpref lbl (Clight.Kloop2 ts1 s' tk)
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s3 s4 s' ts3 ts4 hr h3 h4 ih3 ih4 lbl k tk hmc
    have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
    have hmc3 : match_cont p tp ce (Csem.Kfor3 r s3 s4 k)
        (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) :=
      match_cont.match_Kfor3 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
    have hi4 := ih4 lbl (Csem.Kfor3 r s3 s4 k)
      (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) hmc3
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq ts4 (.Kloop1 (.Ssequence s' ts4) ts3 tk))]
    cases hc4 : Csem.find_label lbl s4 (Csem.Kfor3 r s3 s4 k) with
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc4] at hi4
        rcases hi4 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
    | none =>
        rw [hc4] at hi4
        rw [hi4]
        have hmc4 : match_cont p tp ce (Csem.Kfor4 r s3 s4 k)
            (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) :=
          match_cont.match_Kfor4 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
        exact ih3 lbl (Csem.Kfor4 r s3 s4 k)
          (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) hmc4
  · intro s1 r s3 s4 s' ts1 ts3 ts4 hr hnot h1 h3 h4
      ih1 ih3 ih4 lbl k tk hmc
    let loop : Clight.statement := .Sloop (.Ssequence s' ts4) ts3
    have hfor : tr_stmt ce (.Sfor .Sskip r s3 s4) loop :=
      tr_stmt.tr_for_1 r s3 s4 s' ts3 ts4 hr h3 h4
    have hmci : match_cont p tp ce
        (Csem.Kseq (.Sfor .Sskip r s3 s4) k) (Clight.Kseq loop tk) :=
      match_cont.match_Kseq ce (.Sfor .Sskip r s3 s4) k loop tk hfor hmc
    have hii := ih1 lbl (Csem.Kseq (.Sfor .Sskip r s3 s4) k)
      (Clight.Kseq loop tk) hmci
    simp only [Csem.find_label, Clight.find_label]
    cases hci : Csem.find_label lbl s1
        (Csem.Kseq (.Sfor .Sskip r s3 s4) k) with
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hci] at hii
        rcases hii with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
    | none =>
        rw [hci] at hii
        rw [hii]
        have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
        rw [hpref lbl (.Kseq ts4 (.Kloop1 (.Ssequence s' ts4) ts3 tk))]
        have hmc3 : match_cont p tp ce (Csem.Kfor3 r s3 s4 k)
            (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) :=
          match_cont.match_Kfor3 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
        have hi4 := ih4 lbl (Csem.Kfor3 r s3 s4 k)
          (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) hmc3
        cases hc4 : Csem.find_label lbl s4 (Csem.Kfor3 r s3 s4 k) with
        | some sk =>
            rcases sk with ⟨s'', k'⟩
            rw [hc4] at hi4
            rcases hi4 with ⟨ts', tk', heq, htr', hmc'⟩
            rw [heq]
            exact ⟨ts', tk', rfl, htr', hmc'⟩
        | none =>
            rw [hc4] at hi4
            rw [hi4]
            have hmc4 : match_cont p tp ce (Csem.Kfor4 r s3 s4 k)
                (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) :=
              match_cont.match_Kfor4 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
            exact ih3 lbl (Csem.Kfor4 r s3 s4 k)
              (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) hmc4
  · intro lbl k tk hmc
    rfl
  · intro lbl k tk hmc
    rfl
  · intro lbl k tk hmc
    rfl
  · intro r s' a h lbl k tk hmc
    change Clight.find_label lbl (.Ssequence s' (.Sreturn (some a))) tk = none
    exact pgNoLabel_sequence (pgTrExpressionNoLabel tp h)
      (by intro l k; rfl) lbl tk
  · intro r ls s' a tls hr hls ihls lbl k tk hmc
    have hpref := pgTrExpressionNoLabel tp hr
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq (.Sswitch a tls) tk)]
    have hmcs : match_cont p tp ce (Csem.Kswitch2 k) (Clight.Kswitch tk) :=
      match_cont.match_Kswitch2 ce k tk hmc
    exact ihls lbl (Csem.Kswitch2 k) (Clight.Kswitch tk) hmcs
  · intro label s ts h ih lbl k tk hmc
    simp only [Csem.find_label, Clight.find_label]
    cases heq : CompCert4Lean.Common.AST.ident_eq lbl label with
    | left hsame => exact ⟨ts, tk, rfl, h, hmc⟩
    | right hne => exact ih lbl k tk hmc
  · intro label lbl k tk hmc
    rfl
  · intro lbl k tk hmc
    rfl
  · intro c s ls ts tls hs hls ihs ihls lbl k tk hmc
    have hseq : tr_stmt ce (Csem.seq_of_labeled_statement ls)
        (Clight.seq_of_labeled_statement tls) :=
      tr_seq_of_labeled_statement ce ls tls hls
    have hmc1 : match_cont p tp ce
        (Csem.Kseq (Csem.seq_of_labeled_statement ls) k)
        (Clight.Kseq (Clight.seq_of_labeled_statement tls) tk) :=
      match_cont.match_Kseq ce (Csem.seq_of_labeled_statement ls) k
        (Clight.seq_of_labeled_statement tls) tk hseq hmc
    have his := ihs lbl (Csem.Kseq (Csem.seq_of_labeled_statement ls) k)
      (Clight.Kseq (Clight.seq_of_labeled_statement tls) tk) hmc1
    simp only [Csem.find_label_ls, Clight.find_label_ls]
    cases hc : Csem.find_label lbl s
        (Csem.Kseq (Csem.seq_of_labeled_statement ls) k) with
    | none =>
        rw [hc] at his
        rw [his]
        exact ihls lbl k tk hmc
    | some sk =>
        rcases sk with ⟨s', k'⟩
        rw [hc] at his
        rcases his with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem leftcontext_size : leftcontext_sizeStatement := by
  intro kfrom kto C h
  apply CompCert4Lean.Cfrontend.Cstrategy.leftcontext.rec
    (motive_1 := fun _ C _ =>
      ∀ e1 e2, esize e1 < esize e2 → esize (C e1) < esize (C e2))
    (motive_2 := fun C _ =>
      ∀ e1 e2, esize e1 < esize e2 → esizelist (C e1) < esizelist (C e2))
    (t := h)
  all_goals intros
  all_goals (try simp only [esize, esizelist] at *)
  all_goals (try assumption)
  all_goals (try apply Nat.succ_lt_succ)
  all_goals first
    | solve_by_elim
    | apply Nat.add_lt_add_left; solve_by_elim
    | apply Nat.add_lt_add_right; solve_by_elim

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem tr_val_gen :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_val_genStatement := by
  intro binary64_certificate binary32_certificate
  intro ce le dst v ty a tmp htype heval
  cases dst with
  | For_val =>
      exact SimplExprspec.tr_expr.tr_val_value le v ty a tmp htype heval
  | For_effects =>
      exact SimplExprspec.tr_expr.tr_val_effect le v ty a tmp
  | For_set sd =>
      exact SimplExprspec.tr_expr.tr_val_set le sd v ty a a tmp htype heval

end CompCert4Lean.Cfrontend.SimplExprproof
