import CompCert4Lean.Backend.RTLgen

/-!
# Relational specification of RTL generation

Definition-bearing translation of CompCert's `backend/RTLgenspec.v`.  The
proof-heavy source results are retained as exact transparent proposition
descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Backend.RTLgenspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Support
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.X86.Op

def reg_valid (r : reg) (s : RTLgen.state) : Prop :=
  Plt r s.st_nextreg

def reg_fresh (r : reg) (s : RTLgen.state) : Prop :=
  ¬Plt r s.st_nextreg

def regs_valid (rl : List reg) (s : RTLgen.state) : Prop :=
  ∀ r, r ∈ rl → reg_valid r s

def reg_in_map (m : RTLgen.mapping) (r : reg) : Prop :=
  (∃ id, PTree.get id m.map_vars = some r) ∨ r ∈ m.map_letvars

def map_valid (m : RTLgen.mapping) (s : RTLgen.state) : Prop :=
  ∀ r, reg_in_map m r → reg_valid r s

inductive target_reg_ok (map : RTLgen.mapping) (pr : List reg) : expr → reg → Prop where
  | target_reg_var (id : ident) (r : reg)
      (h : PTree.get id map.map_vars = some r) :
      target_reg_ok map pr (.Evar id) r
  | target_reg_letvar (idx : Nat) (r : reg)
      (h : nth_error map.map_letvars idx = some r) :
      target_reg_ok map pr (.Eletvar idx) r
  | target_reg_other (a : expr) (r : reg)
      (hmap : ¬reg_in_map map r) (hpr : ¬r ∈ pr) :
      target_reg_ok map pr a r

inductive target_regs_ok : RTLgen.mapping → List reg → exprlist → List reg → Prop where
  | target_regs_nil (map : RTLgen.mapping) (pr : List reg) :
      target_regs_ok map pr .Enil []
  | target_regs_cons (map : RTLgen.mapping) (pr : List reg)
      (a1 : expr) (al : exprlist) (r1 : reg) (rl : List reg)
      (hhead : target_reg_ok map pr a1 r1)
      (htail : target_regs_ok map (r1 :: pr) al rl) :
      target_regs_ok map pr (.Econs a1 al) (r1 :: rl)

inductive return_reg_ok : RTLgen.state → RTLgen.mapping → Option reg → Prop where
  | return_reg_ok_none (s : RTLgen.state) (map : RTLgen.mapping) :
      return_reg_ok s map none
  | return_reg_ok_some (s : RTLgen.state) (map : RTLgen.mapping) (r : reg)
      (hmap : ¬reg_in_map map r) (hvalid : reg_valid r s) :
      return_reg_ok s map (some r)

inductive tr_move (c : RTL.code) : RTL.node → reg → RTL.node → reg → Prop where
  | tr_move_0 (n : RTL.node) (r : reg) : tr_move c n r n r
  | tr_move_1 (ns : RTL.node) (rs : reg) (nd : RTL.node) (rd : reg)
      (h : PTree.get ns c = some (RTL.instruction.Iop Omove [rs] rd nd)) :
      tr_move c ns rs nd rd

inductive reg_map_ok : RTLgen.mapping → reg → Option ident → Prop where
  | reg_map_ok_novar (map : RTLgen.mapping) (rd : reg)
      (h : ¬reg_in_map map rd) : reg_map_ok map rd none
  | reg_map_ok_somevar (map : RTLgen.mapping) (rd : reg) (id : ident)
      (h : PTree.get id map.map_vars = some rd) : reg_map_ok map rd (some id)

mutual
  inductive tr_expr (c : RTL.code) :
      RTLgen.mapping → List reg → expr → RTL.node → RTL.node → reg → Option ident → Prop where
    | tr_Evar (map : RTLgen.mapping) (pr : List reg) (id : ident)
        (ns nd : RTL.node) (r rd : reg) (dst : Option ident)
        (hmap : PTree.get id map.map_vars = some r)
        (hok : (rd = r ∧ dst = none) ∨ (reg_map_ok map rd dst ∧ ¬rd ∈ pr))
        (hmove : tr_move c ns r nd rd) :
        tr_expr c map pr (.Evar id) ns nd rd dst
    | tr_Eop (map : RTLgen.mapping) (pr : List reg) (op : operation)
        (al : exprlist) (ns nd : RTL.node) (rd : reg) (n1 : RTL.node)
        (rl : List reg) (dst : Option ident)
        (hargs : tr_exprlist c map pr al ns n1 rl)
        (hcode : PTree.get n1 c = some (RTL.instruction.Iop op rl rd nd))
        (hmap : reg_map_ok map rd dst) (hpr : ¬rd ∈ pr) :
        tr_expr c map pr (.Eop op al) ns nd rd dst
    | tr_Eload (map : RTLgen.mapping) (pr : List reg) (chunk : memory_chunk)
        (addr : addressing) (al : exprlist) (ns nd : RTL.node) (rd : reg) (n1 : RTL.node)
        (rl : List reg) (dst : Option ident)
        (hargs : tr_exprlist c map pr al ns n1 rl)
        (hcode : PTree.get n1 c = some (RTL.instruction.Iload chunk addr rl rd nd))
        (hmap : reg_map_ok map rd dst) (hpr : ¬rd ∈ pr) :
        tr_expr c map pr (.Eload chunk addr al) ns nd rd dst
    | tr_Econdition (map : RTLgen.mapping) (pr : List reg) (a : condexpr) (ifso ifnot : expr)
        (ns nd : RTL.node) (rd : reg) (ntrue nfalse : RTL.node) (dst : Option ident)
        (hcond : tr_condition c map pr a ns ntrue nfalse)
        (htrue : tr_expr c map pr ifso ntrue nd rd dst)
        (hfalse : tr_expr c map pr ifnot nfalse nd rd dst) :
        tr_expr c map pr (.Econdition a ifso ifnot) ns nd rd dst
    | tr_Elet (map : RTLgen.mapping) (pr : List reg) (b1 b2 : expr)
        (ns nd : RTL.node) (rd : reg) (n1 : RTL.node) (r : reg) (dst : Option ident)
        (hfresh : ¬reg_in_map map r)
        (hbound : tr_expr c map pr b1 ns n1 r none)
        (hbody : tr_expr c (RTLgen.add_letvar map r) pr b2 n1 nd rd dst) :
        tr_expr c map pr (.Elet b1 b2) ns nd rd dst
    | tr_Eletvar (map : RTLgen.mapping) (pr : List reg) (n : Nat)
        (ns nd : RTL.node) (rd r : reg) (dst : Option ident)
        (hlet : nth_error map.map_letvars n = some r)
        (hok : (rd = r ∧ dst = none) ∨ (reg_map_ok map rd dst ∧ ¬rd ∈ pr))
        (hmove : tr_move c ns r nd rd) :
        tr_expr c map pr (.Eletvar n) ns nd rd dst
    | tr_Ebuiltin (map : RTLgen.mapping) (pr : List reg) (ef : external_function)
        (al : exprlist) (ns nd : RTL.node) (rd : reg) (dst : Option ident)
        (n1 : RTL.node) (rl : List reg)
        (hargs : tr_exprlist c map pr al ns n1 rl)
        (hcode : PTree.get n1 c = some (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd))
        (hmap : reg_map_ok map rd dst) (hpr : ¬rd ∈ pr) :
        tr_expr c map pr (.Ebuiltin ef al) ns nd rd dst
    | tr_Eexternal (map : RTLgen.mapping) (pr : List reg) (id : ident)
        (sg : signature) (al : exprlist) (ns nd : RTL.node)
        (rd : reg) (dst : Option ident) (n1 : RTL.node) (rl : List reg)
        (hargs : tr_exprlist c map pr al ns n1 rl)
        (hcode : PTree.get n1 c = some (RTL.instruction.Icall sg (.inr id) rl rd nd))
        (hmap : reg_map_ok map rd dst) (hpr : ¬rd ∈ pr) :
        tr_expr c map pr (.Eexternal id sg al) ns nd rd dst

  inductive tr_condition (c : RTL.code) :
      RTLgen.mapping → List reg → condexpr → RTL.node → RTL.node → RTL.node → Prop where
    | tr_CEcond (map : RTLgen.mapping) (pr : List reg) (cond : condition)
        (bl : exprlist) (ns ntrue nfalse n1 : RTL.node) (rl : List reg)
        (hargs : tr_exprlist c map pr bl ns n1 rl)
        (hcode : PTree.get n1 c = some (RTL.instruction.Icond cond rl ntrue nfalse)) :
        tr_condition c map pr (.CEcond cond bl) ns ntrue nfalse
    | tr_CEcondition (map : RTLgen.mapping) (pr : List reg)
        (a1 a2 a3 : condexpr) (ns ntrue nfalse n2 n3 : RTL.node)
        (h1 : tr_condition c map pr a1 ns n2 n3)
        (h2 : tr_condition c map pr a2 n2 ntrue nfalse)
        (h3 : tr_condition c map pr a3 n3 ntrue nfalse) :
        tr_condition c map pr (.CEcondition a1 a2 a3) ns ntrue nfalse
    | tr_CElet (map : RTLgen.mapping) (pr : List reg) (a : expr) (b : condexpr)
        (ns ntrue nfalse : RTL.node) (r : reg) (n1 : RTL.node)
        (hfresh : ¬reg_in_map map r)
        (hbound : tr_expr c map pr a ns n1 r none)
        (hbody : tr_condition c (RTLgen.add_letvar map r) pr b n1 ntrue nfalse) :
        tr_condition c map pr (.CElet a b) ns ntrue nfalse

  inductive tr_exprlist (c : RTL.code) :
      RTLgen.mapping → List reg → exprlist → RTL.node → RTL.node → List reg → Prop where
    | tr_Enil (map : RTLgen.mapping) (pr : List reg) (n : RTL.node) :
        tr_exprlist c map pr .Enil n n []
    | tr_Econs (map : RTLgen.mapping) (pr : List reg) (a1 : expr) (al : exprlist)
        (ns nd : RTL.node) (r1 : reg) (rl : List reg) (n1 : RTL.node)
        (hhead : tr_expr c map pr a1 ns n1 r1 none)
        (htail : tr_exprlist c map (r1 :: pr) al n1 nd rl) :
        tr_exprlist c map pr (.Econs a1 al) ns nd (r1 :: rl)
end

def tr_jumptable (nexits : List RTL.node) (tbl : List Nat) (ttbl : List RTL.node) : Prop :=
  ∀ (v : Z) (act : Nat),
    list_nth_z tbl v = some act →
      ∃ n, list_nth_z ttbl v = some n ∧ nth_error nexits act = some n

inductive tr_exitexpr (c : RTL.code) :
    RTLgen.mapping → exitexpr → RTL.node → List RTL.node → Prop where
  | tr_XEcond (map : RTLgen.mapping) (x : Nat) (n : RTL.node) (nexits : List RTL.node)
      (h : nth_error nexits x = some n) :
      tr_exitexpr c map (.XEexit x) n nexits
  | tr_XEjumptable (map : RTLgen.mapping) (a : expr) (tbl : List Nat)
      (ns : RTL.node) (nexits : List RTL.node) (n1 : RTL.node) (r : reg)
      (tbl' : List RTL.node)
      (hjt : tr_jumptable nexits tbl tbl')
      (harg : tr_expr c map [] a ns n1 r none)
      (hcode : PTree.get n1 c = some (RTL.instruction.Ijumptable r tbl')) :
      tr_exitexpr c map (.XEjumptable a tbl) ns nexits
  | tr_XEcondition (map : RTLgen.mapping) (a1 : condexpr) (a2 a3 : exitexpr)
      (ns : RTL.node) (nexits : List RTL.node) (n2 n3 : RTL.node)
      (hcond : tr_condition c map [] a1 ns n2 n3)
      (h2 : tr_exitexpr c map a2 n2 nexits)
      (h3 : tr_exitexpr c map a3 n3 nexits) :
      tr_exitexpr c map (.XEcondition a1 a2 a3) ns nexits
  | tr_XElet (map : RTLgen.mapping) (a : expr) (b : exitexpr)
      (ns : RTL.node) (nexits : List RTL.node) (r : reg) (n1 : RTL.node)
      (hfresh : ¬reg_in_map map r)
      (hbound : tr_expr c map [] a ns n1 r none)
      (hbody : tr_exitexpr c (RTLgen.add_letvar map r) b n1 nexits) :
      tr_exitexpr c map (.XElet a b) ns nexits

inductive tr_builtin_res : RTLgen.mapping → builtin_res ident → builtin_res reg → Prop where
  | tr_builtin_res_var (map : RTLgen.mapping) (id : ident) (r : reg)
      (h : PTree.get id map.map_vars = some r) :
      tr_builtin_res map (.BR id) (.BR r)
  | tr_builtin_res_none (map : RTLgen.mapping) :
      tr_builtin_res map .BR_none .BR_none
  | tr_builtin_res_fresh (map : RTLgen.mapping) (r : reg)
      (h : ¬reg_in_map map r) :
      tr_builtin_res map .BR_none (.BR r)

inductive tr_stmt (c : RTL.code) (map : RTLgen.mapping) :
    stmt → RTL.node → RTL.node → List RTL.node → RTLgen.labelmap → RTL.node → Option reg → Prop where
  | tr_Sskip (ns : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) :
      tr_stmt c map .Sskip ns ns nexits ngoto nret rret
  | tr_Sassign (id : ident) (a : expr) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg) (r : reg)
      (hmap : PTree.get id map.map_vars = some r)
      (harg : tr_expr c map [] a ns nd r (some id)) :
      tr_stmt c map (.Sassign id a) ns nd nexits ngoto nret rret
  | tr_Sstore (chunk : memory_chunk) (addr : addressing) (al : exprlist) (b : expr)
      (ns nd : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) (rd : reg) (n1 : RTL.node) (rl : List reg)
      (n2 : RTL.node)
      (hargs : tr_exprlist c map [] al ns n1 rl)
      (hvalue : tr_expr c map rl b n1 n2 rd none)
      (hcode : PTree.get n2 c = some (RTL.instruction.Istore chunk addr rl rd nd)) :
      tr_stmt c map (.Sstore chunk addr al b) ns nd nexits ngoto nret rret
  | tr_Scall (optid : Option ident) (sig : signature) (b : expr) (cl : exprlist)
      (ns nd : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) (rd : reg) (n1 : RTL.node) (rf : reg) (n2 : RTL.node)
      (rargs : List reg)
      (hcallee : tr_expr c map [] b ns n1 rf none)
      (hargs : tr_exprlist c map [rf] cl n1 n2 rargs)
      (hcode : PTree.get n2 c = some (RTL.instruction.Icall sig (.inl rf) rargs rd nd))
      (hmap : reg_map_ok map rd optid) :
      tr_stmt c map (.Scall optid sig (.inl b) cl) ns nd nexits ngoto nret rret
  | tr_Scall_imm (optid : Option ident) (sig : signature) (id : ident) (cl : exprlist)
      (ns nd : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) (rd : reg) (n2 : RTL.node) (rargs : List reg)
      (hargs : tr_exprlist c map [] cl ns n2 rargs)
      (hcode : PTree.get n2 c = some (RTL.instruction.Icall sig (.inr id) rargs rd nd))
      (hmap : reg_map_ok map rd optid) :
      tr_stmt c map (.Scall optid sig (.inr id) cl) ns nd nexits ngoto nret rret
  | tr_Stailcall (sig : signature) (b : expr) (cl : exprlist)
      (ns nd : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) (n1 : RTL.node) (rf : reg) (n2 : RTL.node)
      (rargs : List reg)
      (hcallee : tr_expr c map [] b ns n1 rf none)
      (hargs : tr_exprlist c map [rf] cl n1 n2 rargs)
      (hcode : PTree.get n2 c = some (RTL.instruction.Itailcall sig (.inl rf) rargs)) :
      tr_stmt c map (.Stailcall sig (.inl b) cl) ns nd nexits ngoto nret rret
  | tr_Stailcall_imm (sig : signature) (id : ident) (cl : exprlist)
      (ns nd : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) (n2 : RTL.node) (rargs : List reg)
      (hargs : tr_exprlist c map [] cl ns n2 rargs)
      (hcode : PTree.get n2 c = some (RTL.instruction.Itailcall sig (.inr id) rargs)) :
      tr_stmt c map (.Stailcall sig (.inr id) cl) ns nd nexits ngoto nret rret
  | tr_Sbuiltin (res : builtin_res ident) (ef : external_function)
      (args : List (builtin_arg expr)) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg)
      (res' : builtin_res reg) (n1 : RTL.node) (rargs : List reg)
      (hargs : tr_exprlist c map [] (RTLgen.exprlist_of_expr_list (params_of_builtin_args args)) ns n1 rargs)
      (hcode : PTree.get n1 c = some (RTL.instruction.Ibuiltin ef (RTLgen.convert_builtin_args args rargs) res' nd))
      (hres : tr_builtin_res map res res') :
      tr_stmt c map (.Sbuiltin res ef args) ns nd nexits ngoto nret rret
  | tr_Sseq (s1 s2 : stmt) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg) (n : RTL.node)
      (h2 : tr_stmt c map s2 n nd nexits ngoto nret rret)
      (h1 : tr_stmt c map s1 ns n nexits ngoto nret rret) :
      tr_stmt c map (.Sseq s1 s2) ns nd nexits ngoto nret rret
  | tr_Sifthenelse (a : condexpr) (strue sfalse : stmt)
      (ns nd : RTL.node) (nexits : List RTL.node) (ngoto : RTLgen.labelmap)
      (nret : RTL.node) (rret : Option reg) (ntrue nfalse : RTL.node)
      (htrue : tr_stmt c map strue ntrue nd nexits ngoto nret rret)
      (hfalse : tr_stmt c map sfalse nfalse nd nexits ngoto nret rret)
      (hcond : tr_condition c map [] a ns ntrue nfalse) :
      tr_stmt c map (.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
  | tr_Sloop (sbody : stmt) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg) (nloop nend : RTL.node)
      (hbody : tr_stmt c map sbody nloop nend nexits ngoto nret rret)
      (hstart : PTree.get ns c = some (RTL.instruction.Inop nloop))
      (hend : PTree.get nend c = some (RTL.instruction.Inop nloop)) :
      tr_stmt c map (.Sloop sbody) ns nd nexits ngoto nret rret
  | tr_Sblock (sbody : stmt) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg)
      (hbody : tr_stmt c map sbody ns nd (nd :: nexits) ngoto nret rret) :
      tr_stmt c map (.Sblock sbody) ns nd nexits ngoto nret rret
  | tr_Sexit (n : Nat) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg)
      (h : nth_error nexits n = some ns) :
      tr_stmt c map (.Sexit n) ns nd nexits ngoto nret rret
  | tr_Sswitch (a : exitexpr) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg)
      (h : tr_exitexpr c map a ns nexits) :
      tr_stmt c map (.Sswitch a) ns nd nexits ngoto nret rret
  | tr_Sreturn_none (nret nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (rret : Option reg) :
      tr_stmt c map (.Sreturn none) nret nd nexits ngoto nret rret
  | tr_Sreturn_some (a : expr) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : reg)
      (h : tr_expr c map [] a ns nret rret none) :
      tr_stmt c map (.Sreturn (some a)) ns nd nexits ngoto nret (some rret)
  | tr_Slabel (lbl : ident) (s : stmt) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg) (n : RTL.node)
      (hgoto : PTree.get lbl ngoto = some n)
      (hcode : PTree.get n c = some (RTL.instruction.Inop ns))
      (hbody : tr_stmt c map s ns nd nexits ngoto nret rret) :
      tr_stmt c map (.Slabel lbl s) ns nd nexits ngoto nret rret
  | tr_Sgoto (lbl : ident) (ns nd : RTL.node) (nexits : List RTL.node)
      (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg)
      (h : PTree.get lbl ngoto = some ns) :
      tr_stmt c map (.Sgoto lbl) ns nd nexits ngoto nret rret

export tr_stmt (tr_Sassign)

inductive tr_function : CminorSel.function → RTL.function → Prop where
  | tr_function_intro (f : CminorSel.function) (c : RTL.code)
      (rparams : List reg) (map1 : RTLgen.mapping)
      (s0 s1 : RTLgen.state) (i1 : state_incr s0 s1)
      (rvars : List reg) (map2 : RTLgen.mapping)
      (s2 : RTLgen.state) (i2 : state_incr s1 s2)
      (nentry : RTL.node) (ngoto : RTLgen.labelmap) (nret : RTL.node)
      (rret : reg) (orret : Option reg)
      (hparams : RTLgen.add_vars RTLgen.init_mapping f.fn_params s0 =
        .OK (rparams, map1) s1 i1)
      (hvars : RTLgen.add_vars map1 f.fn_vars s1 = .OK (rvars, map2) s2 i2)
      (hret : orret = RTLgen.ret_reg f.fn_sig rret)
      (hstmt : tr_stmt c map2 f.fn_body nentry nret [] ngoto nret orret)
      (hcode : PTree.get nret c = some (RTL.instruction.Ireturn orret)) :
      tr_function f
        { fn_sig := f.fn_sig
          fn_params := rparams
          fn_stacksize := f.fn_stackspace
          fn_code := c
          fn_entrypoint := nentry }

export tr_function (tr_function_intro)

def add_letvar_validStatement : Prop :=
  ∀ (map : RTLgen.mapping) (s : RTLgen.state) (r : reg),
    map_valid map s → reg_valid r s → map_valid (RTLgen.add_letvar map r) s

def add_move_charactStatement : Prop :=
  ∀ (s : RTLgen.state) (ns : RTL.node) (rs : reg) (nd : RTL.node) (rd : reg)
    (s' : RTLgen.state) (i : state_incr s s'),
    RTLgen.add_move rs rd nd s = .OK ns s' i →
      tr_move s'.st_code ns rs nd rd

def add_var_validStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state) (map1 map2 : RTLgen.mapping) (name : ident)
    (r : reg) (i : state_incr s1 s2),
    RTLgen.add_var map1 name s1 = .OK (r, map2) s2 i →
      map_valid map1 s1 → reg_valid r s2 ∧ map_valid map2 s2

def add_vars_validStatement : Prop :=
  ∀ (namel : List ident) (s1 s2 : RTLgen.state) (map1 map2 : RTLgen.mapping)
    (rl : List reg) (i : state_incr s1 s2),
    RTLgen.add_vars map1 namel s1 = .OK (rl, map2) s2 i →
      map_valid map1 s1 → regs_valid rl s2 ∧ map_valid map2 s2

def alloc_optreg_map_okStatement : Prop :=
  ∀ (map : RTLgen.mapping) (optid : Option ident) (s1 : RTLgen.state)
    (r : reg) (s2 : RTLgen.state) (i : state_incr s1 s2),
    map_valid map s1 → RTLgen.alloc_optreg map optid s1 = .OK r s2 i →
      reg_map_ok map r optid

def alloc_reg_target_okStatement : Prop :=
  ∀ (map : RTLgen.mapping) (pr : List reg) (s1 : RTLgen.state)
    (a : expr) (r : reg) (s2 : RTLgen.state) (i : state_incr s1 s2),
    map_valid map s1 → regs_valid pr s1 →
      RTLgen.alloc_reg map a s1 = .OK r s2 i → target_reg_ok map pr a r

def alloc_regs_target_okStatement : Prop :=
  ∀ (map : RTLgen.mapping) (al : exprlist) (pr : List reg)
    (s1 : RTLgen.state) (rl : List reg) (s2 : RTLgen.state) (i : state_incr s1 s2),
    map_valid map s1 → regs_valid pr s1 →
      RTLgen.alloc_regs map al s1 = .OK rl s2 i → target_regs_ok map pr al rl

def convert_builtin_res_charactStatement : Prop :=
  ∀ (map : RTLgen.mapping) (oty : xtype) (res : builtin_res ident)
    (s : RTLgen.state) (res' : builtin_res reg) (s' : RTLgen.state)
    (i : state_incr s s'),
    RTLgen.convert_builtin_res map oty res s = .OK res' s' i →
      map_valid map s → tr_builtin_res map res res'

def init_mapping_validStatement : Prop :=
  ∀ s : RTLgen.state, map_valid RTLgen.init_mapping s

def instr_at_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state) (n : RTL.node) (i : RTL.instruction),
    state_incr s1 s2 → PTree.get n s1.st_code = some i → PTree.get n s2.st_code = some i

def new_reg_not_in_mapStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state) (m : RTLgen.mapping) (r : reg) (i : state_incr s1 s2),
    RTLgen.new_reg s1 = .OK r s2 i → map_valid m s1 → ¬reg_in_map m r

def new_reg_target_okStatement : Prop :=
  ∀ (map : RTLgen.mapping) (pr : List reg) (s1 : RTLgen.state)
    (a : expr) (r : reg) (s2 : RTLgen.state) (i : state_incr s1 s2),
    map_valid map s1 → regs_valid pr s1 → RTLgen.new_reg s1 = .OK r s2 i →
      target_reg_ok map pr a r

def reg_fresh_decrStatement : Prop :=
  ∀ (r : reg) (s1 s2 : RTLgen.state),
    state_incr s1 s2 → reg_fresh r s2 → reg_fresh r s1

def reg_valid_incrStatement : Prop :=
  ∀ (r : reg) (s1 s2 : RTLgen.state),
    state_incr s1 s2 → reg_valid r s1 → reg_valid r s2

def regs_valid_consStatement : Prop :=
  ∀ (r1 : reg) (rl : List reg) (s : RTLgen.state),
    reg_valid r1 s → regs_valid rl s → regs_valid (r1 :: rl) s

def regs_valid_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state) (rl : List reg),
    state_incr s1 s2 → regs_valid rl s1 → regs_valid rl s2

def tr_condition_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state), state_incr s1 s2 →
    ∀ (map : RTLgen.mapping) (pr : List reg) (a : condexpr)
      (ns ntrue nfalse : RTL.node),
      tr_condition s1.st_code map pr a ns ntrue nfalse →
        tr_condition s2.st_code map pr a ns ntrue nfalse

def tr_exitexpr_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state), state_incr s1 s2 →
    ∀ (map : RTLgen.mapping) (a : exitexpr) (ns : RTL.node) (nexits : List RTL.node),
      tr_exitexpr s1.st_code map a ns nexits → tr_exitexpr s2.st_code map a ns nexits

def tr_expr_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state), state_incr s1 s2 →
    ∀ (map : RTLgen.mapping) (pr : List reg) (a : expr)
      (ns nd : RTL.node) (rd : reg) (dst : Option ident),
      tr_expr s1.st_code map pr a ns nd rd dst → tr_expr s2.st_code map pr a ns nd rd dst

def tr_exprlist_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state), state_incr s1 s2 →
    ∀ (map : RTLgen.mapping) (pr : List reg) (al : exprlist)
      (ns nd : RTL.node) (rl : List reg),
      tr_exprlist s1.st_code map pr al ns nd rl → tr_exprlist s2.st_code map pr al ns nd rl

def tr_move_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state), state_incr s1 s2 →
    ∀ (ns : RTL.node) (rs : reg) (nd : RTL.node) (rd : reg),
      tr_move s1.st_code ns rs nd rd → tr_move s2.st_code ns rs nd rd

def tr_stmt_incrStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state), state_incr s1 s2 →
    ∀ (map : RTLgen.mapping) (s : stmt) (ns nd : RTL.node)
      (nexits : List RTL.node) (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg),
      tr_stmt s1.st_code map s ns nd nexits ngoto nret rret →
        tr_stmt s2.st_code map s ns nd nexits ngoto nret rret

def transl_condexpr_charactStatement : Prop :=
  ∀ (a : condexpr) (map : RTLgen.mapping) (ntrue nfalse : RTL.node)
    (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (pr : List reg)
    (INCR : state_incr s s'),
    RTLgen.transl_condexpr map a ntrue nfalse s = .OK ns s' INCR →
      map_valid map s → regs_valid pr s → tr_condition s'.st_code map pr a ns ntrue nfalse

def transl_exit_charactStatement : Prop :=
  ∀ (nexits : List RTL.node) (n : Nat) (s : RTLgen.state)
    (ne : RTL.node) (s' : RTLgen.state) (incr : state_incr s s'),
    RTLgen.transl_exit nexits n s = .OK ne s' incr →
      nth_error nexits n = some ne ∧ s' = s

def transl_exitexpr_charactStatement : Prop :=
  ∀ (nexits : List RTL.node) (a : exitexpr) (map : RTLgen.mapping)
    (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (INCR : state_incr s s'),
    RTLgen.transl_exitexpr map a nexits s = .OK ns s' INCR →
      map_valid map s → tr_exitexpr s'.st_code map a ns nexits

def transl_expr_assign_charactStatement : Prop :=
  ∀ (id : ident) (a : expr) (map : RTLgen.mapping) (rd : reg) (nd : RTL.node)
    (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (INCR : state_incr s s'),
    RTLgen.transl_expr map a rd nd s = .OK ns s' INCR →
      map_valid map s → reg_map_ok map rd (some id) →
        tr_expr s'.st_code map [] a ns nd rd (some id)

def transl_expr_charactStatement : Prop :=
  ∀ (a : expr) (map : RTLgen.mapping) (rd : reg) (nd : RTL.node)
    (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (pr : List reg)
    (INCR : state_incr s s'),
    RTLgen.transl_expr map a rd nd s = .OK ns s' INCR →
      map_valid map s → target_reg_ok map pr a rd → regs_valid pr s → reg_valid rd s →
        tr_expr s'.st_code map pr a ns nd rd none

def transl_exprlist_charactStatement : Prop :=
  ∀ (al : exprlist) (map : RTLgen.mapping) (rl : List reg) (nd : RTL.node)
    (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (pr : List reg)
    (INCR : state_incr s s'),
    RTLgen.transl_exprlist map al rl nd s = .OK ns s' INCR →
      map_valid map s → target_regs_ok map pr al rl → regs_valid pr s → regs_valid rl s →
        tr_exprlist s'.st_code map pr al ns nd rl

def transl_function_charactStatement : Prop :=
  ∀ (f : CminorSel.function) (tf : RTL.function),
    RTLgen.transl_function f = CompCert4Lean.Common.Errors.OK tf → tr_function f tf

def transl_jumptable_charactStatement : Prop :=
  ∀ (nexits : List RTL.node) (tbl : List Nat) (s : RTLgen.state)
    (nl : List RTL.node) (s' : RTLgen.state) (incr : state_incr s s'),
    RTLgen.transl_jumptable nexits tbl s = .OK nl s' incr →
      tr_jumptable nexits tbl nl ∧ s' = s

def transl_stmt_charactStatement : Prop :=
  ∀ (map : RTLgen.mapping) (stmt : CminorSel.stmt) (nd : RTL.node)
    (nexits : List RTL.node) (ngoto : RTLgen.labelmap) (nret : RTL.node) (rret : Option reg)
    (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (INCR : state_incr s s'),
    RTLgen.transl_stmt map stmt nd nexits ngoto nret rret s = .OK ns s' INCR →
      map_valid map s → return_reg_ok s map rret →
        tr_stmt s'.st_code map stmt ns nd nexits ngoto nret rret

def valid_fresh_absurdStatement : Prop :=
  ∀ (r : reg) (s : RTLgen.state), reg_valid r s → reg_fresh r s → False

def valid_fresh_differentStatement : Prop :=
  ∀ (r1 r2 : reg) (s : RTLgen.state), reg_valid r1 s → reg_fresh r2 s → r1 ≠ r2

end CompCert4Lean.Backend.RTLgenspec

namespace CompCert4Lean.Backend.RTLgenspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

theorem instr_at_incr : instr_at_incrStatement := by
  intro s1 s2 n i hin hget
  cases hin with
  | state_incr_intro _ _ hcode =>
      rcases hcode n with hnone | heq
      · have hcontra : (some i : Option RTL.instruction) = none := by
          rw [← hget]
          exact hnone
        exact False.elim ((Option.some_ne_none i) hcontra)
      · calc
          CompCert4Lean.Lib.Maps.PTree.get n s2.st_code =
            CompCert4Lean.Lib.Maps.PTree.get n s1.st_code := heq
          _ = some i := hget

theorem valid_fresh_absurd : valid_fresh_absurdStatement := by
  intro r s hvalid hfresh
  exact hfresh hvalid

theorem valid_fresh_different : valid_fresh_differentStatement := by
  intro r1 r2 s hvalid hfresh heq
  subst r2
  exact hfresh hvalid

theorem reg_valid_incr : reg_valid_incrStatement := by
  intro r s1 s2 hin hvalid
  cases hin with
  | state_incr_intro _ hnextreg _ =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat r <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg at hvalid
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s2.st_nextreg at hnextreg
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat r <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s2.st_nextreg
      exact Nat.lt_of_lt_of_le hvalid hnextreg

end CompCert4Lean.Backend.RTLgenspec
