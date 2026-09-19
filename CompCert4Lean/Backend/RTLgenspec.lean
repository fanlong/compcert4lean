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

theorem reg_fresh_decr : reg_fresh_decrStatement := by
  intro r s1 s2 hin hfresh hvalid
  cases hin with
  | state_incr_intro _ hnextreg _ =>
      apply hfresh
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat r <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg at hvalid
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s2.st_nextreg at hnextreg
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat r <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s2.st_nextreg
      exact Nat.lt_of_lt_of_le hvalid hnextreg

theorem regs_valid_cons : regs_valid_consStatement := by
  intro r1 rl s hvalid hrl r hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with heq | htail
  · subst r
    exact hvalid
  · exact hrl r htail

theorem regs_valid_incr : regs_valid_incrStatement := by
  intro s1 s2 rl hin hvalid r hmem
  exact reg_valid_incr r s1 s2 hin (hvalid r hmem)

theorem new_reg_not_in_map : new_reg_not_in_mapStatement := by
  intro s1 s2 m r i hnew hmap hin
  simp only [RTLgen.new_reg] at hnew
  injection hnew with hr hs
  rw [← hr] at hin
  have hvalid := hmap _ hin
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg at hvalid
  exact Nat.lt_irrefl _ hvalid

end CompCert4Lean.Backend.RTLgenspec

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

private theorem rtlgenspec_add_var_valid_map
    (s1 s2 : RTLgen.state) (map mapPrime : RTLgen.mapping) (name : ident) (r : reg)
    (i : RTLgen.state_incr s1 s2) :
    RTLgen.add_var map name s1 = .OK (r, mapPrime) s2 i →
    map_valid map s1 → map_valid mapPrime s2 := by
  intro h hvalid
  cases map with
  | mk mapVars mapLetvars =>
    unfold PTree.t at mapVars
    unfold CompCert4Lean.Common.AST.ident at name
    unfold CompCert4Lean.Backend.Registers.reg at *
    change RTLgen.bind RTLgen.new_reg
      (fun r => RTLgen.ret (r,
        ({ map_vars := PTree.set name r mapVars, map_letvars := mapLetvars } : RTLgen.mapping)))
      s1 = RTLgen.res.OK (r, mapPrime) s2 i at h
    dsimp [RTLgen.bind] at h
    rw [show RTLgen.new_reg s1 = .OK s1.st_nextreg _ _ from rfl] at h
    simp [RTLgen.ret] at h
    cases h
    unfold map_valid at hvalid ⊢
    intro r hin
    unfold CompCert4Lean.Backend.Registers.reg at r
    unfold reg_in_map at hin
    change Plt r (PArith.BinPos.Pos.succ s1.st_nextreg)
    rcases hin with ⟨id, hget⟩ | hmem
    · change PTree.get id (PTree.set name s1.st_nextreg mapVars) = some r at hget
      rw [PTree.getSet_equation] at hget
      by_cases hid : id = name
      · subst id
        simp at hget
        cases hget
        exact Plt_succ _
      · simp [hid] at hget
        exact Plt_trans_succ r s1.st_nextreg (hvalid r (Or.inl ⟨id, hget⟩))
    · exact Plt_trans_succ r s1.st_nextreg (hvalid r (Or.inr hmem))

theorem add_var_valid : add_var_validStatement := by
  intro s1 s2 map1 map2 name r i h hmap
  have hmap2 := rtlgenspec_add_var_valid_map s1 s2 map1 map2 name r i h hmap
  have hr : reg_valid r s2 := by
    cases map1 with
    | mk mapVars mapLetvars =>
      unfold PTree.t at mapVars
      unfold CompCert4Lean.Common.AST.ident at name
      unfold CompCert4Lean.Backend.Registers.reg at *
      change RTLgen.bind RTLgen.new_reg
        (fun r => RTLgen.ret (r,
          ({ map_vars := PTree.set name r mapVars, map_letvars := mapLetvars } : RTLgen.mapping)))
        s1 = RTLgen.res.OK (r, map2) s2 i at h
      dsimp [RTLgen.bind] at h
      rw [show RTLgen.new_reg s1 = .OK s1.st_nextreg _ _ from rfl] at h
      simp [RTLgen.ret] at h
      cases h
      exact Plt_succ _
  exact ⟨hr, hmap2⟩

end CompCert4Lean.Backend.RTLgenspec

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

theorem init_mapping_valid : init_mapping_validStatement := by
  intro s r hin
  unfold reg_in_map RTLgen.init_mapping at hin
  rcases hin with ⟨id, hget⟩ | hmem
  · simp [PTree.get, PTree.empty] at hget
  · simp at hmem

theorem add_letvar_valid : add_letvar_validStatement := by
  intro map s r hmap hvalid r' hin
  unfold RTLgen.add_letvar at hin
  unfold reg_in_map at hin
  rcases hin with ⟨id, hget⟩ | hmem
  · exact hmap r' (Or.inl ⟨id, hget⟩)
  · simp only [List.mem_cons] at hmem
    rcases hmem with heq | htail
    · subst r'
      exact hvalid
    · exact hmap r' (Or.inr htail)

end CompCert4Lean.Backend.RTLgenspec

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

theorem add_vars_valid : add_vars_validStatement := by
  unfold add_vars_validStatement
  intro namel s1 s2 map1 map2 rl i
  induction namel generalizing s1 s2 map1 map2 rl i with
  | nil =>
      intro h hmap
      change RTLgen.ret ([], map1) s1 = .OK (rl, map2) s2 i at h
      simp [RTLgen.ret] at h
      rcases h with ⟨⟨hrl, hmap2⟩, hs⟩
      cases hrl
      cases hmap2
      cases hs
      constructor
      · intro r hmem
        simp at hmem
      · exact hmap
  | cons name names ih =>
      intro h hvalid
      change RTLgen.bind (RTLgen.add_vars map1 names)
        (fun x => RTLgen.bind (RTLgen.add_var x.2 name)
          (fun y => RTLgen.ret (y.1 :: x.1, y.2))) s1 = .OK (rl, map2) s2 i at h
      cases hrec : RTLgen.add_vars map1 names s1 with
      | Error msg =>
          simp [RTLgen.bind, hrec] at h
      | OK x sm hincr =>
          cases x with
          | mk rlmid mapmid =>
              simp [RTLgen.bind, hrec] at h
              cases hvar : RTLgen.add_var mapmid name sm with
              | Error msg =>
                  simp [hvar] at h
              | OK x sn hinc =>
                  cases x with
                  | mk rnew mapnew =>
                      simp [RTLgen.ret, hvar] at h
                      rcases h with ⟨⟨hrl, hmap⟩, hs⟩
                      have hrecvalid := ih (s1 := s1) (s2 := sm) (map1 := map1)
                        (map2 := mapmid) (rl := rlmid) (i := hincr) hrec hvalid
                      have haddvalid := add_var_valid (s1 := sm) (s2 := sn)
                        (map1 := mapmid) (map2 := mapnew) (name := name) (r := rnew)
                        (i := hinc) hvar hrecvalid.2
                      constructor
                      · simpa only [hrl, hmap, hs] using
                          (regs_valid_cons rnew rlmid sn haddvalid.1
                            (regs_valid_incr sm sn rlmid hinc hrecvalid.1))
                      · simpa only [hmap, hs] using haddvalid.2

end CompCert4Lean.Backend.RTLgenspec

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

theorem new_reg_target_ok : new_reg_target_okStatement := by
  intro map pr s1 a r s2 i hmap hpr hnew
  apply target_reg_ok.target_reg_other
  · exact new_reg_not_in_map s1 s2 map r i hnew hmap
  · intro hrmem
    have hv := hpr r hrmem
    simp only [RTLgen.new_reg] at hnew
    injection hnew with hr hs
    rw [← hr] at hv
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat s1.st_nextreg at hv
    exact Nat.lt_irrefl _ hv

theorem tr_move_incr : tr_move_incrStatement := by
  intro s1 s2 hin ns rs nd rd htr
  cases htr with
  | tr_move_0 => exact tr_move.tr_move_0 _ _
  | tr_move_1 nd rd h =>
      apply tr_move.tr_move_1
      exact instr_at_incr s1 s2 _ _ hin h

private theorem rtlgenspec_getElem?_nth_error {A : Type} (l : List A) (n : Nat) (x : A)
    (h : l[n]? = some x) : nth_error l n = some x := by
  induction l generalizing n with
  | nil => simp at h ⊢
  | cons a t ih =>
      cases n with
      | zero => simpa [nth_error] using h
      | succ n =>
          apply ih
          simpa [nth_error] using h

theorem alloc_reg_target_ok : alloc_reg_target_okStatement := by
  intro map pr s1 a r s2 i hmap hpr halloc
  cases a with
  | Evar id =>
      cases hfind : PTree.get id map.map_vars with
      | none =>
          simp [RTLgen.alloc_reg, RTLgen.find_var, hfind] at halloc
          cases halloc
      | some r0 =>
          simp [RTLgen.alloc_reg, RTLgen.find_var, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          exact target_reg_ok.target_reg_var id r hfind
  | Eletvar idx =>
      cases hfind : map.map_letvars[idx]? with
      | none =>
          simp [RTLgen.alloc_reg, RTLgen.find_letvar, hfind] at halloc
          cases halloc
      | some r0 =>
          simp [RTLgen.alloc_reg, RTLgen.find_letvar, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          apply target_reg_ok.target_reg_letvar idx r
          exact rtlgenspec_getElem?_nth_error map.map_letvars idx r hfind
  | Eop op args =>
      exact new_reg_target_ok map pr s1 (.Eop op args) r s2 i hmap hpr halloc
  | Eload chunk addr args =>
      exact new_reg_target_ok map pr s1 (.Eload chunk addr args) r s2 i hmap hpr halloc
  | Econdition cond ifso ifnot =>
      exact new_reg_target_ok map pr s1 (.Econdition cond ifso ifnot) r s2 i hmap hpr halloc
  | Elet bound body =>
      exact new_reg_target_ok map pr s1 (.Elet bound body) r s2 i hmap hpr halloc
  | Ebuiltin ef args =>
      exact new_reg_target_ok map pr s1 (.Ebuiltin ef args) r s2 i hmap hpr halloc
  | Eexternal id sig args =>
      exact new_reg_target_ok map pr s1 (.Eexternal id sig args) r s2 i hmap hpr halloc

end CompCert4Lean.Backend.RTLgenspec

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

private theorem rtlgenspec_alloc_reg_valid
    (map : RTLgen.mapping) (a : expr) (r : reg)
    (s1 s2 : RTLgen.state) (i : RTLgen.state_incr s1 s2) :
    map_valid map s1 →
    RTLgen.alloc_reg map a s1 = .OK r s2 i →
    reg_valid r s2 := by
  intro hmap halloc
  cases a with
  | Evar id =>
      cases hfind : PTree.get id map.map_vars with
      | none =>
          simp [RTLgen.alloc_reg, RTLgen.find_var, hfind] at halloc
          cases halloc
      | some r0 =>
          simp [RTLgen.alloc_reg, RTLgen.find_var, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          exact hmap r (Or.inl ⟨id, hfind⟩)
  | Eletvar idx =>
      cases hfind : map.map_letvars[idx]? with
      | none =>
          simp [RTLgen.alloc_reg, RTLgen.find_letvar, hfind] at halloc
          cases halloc
      | some r0 =>
          simp [RTLgen.alloc_reg, RTLgen.find_letvar, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          rcases (List.getElem?_eq_some_iff.mp hfind) with ⟨hi, hx⟩
          exact hmap r (Or.inr (List.mem_of_getElem hx))
  | Eop op args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _

  | Eload chunk addr args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Econdition cond ifso ifnot =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Elet bound body =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Ebuiltin ef args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Eexternal id sig args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _

private theorem rtlgenspec_map_valid_incr
    (map : RTLgen.mapping) (s1 s2 : RTLgen.state)
    (i : RTLgen.state_incr s1 s2) :
    map_valid map s1 → map_valid map s2 := by
  intro hmap r hr
  exact reg_valid_incr r s1 s2 i (hmap r hr)

theorem alloc_regs_target_ok : alloc_regs_target_okStatement := by
  intro map al pr s1 rl s2 i hmap hpr halloc
  refine exprlist.rec
      (motive_1 := fun _ => True)
      (motive_2 := fun al => ∀ (map : RTLgen.mapping) (pr : List reg)
        (s1 : RTLgen.state) (rl : List reg) (s2 : RTLgen.state)
        (i : RTLgen.state_incr s1 s2),
        map_valid map s1 → regs_valid pr s1 →
        RTLgen.alloc_regs map al s1 = .OK rl s2 i →
        target_regs_ok map pr al rl)
      (motive_3 := fun _ => True)
      (fun _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun map pr s1 rl s2 i hmap hpr halloc => by
        change RTLgen.ret [] s1 = .OK rl s2 i at halloc
        cases halloc
        exact target_regs_ok.target_regs_nil map pr)
      (fun a al _ ih map pr s1 rl s2 i hmap hpr halloc => by
        change RTLgen.bind (RTLgen.alloc_reg map a)
          (fun r => RTLgen.bind (RTLgen.alloc_regs map al)
            (fun rl => RTLgen.ret (r :: rl))) s1 = .OK rl s2 i at halloc
        cases hreg : RTLgen.alloc_reg map a s1 with
        | Error msg => simp [RTLgen.bind, hreg] at halloc
        | OK r sm hincr =>
            simp [RTLgen.bind, hreg] at halloc
            cases htail : RTLgen.alloc_regs map al sm with
            | Error msg => simp [RTLgen.bind, htail] at halloc
            | OK rlmid sn hinc =>
                simp [RTLgen.bind, htail, RTLgen.ret] at halloc
                rcases halloc with ⟨hrl, hs⟩
                cases hrl
                cases hs
                have hhead := alloc_reg_target_ok map pr s1 a r sm hincr hmap hpr hreg
                have hrvalid := rtlgenspec_alloc_reg_valid map a r s1 sm hincr hmap hreg
                have hmap' := rtlgenspec_map_valid_incr map s1 sm hincr hmap
                have hprsm := regs_valid_incr s1 sm pr hincr hpr
                have hpr' : regs_valid (r :: pr) sm :=
                  regs_valid_cons r pr sm hrvalid hprsm
                have htailvalid := ih map (r :: pr) sm rlmid s2 hinc hmap' hpr' htail
                exact target_regs_ok.target_regs_cons map pr a al r rlmid hhead htailvalid)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      al map pr s1 rl s2 i hmap hpr halloc

end CompCert4Lean.Backend.RTLgenspec

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

theorem add_move_charact : add_move_charactStatement := by
  intro s ns rs nd rd s' i h
  by_cases heq : rs = rd
  · simp [RTLgen.add_move, heq, RTLgen.ret] at h
    rcases h with ⟨hns, hs⟩
    cases hns
    cases hs
    cases heq
    exact tr_move.tr_move_0 _ _
  · simp [RTLgen.add_move, heq, RTLgen.add_instr, RTLgen.ret] at h
    injection h with hns hs
    cases hns
    cases hs
    apply tr_move.tr_move_1
    change PTree.get s.st_nextnode
      (PTree.set s.st_nextnode (RTL.instruction.Iop Omove [rs] rd nd) s.st_code) = _
    have hx := PTree.getSet_equation (A := RTL.instruction)
      s.st_nextnode s.st_nextnode (RTL.instruction.Iop Omove [rs] rd nd) s.st_code
    rw [hx]
    simp

end CompCert4Lean.Backend.RTLgenspec

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

theorem tr_expr_incr : tr_expr_incrStatement := by
  intro s1 s2 EXT map pr a ns nd rd dst htr
  refine tr_expr.rec
    (motive_1 := fun map pr a ns nd rd dst _ =>
      tr_expr s2.st_code map pr a ns nd rd dst)
    (motive_2 := fun map pr a ns nt nf _ =>
      tr_condition s2.st_code map pr a ns nt nf)
    (motive_3 := fun map pr al ns nd rl _ =>
      tr_exprlist s2.st_code map pr al ns nd rl)
    (fun map pr id ns nd r rd dst hmap hok hmove => by
      apply tr_expr.tr_Evar
      · exact hmap
      · exact hok
      · exact tr_move_incr s1 s2 EXT ns r nd rd hmove)
    (fun map pr op al ns nd rd n1 rl dst hargs hcode hmap hpr ih => by
      apply tr_expr.tr_Eop
      · exact ih
      · exact instr_at_incr s1 s2 n1 _ EXT hcode
      · exact hmap
      · exact hpr)
    (fun map pr chunk addr al ns nd rd n1 rl dst hargs hcode hmap hpr ih => by
      apply tr_expr.tr_Eload
      · exact ih
      · exact instr_at_incr s1 s2 n1 _ EXT hcode
      · exact hmap
      · exact hpr)
    (fun map pr a ifso ifnot ns nd rd nt nf dst hcond htrue hfalse ihc iht ihf => by
      apply tr_expr.tr_Econdition
      · exact ihc
      · exact iht
      · exact ihf)
    (fun map pr b1 b2 ns nd rd n1 r dst hfresh hbound hbody ihb ihbody => by
      apply tr_expr.tr_Elet
      · exact hfresh
      · exact ihb
      · exact ihbody)
    (fun map pr n ns nd rd r dst hlet hok hmove => by
      apply tr_expr.tr_Eletvar
      · exact hlet
      · exact hok
      · exact tr_move_incr s1 s2 EXT ns r nd rd hmove)
    (fun map pr ef al ns nd rd dst n1 rl hargs hcode hmap hpr ih => by
      apply tr_expr.tr_Ebuiltin
      · exact ih
      · exact instr_at_incr s1 s2 n1 _ EXT hcode
      · exact hmap
      · exact hpr)
    (fun map pr id sg al ns nd rd dst n1 rl hargs hcode hmap hpr ih => by
      apply tr_expr.tr_Eexternal
      · exact ih
      · exact instr_at_incr s1 s2 n1 _ EXT hcode
      · exact hmap
      · exact hpr)
    (fun map pr cond bl ns nt nf n1 rl hargs hcode ih => by
      apply tr_condition.tr_CEcond
      · exact ih
      · exact instr_at_incr s1 s2 n1 _ EXT hcode)
    (fun map pr a1 a2 a3 ns nt nf n2 n3 h1 h2 h3 ih1 ih2 ih3 => by
      apply tr_condition.tr_CEcondition
      · exact ih1
      · exact ih2
      · exact ih3)
    (fun map pr a b ns nt nf r n1 hfresh hbound hbody ihb ihbody => by
      apply tr_condition.tr_CElet
      · exact hfresh
      · exact ihb
      · exact ihbody)
    (fun map pr n => by exact tr_exprlist.tr_Enil _ _ _)
    (fun map pr a1 al ns nd r1 rl n1 hhead htail ihhead ihtail => by
      apply tr_exprlist.tr_Econs
      · exact ihhead
      · exact ihtail)
    htr -- tr_expr_end

end CompCert4Lean.Backend.RTLgenspec

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

theorem tr_condition_incr : tr_condition_incrStatement := by
  intro s1 s2 EXT map pr a ns nt nf htr
  refine tr_condition.rec
    (motive_1 := fun map pr a ns nd rd dst h =>
      tr_expr s2.st_code map pr a ns nd rd dst)
    (motive_2 := fun map pr a ns nt nf h =>
      tr_condition s2.st_code map pr a ns nt nf)
    (motive_3 := fun map pr al ns nd rl h =>
      tr_exprlist s2.st_code map pr al ns nd rl)
    (fun map pr id ns nd r rd dst hmap hok hmove => by
      exact tr_expr_incr s1 s2 EXT map pr (.Evar id) ns nd rd dst
        (tr_expr.tr_Evar map pr id ns nd r rd dst hmap hok hmove))
    (fun map pr op al ns nd rd n1 rl dst hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eop op al) ns nd rd dst
        (tr_expr.tr_Eop map pr op al ns nd rd n1 rl dst hargs hcode hmap hpr))
    (fun map pr chunk addr al ns nd rd n1 rl dst hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eload chunk addr al) ns nd rd dst
        (tr_expr.tr_Eload map pr chunk addr al ns nd rd n1 rl dst hargs hcode hmap hpr))
    (fun map pr a ifso ifnot ns nd rd nt nf dst hcond htrue hfalse ihc iht ihf => by
      exact tr_expr_incr s1 s2 EXT map pr (.Econdition a ifso ifnot) ns nd rd dst
        (tr_expr.tr_Econdition map pr a ifso ifnot ns nd rd nt nf dst hcond htrue hfalse))
    (fun map pr b1 b2 ns nd rd n1 r dst hfresh hbound hbody ihb ihbody => by
      exact tr_expr_incr s1 s2 EXT map pr (.Elet b1 b2) ns nd rd dst
        (tr_expr.tr_Elet map pr b1 b2 ns nd rd n1 r dst hfresh hbound hbody))
    (fun map pr n ns nd rd r dst hlet hok hmove => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eletvar n) ns nd rd dst
        (tr_expr.tr_Eletvar map pr n ns nd rd r dst hlet hok hmove))
    (fun map pr ef al ns nd rd dst n1 rl hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Ebuiltin ef al) ns nd rd dst
        (tr_expr.tr_Ebuiltin map pr ef al ns nd rd dst n1 rl hargs hcode hmap hpr))
    (fun map pr id sg al ns nd rd dst n1 rl hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eexternal id sg al) ns nd rd dst
        (tr_expr.tr_Eexternal map pr id sg al ns nd rd dst n1 rl hargs hcode hmap hpr))
    (fun map pr cond bl ns nt nf n1 rl hargs hcode ih => by
      apply tr_condition.tr_CEcond
      · exact ih
      · exact instr_at_incr s1 s2 n1 _ EXT hcode)
    (fun map pr a1 a2 a3 ns nt nf n2 n3 h1 h2 h3 ih1 ih2 ih3 => by
      apply tr_condition.tr_CEcondition
      · exact ih1
      · exact ih2
      · exact ih3)
    (fun map pr a b ns nt nf r n1 hfresh hbound hbody ihb ihbody => by
      apply tr_condition.tr_CElet
      · exact hfresh
      · exact ihb
      · exact ihbody)
    (fun map pr n => by exact tr_exprlist.tr_Enil _ _ _)
    (fun map pr a1 al ns nd r1 rl n1 hhead htail ihhead ihtail => by
      apply tr_exprlist.tr_Econs
      · exact ihhead
      · exact ihtail)
    htr

end CompCert4Lean.Backend.RTLgenspec

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

theorem tr_exprlist_incr : tr_exprlist_incrStatement := by
  intro s1 s2 EXT map pr al ns nd rl htr
  refine tr_exprlist.rec
    (motive_1 := fun map pr a ns nd rd dst h =>
      tr_expr s2.st_code map pr a ns nd rd dst)
    (motive_2 := fun map pr a ns nt nf h =>
      tr_condition s2.st_code map pr a ns nt nf)
    (motive_3 := fun map pr al ns nd rl h =>
      tr_exprlist s2.st_code map pr al ns nd rl)
    (fun map pr id ns nd r rd dst hmap hok hmove => by
      exact tr_expr_incr s1 s2 EXT map pr (.Evar id) ns nd rd dst
        (tr_expr.tr_Evar map pr id ns nd r rd dst hmap hok hmove))
    (fun map pr op al ns nd rd n1 rl dst hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eop op al) ns nd rd dst
        (tr_expr.tr_Eop map pr op al ns nd rd n1 rl dst hargs hcode hmap hpr))
    (fun map pr chunk addr al ns nd rd n1 rl dst hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eload chunk addr al) ns nd rd dst
        (tr_expr.tr_Eload map pr chunk addr al ns nd rd n1 rl dst hargs hcode hmap hpr))
    (fun map pr a ifso ifnot ns nd rd nt nf dst hcond htrue hfalse ihc iht ihf => by
      exact tr_expr_incr s1 s2 EXT map pr (.Econdition a ifso ifnot) ns nd rd dst
        (tr_expr.tr_Econdition map pr a ifso ifnot ns nd rd nt nf dst hcond htrue hfalse))
    (fun map pr b1 b2 ns nd rd n1 r dst hfresh hbound hbody ihb ihbody => by
      exact tr_expr_incr s1 s2 EXT map pr (.Elet b1 b2) ns nd rd dst
        (tr_expr.tr_Elet map pr b1 b2 ns nd rd n1 r dst hfresh hbound hbody))
    (fun map pr n ns nd rd r dst hlet hok hmove => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eletvar n) ns nd rd dst
        (tr_expr.tr_Eletvar map pr n ns nd rd r dst hlet hok hmove))
    (fun map pr ef al ns nd rd dst n1 rl hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Ebuiltin ef al) ns nd rd dst
        (tr_expr.tr_Ebuiltin map pr ef al ns nd rd dst n1 rl hargs hcode hmap hpr))
    (fun map pr id sg al ns nd rd dst n1 rl hargs hcode hmap hpr ih => by
      exact tr_expr_incr s1 s2 EXT map pr (.Eexternal id sg al) ns nd rd dst
        (tr_expr.tr_Eexternal map pr id sg al ns nd rd dst n1 rl hargs hcode hmap hpr))
    (fun map pr cond bl ns nt nf n1 rl hargs hcode ih => by
      exact tr_condition_incr s1 s2 EXT map pr (.CEcond cond bl) ns nt nf
        (tr_condition.tr_CEcond map pr cond bl ns nt nf n1 rl hargs hcode))
    (fun map pr a1 a2 a3 ns nt nf n2 n3 h1 h2 h3 ih1 ih2 ih3 => by
      exact tr_condition_incr s1 s2 EXT map pr (.CEcondition a1 a2 a3) ns nt nf
        (tr_condition.tr_CEcondition map pr a1 a2 a3 ns nt nf n2 n3 h1 h2 h3))
    (fun map pr a b ns nt nf r n1 hfresh hbound hbody ihb ihbody => by
      exact tr_condition_incr s1 s2 EXT map pr (.CElet a b) ns nt nf
        (tr_condition.tr_CElet map pr a b ns nt nf r n1 hfresh hbound hbody))
    (fun map pr n => by exact tr_exprlist.tr_Enil _ _ _)
    (fun map pr a1 al ns nd r1 rl n1 hhead htail ihhead ihtail => by
      apply tr_exprlist.tr_Econs
      · exact ihhead
      · exact ihtail)
    htr

end CompCert4Lean.Backend.RTLgenspec
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

private theorem test_alloc_reg_valid
    (map : RTLgen.mapping) (a : expr) (r : reg)
    (s1 s2 : RTLgen.state) (i : state_incr s1 s2) :
    map_valid map s1 →
    RTLgen.alloc_reg map a s1 = .OK r s2 i →
    reg_valid r s2 := by
  intro hmap halloc
  cases a with
  | Evar id =>
      cases hfind : PTree.get id map.map_vars with
      | none => simp [RTLgen.alloc_reg, RTLgen.find_var, RTLgen.error, hfind] at halloc
      | some r0 =>
          simp [RTLgen.alloc_reg, RTLgen.find_var, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          exact hmap r (Or.inl ⟨id, hfind⟩)
  | Eletvar idx =>
      cases hfind : map.map_letvars[idx]? with
      | none => simp [RTLgen.alloc_reg, RTLgen.find_letvar, RTLgen.error, hfind] at halloc
      | some r0 =>
          simp [RTLgen.alloc_reg, RTLgen.find_letvar, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          rcases (List.getElem?_eq_some_iff.mp hfind) with ⟨hi, hx⟩
          exact hmap r (Or.inr (List.mem_of_getElem hx))
  | Eop op args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Eload chunk addr args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Econdition cond ifso ifnot =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Elet bound body =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Ebuiltin ef args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _
  | Eexternal id sig args =>
      simp only [RTLgen.alloc_reg, RTLgen.new_reg] at halloc
      injection halloc with hr hs
      cases hr
      cases hs
      exact Plt_succ _

private theorem test_map_valid_incr
    (map : RTLgen.mapping) (s1 s2 : RTLgen.state) (i : state_incr s1 s2) :
    map_valid map s1 → map_valid map s2 := by
  intro hmap r hr
  exact reg_valid_incr r s1 s2 i (hmap r hr)

private theorem test_add_instr_code
    (s : RTLgen.state) (ins : RTL.instruction) (n : RTL.node)
    (s' : RTLgen.state) (i : state_incr s s') :
    RTLgen.add_instr ins s = .OK n s' i →
    PTree.get n s'.st_code = some ins := by
  intro h
  simp [RTLgen.add_instr] at h
  injection h with hn hs
  cases hn
  cases hs
  change PTree.get s.st_nextnode
    (PTree.set s.st_nextnode ins (show PTree.t RTL.instruction from s.st_code)) = some ins
  have hx := PTree.getSet_equation (A := RTL.instruction)
    s.st_nextnode s.st_nextnode ins s.st_code
  rw [hx]
  simp

private theorem test_new_reg_valid
    (s : RTLgen.state) (r : reg) (s' : RTLgen.state) (i : state_incr s s') :
    RTLgen.new_reg s = .OK r s' i → reg_valid r s' := by
  intro h
  simp [RTLgen.new_reg] at h
  injection h with hr hs
  cases hr
  cases hs
  exact Plt_succ _

private theorem test_new_reg_fresh
    (s : RTLgen.state) (r : reg) (s' : RTLgen.state) (i : state_incr s s') :
    RTLgen.new_reg s = .OK r s' i → reg_fresh r s := by
  intro h
  simp [RTLgen.new_reg] at h
  injection h with hr hs
  cases hr
  cases hs
  unfold reg_fresh
  intro hlt
  change PArith.BinPos.Pos.to_nat s.st_nextreg <
    PArith.BinPos.Pos.to_nat s.st_nextreg at hlt
  exact Nat.lt_irrefl _ hlt

private theorem test_getElem_nth {A : Type} (l : List A) (n : Nat) (x : A)
    (h : l[n]? = some x) : nth_error l n = some x := by
  induction l generalizing n with
  | nil => simp at h ⊢
  | cons a t ih =>
      cases n with
      | zero => simpa [nth_error] using h
      | succ n =>
          apply ih
          simpa [nth_error] using h

private theorem test_alloc_regs_valid
    (map : RTLgen.mapping) (al : exprlist) (rl : List reg)
    (s1 s2 : RTLgen.state) (i : state_incr s1 s2) :
    map_valid map s1 →
    RTLgen.alloc_regs map al s1 = .OK rl s2 i →
    regs_valid rl s2 := by
  intro hmap halloc
  refine exprlist.rec
      (motive_1 := fun _ => True)
      (motive_2 := fun al => ∀ (map : RTLgen.mapping) (rl : List reg)
        (s1 s2 : RTLgen.state) (i : state_incr s1 s2),
        map_valid map s1 →
        RTLgen.alloc_regs map al s1 = .OK rl s2 i →
        regs_valid rl s2)
      (motive_3 := fun _ => True)
      (fun _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun map rl s1 s2 i hmap halloc => by
        change RTLgen.ret [] s1 = .OK rl s2 i at halloc
        simp [RTLgen.ret] at halloc
        rcases halloc with ⟨hrl, hs⟩
        cases hrl
        cases hs
        intro r hmem
        simp at hmem)
      (fun a al ihhead ihtail map rl s1 s2 i hmap halloc => by
        change RTLgen.bind (RTLgen.alloc_reg map a)
          (fun r => RTLgen.bind (RTLgen.alloc_regs map al)
            (fun rl => RTLgen.ret (r :: rl))) s1 = .OK rl s2 i at halloc
        cases hreg : RTLgen.alloc_reg map a s1 with
        | Error msg => simp [RTLgen.bind, hreg] at halloc
        | OK r sm hincr =>
            simp [RTLgen.bind, hreg] at halloc
            cases htail : RTLgen.alloc_regs map al sm with
            | Error msg => simp [RTLgen.bind, htail] at halloc
            | OK rlmid sn hinc =>
                simp [RTLgen.bind, htail, RTLgen.ret] at halloc
                rcases halloc with ⟨hrl, hs⟩
                cases hrl
                cases hs
                have hrvalid := test_alloc_reg_valid map a r s1 sm hincr hmap hreg
                have hmap' := test_map_valid_incr map s1 sm hincr hmap
                have htailvalid := ihtail map rlmid sm s2 hinc hmap' htail
                exact regs_valid_cons r rlmid s2
                  (reg_valid_incr r sm s2 hinc hrvalid) htailvalid)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      al map rl s1 s2 i hmap halloc

mutual
  private def aux_expr (a : expr) (map : RTLgen.mapping) (rd : reg) (nd : RTL.node)
      (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (pr : List reg)
      (INCR : state_incr s s') :
      RTLgen.transl_expr map a rd nd s = .OK ns s' INCR →
      map_valid map s → target_reg_ok map pr a rd → regs_valid pr s → reg_valid rd s →
      tr_expr s'.st_code map pr a ns nd rd none := by
    intro TR WF OK VALID VALID2
    cases a with
    | Evar id =>
        cases hfind : PTree.get id map.map_vars with
        | none =>
            change RTLgen.bind (RTLgen.find_var map id)
              (fun r => RTLgen.add_move r rd nd) s = _ at TR
            simp [RTLgen.find_var, hfind, RTLgen.error, RTLgen.bind] at TR
        | some r0 =>
            change RTLgen.bind (RTLgen.find_var map id)
              (fun r => RTLgen.add_move r rd nd) s = _ at TR
            rw [show RTLgen.find_var map id = RTLgen.ret r0 by simp [RTLgen.find_var, hfind]] at TR
            simp [RTLgen.bind] at TR
            by_cases hr : r0 = rd
            · simp [RTLgen.add_move, hr, RTLgen.ret, RTLgen.bind] at TR
              rcases TR with ⟨hns, hs⟩
              cases hns
              cases hs
              cases hr
              apply tr_expr.tr_Evar
              · exact hfind
              · left; exact ⟨rfl, rfl⟩
              · exact tr_move.tr_move_0 _ _
            · simp [RTLgen.add_move, hr, RTLgen.add_instr, RTLgen.ret, RTLgen.bind] at TR
              injection TR with hns hs
              cases hns
              cases hs
              apply tr_expr.tr_Evar
              · exact hfind
              · cases OK with
                | target_reg_var id' r' hmap' =>
                    exfalso
                    have he : (some r0 : Option reg) = some rd := hfind.symm.trans hmap'
                    exact hr (Option.some.inj he)
                | target_reg_other a' r' hmap' hpr' =>
                    exact Or.inr ⟨reg_map_ok.reg_map_ok_novar map rd hmap', hpr'⟩
              · apply tr_move.tr_move_1
                change PTree.get s.st_nextnode
                  (PTree.set s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code) = _
                have hx := PTree.getSet_equation (A := RTL.instruction)
                  s.st_nextnode s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code
                rw [hx]
                simp
    | Eop op al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Iop op rl rd nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Iop op rl rd nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Eop
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hpr_sn := regs_valid_incr s sn pr hssn VALID
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' pr htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al pr s rl sm hincr WF VALID halloc)
                        hpr_sn hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Iop op rl rd nd) no sn hinstr hadd)
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' =>
                          exact reg_map_ok.reg_map_ok_novar map rd hmap'
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hpr'
    | Eload chunk addr al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Iload chunk addr rl rd nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Iload chunk addr rl rd nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Eload
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hpr_sn := regs_valid_incr s sn pr hssn VALID
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' pr htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al pr s rl sm hincr WF VALID halloc)
                        hpr_sn hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Iload chunk addr rl rd nd) no sn hinstr hadd)
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' =>
                          exact reg_map_ok.reg_map_ok_novar map rd hmap'
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hpr'
    | Econdition a ifso ifnot =>
        change RTLgen.bind (RTLgen.transl_expr map ifnot rd nd)
          (fun nfalse => RTLgen.bind (RTLgen.transl_expr map ifso rd nd)
            (fun ntrue => RTLgen.transl_condexpr map a ntrue nfalse)) s = .OK ns s' INCR at TR
        cases hfalse : RTLgen.transl_expr map ifnot rd nd s with
        | Error msg => simp [RTLgen.bind, hfalse] at TR
        | OK nfalse s0 hfalseIncr =>
            simp [RTLgen.bind, hfalse] at TR
            cases htrue : RTLgen.transl_expr map ifso rd nd s0 with
            | Error msg => simp [RTLgen.bind, htrue] at TR
            | OK ntrue s1 htrueIncr =>
                simp [RTLgen.bind, htrue] at TR
                cases hcond : RTLgen.transl_condexpr map a ntrue nfalse s1 with
                | Error msg => simp [RTLgen.bind, hcond] at TR
                | OK ns2 sfin hcondIncr =>
                    simp [RTLgen.bind, hcond, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    have hfalseTo : state_incr s0 s' :=
                      RTLgen.state_incr_trans s0 s1 s' htrueIncr hcondIncr
                    have htrueTo : state_incr s1 s' := hcondIncr
                    have hmap0 := test_map_valid_incr map s s0 hfalseIncr WF
                    have hmap1 := test_map_valid_incr map s0 s1 htrueIncr hmap0
                    have hpr0 := regs_valid_incr s s0 pr hfalseIncr VALID
                    have hpr1 := regs_valid_incr s0 s1 pr htrueIncr hpr0
                    have hrd0 := reg_valid_incr rd s s0 hfalseIncr VALID2
                    have hrd1 := reg_valid_incr rd s0 s1 htrueIncr hrd0
                    have hOKmap : ¬ reg_in_map map rd := by
                      cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hmap'
                    have hOKpr : ¬ rd ∈ pr := by
                      cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hpr'
                    apply tr_expr.tr_Econdition
                    · exact aux_cond a map ntrue nfalse s1 ns s' pr hcondIncr
                        hcond hmap1 hpr1
                    · exact tr_expr_incr s1 s' hcondIncr map pr ifso ntrue nd rd none
                        (aux_expr ifso map rd nd s0 ntrue s1 pr htrueIncr htrue hmap0
                          (target_reg_ok.target_reg_other ifso rd hOKmap hOKpr)
                          hpr0 hrd0)
                    · exact tr_expr_incr s0 s' hfalseTo map pr ifnot nfalse nd rd none
                        (aux_expr ifnot map rd nd s nfalse s0 pr hfalseIncr hfalse WF
                          (target_reg_ok.target_reg_other ifnot rd hOKmap hOKpr)
                          VALID VALID2)
    | Elet b c =>
        change RTLgen.bind RTLgen.new_reg
          (fun r => RTLgen.bind (RTLgen.transl_expr (RTLgen.add_letvar map r) c rd nd)
            (fun nc => RTLgen.transl_expr map b r nc)) s = .OK ns s' INCR at TR
        cases hnew : RTLgen.new_reg s with
        | Error msg => simp [RTLgen.bind, hnew] at TR
        | OK r s0 hnewIncr =>
            simp [RTLgen.bind, hnew] at TR
            cases hbody : RTLgen.transl_expr (RTLgen.add_letvar map r) c rd nd s0 with
            | Error msg => simp [RTLgen.bind, hbody] at TR
            | OK nc s1 hbodyIncr =>
                simp [RTLgen.bind, hbody] at TR
                cases hbound : RTLgen.transl_expr map b r nc s1 with
                | Error msg => simp [RTLgen.bind, hbound] at TR
                | OK ns2 sfin hboundIncr =>
                    simp [RTLgen.bind, hbound, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    have hr0 := test_new_reg_valid s r s0 hnewIncr hnew
                    have hmap0 := test_map_valid_incr map s s0 hnewIncr WF
                    have hmapLet := add_letvar_valid map s0 r hmap0
                        (by exact hr0)
                    have hmap1 := test_map_valid_incr (RTLgen.add_letvar map r)
                        s0 s1 hbodyIncr hmapLet
                    have hmap1orig := test_map_valid_incr map s s1
                        (RTLgen.state_incr_trans s s0 s1 hnewIncr hbodyIncr) WF
                    have hpr0 := regs_valid_incr s s0 pr hnewIncr VALID
                    have hpr1 := regs_valid_incr s0 s1 pr hbodyIncr hpr0
                    have hrd0 := reg_valid_incr rd s s0 hnewIncr VALID2
                    have hrd1 := reg_valid_incr rd s0 s1 hbodyIncr hrd0
                    have hr1 := reg_valid_incr r s0 s1 hbodyIncr hr0
                    have hOKmap : ¬ reg_in_map map rd := by
                      cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hmap'
                    have hOKpr : ¬ rd ∈ pr := by
                      cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hpr'
                    have hrd_ne : rd ≠ r := by
                      intro heq
                      subst rd
                      exact valid_fresh_absurd r s VALID2
                        (test_new_reg_fresh s r s0 hnewIncr hnew)
                    have hOKmapLet : ¬ reg_in_map (RTLgen.add_letvar map r) rd := by
                      intro hin
                      unfold RTLgen.add_letvar reg_in_map at hin
                      rcases hin with ⟨id, hget⟩ | hmem
                      · exact hOKmap (Or.inl ⟨id, hget⟩)
                      · simp only [List.mem_cons] at hmem
                        rcases hmem with heq | htail
                        · exact hrd_ne heq
                        · exact hOKmap (Or.inr htail)
                    have hr_not_map : ¬ reg_in_map map r :=
                      new_reg_not_in_map s s0 map r hnewIncr hnew WF
                    have hr_fresh_s : reg_fresh r s := test_new_reg_fresh s r s0 hnewIncr hnew
                    have hr_not_pr : ¬ r ∈ pr := by
                      intro hmem
                      exact valid_fresh_absurd r s (VALID r hmem) hr_fresh_s
                    apply tr_expr.tr_Elet
                    · exact hr_not_map
                    · exact aux_expr b map r nc s1 ns s' pr hboundIncr hbound hmap1orig
                        (target_reg_ok.target_reg_other b r hr_not_map hr_not_pr)
                        (regs_valid_incr s s1 pr
                          (RTLgen.state_incr_trans s s0 s1 hnewIncr hbodyIncr) VALID) hr1
                    · exact tr_expr_incr s1 s' hboundIncr
                        (RTLgen.add_letvar map r) pr c nc nd rd none
                        (aux_expr c (RTLgen.add_letvar map r) rd nd s0 nc s1 pr
                          hbodyIncr hbody hmapLet
                          (target_reg_ok.target_reg_other c rd hOKmapLet hOKpr)
                          hpr0 hrd0)
    | Eletvar n =>
        change RTLgen.bind (RTLgen.find_letvar map n)
          (fun r => RTLgen.add_move r rd nd) s = .OK ns s' INCR at TR
        cases hfind : map.map_letvars[n]? with
        | none => simp [RTLgen.find_letvar, RTLgen.error, RTLgen.bind, hfind] at TR
        | some r0 =>
            rw [show RTLgen.find_letvar map n = RTLgen.ret r0 by
              simp [RTLgen.find_letvar, hfind]] at TR
            simp [RTLgen.bind] at TR
            by_cases hr : r0 = rd
            · simp [RTLgen.add_move, hr, RTLgen.ret] at TR
              rcases TR with ⟨hns, hs⟩
              cases hns
              cases hs
              have hlet0 := test_getElem_nth map.map_letvars n r0 hfind
              cases hr
              apply tr_expr.tr_Eletvar
              · exact hlet0
              · left; exact ⟨rfl, rfl⟩
              · exact tr_move.tr_move_0 _ _
            · simp [RTLgen.add_move, hr, RTLgen.add_instr, RTLgen.ret] at TR
              injection TR with hns hs
              cases hns
              cases hs
              apply tr_expr.tr_Eletvar
              · exact test_getElem_nth map.map_letvars n r0 hfind
              · cases OK with
                | target_reg_letvar idx r' hlet' =>
                    exfalso
                    have hlet0 := test_getElem_nth map.map_letvars n r0 hfind
                    have he : (some r0 : Option reg) = some rd := hlet0.symm.trans hlet'
                    exact hr (Option.some.inj he)
                | target_reg_other a' r' hmap' hpr' =>
                    exact Or.inr ⟨reg_map_ok.reg_map_ok_novar map rd hmap', hpr'⟩
              · apply tr_move.tr_move_1
                change PTree.get s.st_nextnode
                  (PTree.set s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code) = _
                have hx := PTree.getSet_equation (A := RTL.instruction)
                  s.st_nextnode s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code
                rw [hx]
                simp
    | Ebuiltin ef al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Ebuiltin
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hpr_sn := regs_valid_incr s sn pr hssn VALID
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' pr htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al pr s rl sm hincr WF VALID halloc)
                        hpr_sn hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd)
                          no sn hinstr hadd)
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' =>
                          exact reg_map_ok.reg_map_ok_novar map rd hmap'
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hpr'
    | Eexternal id sg al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Icall sg (.inr id) rl rd nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Icall sg (.inr id) rl rd nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Eexternal
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hpr_sn := regs_valid_incr s sn pr hssn VALID
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' pr htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al pr s rl sm hincr WF VALID halloc)
                        hpr_sn hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Icall sg (.inr id) rl rd nd)
                          no sn hinstr hadd)
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' =>
                          exact reg_map_ok.reg_map_ok_novar map rd hmap'
                    · cases OK with
                      | target_reg_other a' r' hmap' hpr' => exact hpr'
  private def aux_list (al : exprlist) (map : RTLgen.mapping) (rl : List reg) (nd : RTL.node)
      (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (pr : List reg)
      (INCR : state_incr s s') :
      RTLgen.transl_exprlist map al rl nd s = .OK ns s' INCR →
      map_valid map s → target_regs_ok map pr al rl → regs_valid pr s → regs_valid rl s →
        tr_exprlist s'.st_code map pr al ns nd rl := by
    intro TR WF OK VALID VALID2
    cases al with
    | Enil =>
        cases rl with
        | nil =>
            change RTLgen.ret nd s = .OK ns s' INCR at TR
            simp [RTLgen.ret] at TR
            rcases TR with ⟨hns, hs⟩
            cases hns
            cases hs
            exact tr_exprlist.tr_Enil _ _ _
        | cons r rs =>
            change RTLgen.error _ s = .OK ns s' INCR at TR
            simp [RTLgen.error] at TR
    | Econs b bs =>
        cases rl with
        | nil =>
            change RTLgen.error _ s = .OK ns s' INCR at TR
            simp [RTLgen.error] at TR
        | cons r rs =>
            change RTLgen.bind (RTLgen.transl_exprlist map bs rs nd)
              (fun no => RTLgen.transl_expr map b r no) s = .OK ns s' INCR at TR
            cases htail : RTLgen.transl_exprlist map bs rs nd s with
            | Error msg => simp [RTLgen.bind, htail] at TR
            | OK no sm htailIncr =>
                simp [RTLgen.bind, htail] at TR
                cases hhead : RTLgen.transl_expr map b r no sm with
                | Error msg => simp [RTLgen.bind, hhead] at TR
                | OK ns2 sfin hheadIncr =>
                    simp [RTLgen.bind, hhead, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    cases OK with
                    | target_regs_cons pr0 b0 bs0 r0 rs0 hheadOK htailOK =>
                        have hr_s : reg_valid r s := VALID2 r (by simp)
                        have hrs_s : regs_valid rs s := by
                          intro x hx
                          exact VALID2 x (by simp [hx])
                        have hmap_sm := test_map_valid_incr map s sm htailIncr WF
                        have hpr_sm := regs_valid_incr s sm pr htailIncr VALID
                        have hr_sm := reg_valid_incr r s sm htailIncr hr_s
                        have htailproof := aux_list bs map rs nd s no sm (r :: pr)
                          htailIncr htail WF htailOK (regs_valid_cons r pr s hr_s VALID) hrs_s
                        apply tr_exprlist.tr_Econs
                        · exact aux_expr b map r no sm ns s' pr hheadIncr hhead
                            hmap_sm hheadOK hpr_sm hr_sm
                        · exact tr_exprlist_incr sm s' hheadIncr map (r :: pr) bs no nd rs
                            htailproof
  private def aux_cond (a : condexpr) (map : RTLgen.mapping) (ntrue nfalse : RTL.node)
      (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (pr : List reg)
      (INCR : state_incr s s') :
      RTLgen.transl_condexpr map a ntrue nfalse s = .OK ns s' INCR →
      map_valid map s → regs_valid pr s →
        tr_condition s'.st_code map pr a ns ntrue nfalse := by
    intro TR WF VALID
    cases a with
    | CEcond cond bl =>
        change RTLgen.bind (RTLgen.alloc_regs map bl)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Icond cond rl ntrue nfalse))
            (fun nt => RTLgen.transl_exprlist map bl rl nt)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map bl s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Icond cond rl ntrue nfalse) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK nt sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map bl rl nt sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailIncr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_condition.tr_CEcond
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hpr_sn := regs_valid_incr s sn pr hssn VALID
                    have hrl_sm := test_alloc_regs_valid map bl rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list bl map rl nt sn ns s' pr htailIncr
                        htail hmap_sn
                        (alloc_regs_target_ok map bl pr s rl sm hincr WF VALID halloc)
                        hpr_sn hrl_sn
                    · exact instr_at_incr sn s' nt _ htailIncr
                        (test_add_instr_code sm (RTL.instruction.Icond cond rl ntrue nfalse)
                          nt sn hinstr hadd)
    | CEcondition a b c =>
        change RTLgen.bind (RTLgen.transl_condexpr map c ntrue nfalse)
          (fun nc => RTLgen.bind (RTLgen.transl_condexpr map b ntrue nfalse)
            (fun nb => RTLgen.transl_condexpr map a nb nc)) s = .OK ns s' INCR at TR
        cases hc : RTLgen.transl_condexpr map c ntrue nfalse s with
        | Error msg => simp [RTLgen.bind, hc] at TR
        | OK nc s0 hcIncr =>
            simp [RTLgen.bind, hc] at TR
            cases hb : RTLgen.transl_condexpr map b ntrue nfalse s0 with
            | Error msg => simp [RTLgen.bind, hb] at TR
            | OK nb s1 hbIncr =>
                simp [RTLgen.bind, hb] at TR
                cases ha : RTLgen.transl_condexpr map a nb nc s1 with
                | Error msg => simp [RTLgen.bind, ha] at TR
                | OK ns2 sfin haIncr =>
                    simp [RTLgen.bind, ha, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    have hmap0 := test_map_valid_incr map s s0 hcIncr WF
                    have hmap1 := test_map_valid_incr map s0 s1 hbIncr hmap0
                    have hpr0 := regs_valid_incr s s0 pr hcIncr VALID
                    have hpr1 := regs_valid_incr s0 s1 pr hbIncr hpr0
                    have hcaTo : state_incr s0 s' :=
                      RTLgen.state_incr_trans s0 s1 s' hbIncr haIncr
                    have hA := aux_cond a map nb nc s1 ns s' pr haIncr ha hmap1 hpr1
                    have hB := tr_condition_incr s1 s' haIncr map pr b nb ntrue nfalse
                      (aux_cond b map ntrue nfalse s0 nb s1 pr hbIncr hb hmap0 hpr0)
                    have hC := tr_condition_incr s0 s' hcaTo map pr c nc ntrue nfalse
                      (aux_cond c map ntrue nfalse s nc s0 pr hcIncr hc WF VALID)
                    exact tr_condition.tr_CEcondition map pr a b c ns ntrue nfalse nb nc hA hB hC
    | CElet b c =>
        change RTLgen.bind RTLgen.new_reg
          (fun r => RTLgen.bind (RTLgen.transl_condexpr (RTLgen.add_letvar map r) c ntrue nfalse)
            (fun nc => RTLgen.transl_expr map b r nc)) s = .OK ns s' INCR at TR
        cases hnew : RTLgen.new_reg s with
        | Error msg => simp [RTLgen.bind, hnew] at TR
        | OK r s0 hnewIncr =>
            simp [RTLgen.bind, hnew] at TR
            cases hbody : RTLgen.transl_condexpr (RTLgen.add_letvar map r) c ntrue nfalse s0 with
            | Error msg => simp [RTLgen.bind, hbody] at TR
            | OK nc s1 hbodyIncr =>
                simp [RTLgen.bind, hbody] at TR
                cases hbound : RTLgen.transl_expr map b r nc s1 with
                | Error msg => simp [RTLgen.bind, hbound] at TR
                | OK ns2 sfin hboundIncr =>
                    simp [RTLgen.bind, hbound, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    have hr0 := test_new_reg_valid s r s0 hnewIncr hnew
                    have hmap0 := test_map_valid_incr map s s0 hnewIncr WF
                    have hmapLet := add_letvar_valid map s0 r hmap0 hr0
                    have hmap1 := test_map_valid_incr (RTLgen.add_letvar map r)
                        s0 s1 hbodyIncr hmapLet
                    have hmap1orig := test_map_valid_incr map s s1
                        (RTLgen.state_incr_trans s s0 s1 hnewIncr hbodyIncr) WF
                    have hpr0 := regs_valid_incr s s0 pr hnewIncr VALID
                    have hpr1 := regs_valid_incr s0 s1 pr hbodyIncr hpr0
                    have hr1 := reg_valid_incr r s0 s1 hbodyIncr hr0
                    have hr_not_map : ¬ reg_in_map map r :=
                      new_reg_not_in_map s s0 map r hnewIncr hnew WF
                    have hr_fresh_s : reg_fresh r s := test_new_reg_fresh s r s0 hnewIncr hnew
                    have hr_not_pr : ¬ r ∈ pr := by
                      intro hmem
                      exact valid_fresh_absurd r s (VALID r hmem) hr_fresh_s
                    have hbodyProof := tr_condition_incr s1 s' hboundIncr
                      (RTLgen.add_letvar map r) pr c nc ntrue nfalse
                      (aux_cond c (RTLgen.add_letvar map r) ntrue nfalse s0 nc s1 pr
                        hbodyIncr hbody hmapLet hpr0)
                    exact tr_condition.tr_CElet map pr b c ns ntrue nfalse r nc
                      hr_not_map
                      (aux_expr b map r nc s1 ns s' pr hboundIncr hbound hmap1orig
                        (target_reg_ok.target_reg_other b r hr_not_map hr_not_pr)
                        hpr1 hr1)
                      hbodyProof
end

private theorem test_mutual :
    transl_expr_charactStatement ∧ transl_exprlist_charactStatement ∧ transl_condexpr_charactStatement := by
  exact ⟨aux_expr, aux_list, aux_cond⟩


theorem transl_expr_charact : transl_expr_charactStatement := test_mutual.1

theorem transl_exprlist_charact : transl_exprlist_charactStatement := test_mutual.2.1

theorem transl_condexpr_charact : transl_condexpr_charactStatement := test_mutual.2.2

end CompCert4Lean.Backend.RTLgenspec

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

theorem alloc_optreg_map_ok : alloc_optreg_map_okStatement := by
  intro map optid s1 r s2 i hmap halloc
  cases optid with
  | none =>
      apply reg_map_ok.reg_map_ok_novar
      exact new_reg_not_in_map s1 s2 map r i halloc hmap
  | some id =>
      apply reg_map_ok.reg_map_ok_somevar
      change RTLgen.find_var map id s1 = .OK r s2 i at halloc
      cases hfind : PTree.get id map.map_vars with
      | none =>
          simp [RTLgen.find_var, RTLgen.error, hfind] at halloc
      | some r0 =>
          simp [RTLgen.find_var, hfind, RTLgen.ret] at halloc
          rcases halloc with ⟨hr, hs⟩
          cases hr
          cases hs
          rfl

end CompCert4Lean.Backend.RTLgenspec

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

theorem tr_exitexpr_incr : tr_exitexpr_incrStatement := by
  intro s1 s2 EXT map a ns nexits htr
  induction htr with
  | tr_XEcond map x n nexits h =>
      exact tr_exitexpr.tr_XEcond map x n nexits h
  | tr_XEjumptable map a tbl ns nexits n1 r tbl' hjt harg hcode =>
      apply tr_exitexpr.tr_XEjumptable
      · exact hjt
      · exact tr_expr_incr s1 s2 EXT map [] a ns n1 r none harg
      · exact instr_at_incr s1 s2 n1 _ EXT hcode
  | tr_XEcondition map a1 a2 a3 ns nexits n2 n3 hcond h2 h3 ih2 ih3 =>
      apply tr_exitexpr.tr_XEcondition
      · exact tr_condition_incr s1 s2 EXT map [] a1 ns n2 n3 hcond
      · exact ih2
      · exact ih3
  | tr_XElet map a b ns nexits r n1 hfresh hbound hbody ihbody =>
      apply tr_exitexpr.tr_XElet
      · exact hfresh
      · exact tr_expr_incr s1 s2 EXT map [] a ns n1 r none hbound
      · exact ihbody

end CompCert4Lean.Backend.RTLgenspec

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

private theorem rtlgenspec_transl_exit_charact
    (nexits : List RTL.node) (n : Nat) (s : RTLgen.state)
    (ne : RTL.node) (s' : RTLgen.state) (incr : state_incr s s') :
    RTLgen.transl_exit nexits n s = .OK ne s' incr →
      nth_error nexits n = some ne ∧ s' = s := by
  intro h
  cases hget : nexits[n]? with
  | none =>
      simp [RTLgen.transl_exit, hget, RTLgen.error] at h
  | some ne0 =>
      have hnth := rtlgenspec_getElem?_nth_error nexits n _ hget
      simp [RTLgen.transl_exit, hget, RTLgen.ret] at h
      rcases h with ⟨hne, hs⟩
      cases hne
      cases hs
      exact ⟨hnth, rfl⟩

theorem transl_jumptable_charact : transl_jumptable_charactStatement := by
  intro nexits tbl
  induction tbl with
  | nil =>
      intro s nl s' incr h
      change RTLgen.ret [] s = .OK nl s' incr at h
      cases h
      constructor
      · intro v act hv
        simp [tr_jumptable, CompCert4Lean.Lib.Coqlib.list_nth_z] at hv
      · rfl
  | cons t tl ih =>
      intro s nl s' incr h
      change RTLgen.bind (RTLgen.transl_exit nexits t)
          (fun n1 => RTLgen.bind (RTLgen.transl_jumptable nexits tl)
            (fun nl' => RTLgen.ret (n1 :: nl'))) s = .OK nl s' incr at h
      cases hfirst : RTLgen.transl_exit nexits t s with
      | Error msg =>
          simp [RTLgen.bind, hfirst] at h
      | OK n1 sm i1 =>
          simp [RTLgen.bind, hfirst] at h
          cases htail : RTLgen.transl_jumptable nexits tl sm with
          | Error msg =>
              simp [RTLgen.bind, htail] at h
          | OK nlmid sn i2 =>
              simp [RTLgen.bind, htail, RTLgen.ret] at h
              rcases h with ⟨hnl, hs⟩
              cases hnl
              cases hs
              have hfirst' := rtlgenspec_transl_exit_charact nexits t s n1 sm i1 hfirst
              have htail' := ih sm nlmid s' i2 htail
              constructor
              · intro v act hv
                cases hz : zeq v Z0 with
                | left hv0 =>
                    cases hv0
                    have hvt : (some t : Option Nat) = some act := by
                      simpa [CompCert4Lean.Lib.Coqlib.list_nth_z, hz] using hv
                    cases hvt
                    exact ⟨n1, by simp [CompCert4Lean.Lib.Coqlib.list_nth_z, hz], hfirst'.1⟩
                | right hv0 =>
                    have hv' : list_nth_z tl (ZArith.BinInt.Z.pred v) = some act := by
                      simpa [CompCert4Lean.Lib.Coqlib.list_nth_z, hz] using hv
                    rcases htail'.1 (ZArith.BinInt.Z.pred v) act hv' with ⟨n, hn, ha⟩
                    exact ⟨n, by simpa [CompCert4Lean.Lib.Coqlib.list_nth_z, hz] using hn, ha⟩
              · exact htail'.2.trans hfirst'.2

end CompCert4Lean.Backend.RTLgenspec

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

mutual
  private def assign_expr (id : ident) (a : expr) (map : RTLgen.mapping) (rd : reg) (nd : RTL.node)
      (s : RTLgen.state) (ns : RTL.node) (s' : RTLgen.state) (INCR : state_incr s s') :
      RTLgen.transl_expr map a rd nd s = .OK ns s' INCR →
      map_valid map s → reg_map_ok map rd (some id) →
      tr_expr s'.st_code map [] a ns nd rd (some id) := by
    intro TR WF OK
    cases a with
    | Evar v =>
        cases hfind : PTree.get v map.map_vars with
        | none =>
            change RTLgen.bind (RTLgen.find_var map v)
              (fun r => RTLgen.add_move r rd nd) s = _ at TR
            simp [RTLgen.find_var, hfind, RTLgen.error, RTLgen.bind] at TR
        | some r0 =>
            change RTLgen.bind (RTLgen.find_var map v)
              (fun r => RTLgen.add_move r rd nd) s = _ at TR
            rw [show RTLgen.find_var map v = RTLgen.ret r0 by simp [RTLgen.find_var, hfind]] at TR
            simp [RTLgen.bind] at TR
            by_cases hr : r0 = rd
            · simp [RTLgen.add_move, hr, RTLgen.ret, RTLgen.bind] at TR
              rcases TR with ⟨hns, hs⟩
              cases hns
              cases hs
              cases hr
              apply tr_expr.tr_Evar
              · exact hfind
              · exact Or.inr ⟨OK, by simp⟩
              · exact tr_move.tr_move_0 _ _
            · simp [RTLgen.add_move, hr, RTLgen.add_instr, RTLgen.ret, RTLgen.bind] at TR
              injection TR with hns hs
              cases hns
              cases hs
              apply tr_expr.tr_Evar
              · exact hfind
              · exact Or.inr ⟨OK, by simp⟩
              · apply tr_move.tr_move_1
                change PTree.get s.st_nextnode
                  (PTree.set s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code) = _
                have hx := PTree.getSet_equation (A := RTL.instruction)
                  s.st_nextnode s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code
                rw [hx]
                simp
    | Eop op al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Iop op rl rd nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Iop op rl rd nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Eop
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' [] htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al [] s rl sm hincr WF
                          (by intro r hr; simp at hr) halloc)
                        (by intro r hr; simp at hr) hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Iop op rl rd nd) no sn hinstr hadd)
                    · exact OK
                    · simp
    | Eload chunk addr al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Iload chunk addr rl rd nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Iload chunk addr rl rd nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Eload
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' [] htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al [] s rl sm hincr WF
                          (by intro r hr; simp at hr) halloc)
                        (by intro r hr; simp at hr) hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Iload chunk addr rl rd nd) no sn hinstr hadd)
                    · exact OK
                    · simp
    | Econdition a ifso ifnot =>
        change RTLgen.bind (RTLgen.transl_expr map ifnot rd nd)
          (fun nfalse => RTLgen.bind (RTLgen.transl_expr map ifso rd nd)
            (fun ntrue => RTLgen.transl_condexpr map a ntrue nfalse)) s = .OK ns s' INCR at TR
        cases hfalse : RTLgen.transl_expr map ifnot rd nd s with
        | Error msg => simp [RTLgen.bind, hfalse] at TR
        | OK nfalse s0 hfalseIncr =>
            simp [RTLgen.bind, hfalse] at TR
            cases htrue : RTLgen.transl_expr map ifso rd nd s0 with
            | Error msg => simp [RTLgen.bind, htrue] at TR
            | OK ntrue s1 htrueIncr =>
                simp [RTLgen.bind, htrue] at TR
                cases hcond : RTLgen.transl_condexpr map a ntrue nfalse s1 with
                | Error msg => simp [RTLgen.bind, hcond] at TR
                | OK ns2 sfin hcondIncr =>
                    simp [RTLgen.bind, hcond, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    have hfalseTo : state_incr s0 s' :=
                      RTLgen.state_incr_trans s0 s1 s' htrueIncr hcondIncr
                    have hmap0 := test_map_valid_incr map s s0 hfalseIncr WF
                    have hmap1 := test_map_valid_incr map s0 s1 htrueIncr hmap0
                    apply tr_expr.tr_Econdition
                    · exact aux_cond a map ntrue nfalse s1 ns s' [] hcondIncr
                        hcond hmap1 (by intro r hr; simp at hr)
                    · exact tr_expr_incr s1 s' hcondIncr map [] ifso ntrue nd rd (some id)
                        (assign_expr id ifso map rd nd s0 ntrue s1 htrueIncr htrue hmap0 OK)
                    · exact tr_expr_incr s0 s' hfalseTo map [] ifnot nfalse nd rd (some id)
                        (assign_expr id ifnot map rd nd s nfalse s0 hfalseIncr hfalse WF OK)
    | Elet b c =>
        change RTLgen.bind RTLgen.new_reg
          (fun r => RTLgen.bind (RTLgen.transl_expr (RTLgen.add_letvar map r) c rd nd)
            (fun nc => RTLgen.transl_expr map b r nc)) s = .OK ns s' INCR at TR
        cases hnew : RTLgen.new_reg s with
        | Error msg => simp [RTLgen.bind, hnew] at TR
        | OK r s0 hnewIncr =>
            simp [RTLgen.bind, hnew] at TR
            cases hbody : RTLgen.transl_expr (RTLgen.add_letvar map r) c rd nd s0 with
            | Error msg => simp [RTLgen.bind, hbody] at TR
            | OK nc s1 hbodyIncr =>
                simp [RTLgen.bind, hbody] at TR
                cases hbound : RTLgen.transl_expr map b r nc s1 with
                | Error msg => simp [RTLgen.bind, hbound] at TR
                | OK ns2 sfin hboundIncr =>
                    simp [RTLgen.bind, hbound, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    have hr0 := test_new_reg_valid s r s0 hnewIncr hnew
                    have hmap0 := test_map_valid_incr map s s0 hnewIncr WF
                    have hmapLet := add_letvar_valid map s0 r hmap0 hr0
                    have hmap1orig := test_map_valid_incr map s s1
                      (RTLgen.state_incr_trans s s0 s1 hnewIncr hbodyIncr) WF
                    have hr1 := reg_valid_incr r s0 s1 hbodyIncr hr0
                    have hr_not_map : ¬ reg_in_map map r :=
                      new_reg_not_in_map s s0 map r hnewIncr hnew WF
                    have hr_fresh_s : reg_fresh r s := test_new_reg_fresh s r s0 hnewIncr hnew
                    have hr_not_pr : ¬ r ∈ [] := by simp
                    have hOKmapLet : reg_map_ok (RTLgen.add_letvar map r) rd (some id) := by
                      cases OK with
                      | reg_map_ok_somevar id0 hget =>
                          apply reg_map_ok.reg_map_ok_somevar
                          simpa [RTLgen.add_letvar] using hget
                    apply tr_expr.tr_Elet
                    · exact hr_not_map
                    · exact aux_expr b map r nc s1 ns s' [] hboundIncr hbound hmap1orig
                        (target_reg_ok.target_reg_other b r hr_not_map hr_not_pr)
                        (by intro x hx; simp at hx) hr1
                    · exact tr_expr_incr s1 s' hboundIncr
                        (RTLgen.add_letvar map r) [] c nc nd rd (some id)
                        (assign_expr id c (RTLgen.add_letvar map r) rd nd s0 nc s1 hbodyIncr hbody
                          hmapLet hOKmapLet)
    | Eletvar n =>
        cases hfind : map.map_letvars[n]? with
        | none =>
            change RTLgen.bind (RTLgen.find_letvar map n)
              (fun r => RTLgen.add_move r rd nd) s = _ at TR
            simp [RTLgen.find_letvar, RTLgen.error, RTLgen.bind, hfind] at TR
        | some r0 =>
            change RTLgen.bind (RTLgen.find_letvar map n)
              (fun r => RTLgen.add_move r rd nd) s = _ at TR
            rw [show RTLgen.find_letvar map n = RTLgen.ret r0 by
              simp [RTLgen.find_letvar, hfind]] at TR
            simp [RTLgen.bind] at TR
            by_cases hr : r0 = rd
            · simp [RTLgen.add_move, hr, RTLgen.ret] at TR
              rcases TR with ⟨hns, hs⟩
              cases hns
              cases hs
              have hlet0 := test_getElem_nth map.map_letvars n r0 hfind
              cases hr
              apply tr_expr.tr_Eletvar
              · exact hlet0
              · exact Or.inr ⟨OK, by simp⟩
              · exact tr_move.tr_move_0 _ _
            · simp [RTLgen.add_move, hr, RTLgen.add_instr, RTLgen.ret] at TR
              injection TR with hns hs
              cases hns
              cases hs
              apply tr_expr.tr_Eletvar
              · exact test_getElem_nth map.map_letvars n r0 hfind
              · exact Or.inr ⟨OK, by simp⟩
              · apply tr_move.tr_move_1
                change PTree.get s.st_nextnode
                  (PTree.set s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code) = _
                have hx := PTree.getSet_equation (A := RTL.instruction)
                  s.st_nextnode s.st_nextnode (RTL.instruction.Iop Omove [r0] rd nd) s.st_code
                rw [hx]
                simp
    | Ebuiltin ef al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Ebuiltin
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' [] htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al [] s rl sm hincr WF
                          (by intro r hr; simp at hr) halloc)
                        (by intro r hr; simp at hr) hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Ibuiltin ef (rl.map BA) (BR rd) nd) no sn hinstr hadd)
                    · exact OK
                    · simp
    | Eexternal ext sg al =>
        change RTLgen.bind (RTLgen.alloc_regs map al)
          (fun rl => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Icall sg (.inr ext) rl rd nd))
            (fun no => RTLgen.transl_exprlist map al rl no)) s = .OK ns s' INCR at TR
        cases halloc : RTLgen.alloc_regs map al s with
        | Error msg => simp [RTLgen.bind, halloc] at TR
        | OK rl sm hincr =>
            simp [RTLgen.bind, halloc] at TR
            cases hadd : RTLgen.add_instr (RTL.instruction.Icall sg (.inr ext) rl rd nd) sm with
            | Error msg => simp [RTLgen.bind, hadd] at TR
            | OK no sn hinstr =>
                simp [RTLgen.bind, hadd] at TR
                cases htail : RTLgen.transl_exprlist map al rl no sn with
                | Error msg => simp [RTLgen.bind, htail] at TR
                | OK ns2 sfin htailincr =>
                    simp [RTLgen.bind, htail, RTLgen.ret] at TR
                    rcases TR with ⟨hns, hs⟩
                    cases hns
                    cases hs
                    apply tr_expr.tr_Eexternal
                    have hssn := RTLgen.state_incr_trans s sm sn hincr hinstr
                    have hmap_sn := test_map_valid_incr map s sn hssn WF
                    have hrl_sm := test_alloc_regs_valid map al rl s sm hincr WF halloc
                    have hrl_sn := regs_valid_incr sm sn rl hinstr hrl_sm
                    · exact aux_list al map rl no sn ns s' [] htailincr
                        htail hmap_sn
                        (alloc_regs_target_ok map al [] s rl sm hincr WF
                          (by intro r hr; simp at hr) halloc)
                        (by intro r hr; simp at hr) hrl_sn
                    · exact instr_at_incr sn s' no _ htailincr
                        (test_add_instr_code sm (RTL.instruction.Icall sg (.inr ext) rl rd nd) no sn hinstr hadd)
                    · exact OK
                    · simp

end

theorem transl_expr_assign_charact : transl_expr_assign_charactStatement := by
  intro id a map rd nd s ns s' INCR TR WF OK
  exact assign_expr id a map rd nd s ns s' INCR TR WF OK

end CompCert4Lean.Backend.RTLgenspec

namespace CompCert4Lean.Backend.RTLgenspec

theorem tr_stmt_incr : tr_stmt_incrStatement := by
  intro s1 s2 EXT map stmt ns nd nexits ngoto nret rret htr
  induction htr with
  | tr_Sskip ns nexits ngoto nret rret =>
      exact tr_stmt.tr_Sskip ns nexits ngoto nret rret
  | tr_Sassign id a ns nd nexits ngoto nret rret r hmap harg =>
      apply tr_stmt.tr_Sassign
      · exact hmap
      · exact tr_expr_incr s1 s2 EXT map [] a ns nd r (some id) harg
  | tr_Sstore chunk addr al b ns nd nexits ngoto nret rret rd n1 rl n2 hargs hvalue hcode =>
      apply tr_stmt.tr_Sstore
      · exact tr_exprlist_incr s1 s2 EXT map [] al ns n1 rl hargs
      · exact tr_expr_incr s1 s2 EXT map rl b n1 n2 rd none hvalue
      · exact instr_at_incr s1 s2 n2 _ EXT hcode
  | tr_Scall optid sig b cl ns nd nexits ngoto nret rret rd n1 rf n2 rargs
      hcallee hargs hcode hmap =>
      apply tr_stmt.tr_Scall
      · exact tr_expr_incr s1 s2 EXT map [] b ns n1 rf none hcallee
      · exact tr_exprlist_incr s1 s2 EXT map [rf] cl n1 n2 rargs hargs
      · exact instr_at_incr s1 s2 n2 _ EXT hcode
      · exact hmap
  | tr_Scall_imm optid sig id cl ns nd nexits ngoto nret rret rd n2 rargs hargs hcode hmap =>
      apply tr_stmt.tr_Scall_imm
      · exact tr_exprlist_incr s1 s2 EXT map [] cl ns n2 rargs hargs
      · exact instr_at_incr s1 s2 n2 _ EXT hcode
      · exact hmap
  | tr_Stailcall sig b cl ns nd nexits ngoto nret rret n1 rf n2 rargs hcallee hargs hcode =>
      apply tr_stmt.tr_Stailcall
      · exact tr_expr_incr s1 s2 EXT map [] b ns n1 rf none hcallee
      · exact tr_exprlist_incr s1 s2 EXT map [rf] cl n1 n2 rargs hargs
      · exact instr_at_incr s1 s2 n2 _ EXT hcode
  | tr_Stailcall_imm sig id cl ns nd nexits ngoto nret rret n2 rargs hargs hcode =>
      apply tr_stmt.tr_Stailcall_imm
      · exact tr_exprlist_incr s1 s2 EXT map [] cl ns n2 rargs hargs
      · exact instr_at_incr s1 s2 n2 _ EXT hcode
  | tr_Sbuiltin res ef args ns nd nexits ngoto nret rret res' n1 rargs hargs hcode hres =>
      apply tr_stmt.tr_Sbuiltin
      · exact tr_exprlist_incr s1 s2 EXT map []
          (RTLgen.exprlist_of_expr_list
            (CompCert4Lean.Common.AST.params_of_builtin_args args)) ns n1 rargs hargs
      · exact instr_at_incr s1 s2 n1 _ EXT hcode
      · exact hres
  | tr_Sseq s1' s2' ns nd nexits ngoto nret rret n h2 h1 ih2 ih1 =>
      exact tr_stmt.tr_Sseq s1' s2' ns nd nexits ngoto nret rret n ih2 ih1
  | tr_Sifthenelse a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse
      htrue hfalse hcond ihtrue ihfalse =>
      apply tr_stmt.tr_Sifthenelse
      · exact ihtrue
      · exact ihfalse
      · exact tr_condition_incr s1 s2 EXT map [] a ns ntrue nfalse hcond
  | tr_Sloop sbody ns nd nexits ngoto nret rret nloop nend hbody hstart hend ihbody =>
      apply tr_stmt.tr_Sloop
      · exact ihbody
      · exact instr_at_incr s1 s2 ns _ EXT hstart
      · exact instr_at_incr s1 s2 nend _ EXT hend
  | tr_Sblock sbody ns nd nexits ngoto nret rret hbody ihbody =>
      exact tr_stmt.tr_Sblock sbody ns nd nexits ngoto nret rret ihbody
  | tr_Sexit n ns nd nexits ngoto nret rret h =>
      exact tr_stmt.tr_Sexit n ns nd nexits ngoto nret rret h
  | tr_Sswitch a ns nd nexits ngoto nret rret h =>
      exact tr_stmt.tr_Sswitch a ns nd nexits ngoto nret rret
        (tr_exitexpr_incr s1 s2 EXT map a ns nexits h)
  | tr_Sreturn_none nret nd nexits ngoto rret =>
      exact tr_stmt.tr_Sreturn_none nret nd nexits ngoto rret
  | tr_Sreturn_some a ns nd nexits ngoto nret rret h =>
      exact tr_stmt.tr_Sreturn_some a ns nd nexits ngoto nret rret
        (tr_expr_incr s1 s2 EXT map [] a ns nret rret none h)
  | tr_Slabel lbl s ns nd nexits ngoto nret rret n hgoto hcode hbody ihbody =>
      apply tr_stmt.tr_Slabel
      · exact hgoto
      · exact instr_at_incr s1 s2 n _ EXT hcode
      · exact ihbody
  | tr_Sgoto lbl ns nd nexits ngoto nret rret h =>
      exact tr_stmt.tr_Sgoto lbl ns nd nexits ngoto nret rret h

end CompCert4Lean.Backend.RTLgenspec

namespace CompCert4Lean.Backend.RTLgenspec

theorem transl_exit_charact : transl_exit_charactStatement :=
  rtlgenspec_transl_exit_charact

end CompCert4Lean.Backend.RTLgenspec

namespace CompCert4Lean.Backend.RTLgenspec

open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTLgen

theorem transl_exitexpr_charact : transl_exitexpr_charactStatement := by
  intro nexits a
  induction a with
  | XEexit n =>
      intro map s ns s' INCR TR WF
      exact tr_exitexpr.tr_XEcond map n ns nexits
        (transl_exit_charact nexits n s ns s' INCR TR).1
  | XEjumptable a tbl =>
      intro map s ns s' INCR TR WF
      change RTLgen.bind (RTLgen.alloc_reg map a)
        (fun r => RTLgen.bind (RTLgen.transl_jumptable nexits tbl)
          (fun tbl' => RTLgen.bind (RTLgen.add_instr (RTL.instruction.Ijumptable r tbl'))
            (fun n1 => RTLgen.transl_expr map a r n1))) s = .OK ns s' INCR at TR
      cases halloc : RTLgen.alloc_reg map a s with
      | Error msg => simp [RTLgen.bind, halloc] at TR
      | OK r s0 ialloc =>
          simp [RTLgen.bind, halloc] at TR
          cases hjt : RTLgen.transl_jumptable nexits tbl s0 with
          | Error msg => simp [RTLgen.bind, hjt] at TR
          | OK tbl' s1 ijt =>
              simp [RTLgen.bind, hjt] at TR
              cases hadd : RTLgen.add_instr (RTL.instruction.Ijumptable r tbl') s1 with
              | Error msg => simp [RTLgen.bind, hadd] at TR
              | OK n1 s2 iadd =>
                  simp [RTLgen.bind, hadd] at TR
                  cases harg : RTLgen.transl_expr map a r n1 s2 with
                  | Error msg => simp [RTLgen.bind, harg] at TR
                  | OK ns2 sfin iarg =>
                      simp [RTLgen.bind, harg] at TR
                      rcases TR with ⟨hns, hs⟩
                      cases hns
                      cases hs
                      have i02 := RTLgen.state_incr_trans s0 s1 s2 ijt iadd
                      have is2 := RTLgen.state_incr_trans s s0 s2 ialloc i02
                      apply tr_exitexpr.tr_XEjumptable
                      · exact (transl_jumptable_charact nexits tbl s0 tbl' s1 ijt hjt).1
                      · exact transl_expr_charact a map r n1 s2 ns s' [] iarg harg
                          (test_map_valid_incr map s s2 is2 WF)
                          (alloc_reg_target_ok map [] s a r s0 ialloc WF
                            (by intro r hr; simp at hr) halloc)
                          (by intro r hr; simp at hr)
                          (reg_valid_incr r s0 s2 i02
                            (test_alloc_reg_valid map a r s s0 ialloc WF halloc))
                      · exact instr_at_incr s2 s' n1 _ iarg
                          (test_add_instr_code s1 (RTL.instruction.Ijumptable r tbl')
                            n1 s2 iadd hadd)
  | XEcondition a b c ihb ihc =>
      intro map s ns s' INCR TR WF
      change RTLgen.bind (RTLgen.transl_exitexpr map c nexits)
        (fun nc => RTLgen.bind (RTLgen.transl_exitexpr map b nexits)
          (fun nb => RTLgen.transl_condexpr map a nb nc)) s = .OK ns s' INCR at TR
      cases hc : RTLgen.transl_exitexpr map c nexits s with
      | Error msg => simp [RTLgen.bind, hc] at TR
      | OK nc s0 ic =>
          simp [RTLgen.bind, hc] at TR
          cases hb : RTLgen.transl_exitexpr map b nexits s0 with
          | Error msg => simp [RTLgen.bind, hb] at TR
          | OK nb s1 ib =>
              simp [RTLgen.bind, hb] at TR
              cases ha : RTLgen.transl_condexpr map a nb nc s1 with
              | Error msg => simp [RTLgen.bind, ha] at TR
              | OK ns2 sfin ia =>
                  simp [RTLgen.bind, ha] at TR
                  rcases TR with ⟨hns, hs⟩
                  cases hns
                  cases hs
                  have hmap0 := test_map_valid_incr map s s0 ic WF
                  have hmap1 := test_map_valid_incr map s0 s1 ib hmap0
                  exact tr_exitexpr.tr_XEcondition map a b c ns nexits nb nc
                    (transl_condexpr_charact a map nb nc s1 ns s' [] ia ha hmap1
                      (by intro r hr; simp at hr))
                    (tr_exitexpr_incr s1 s' ia map b nb nexits
                      (ihb map s0 nb s1 ib hb hmap0))
                    (tr_exitexpr_incr s0 s' (RTLgen.state_incr_trans s0 s1 s' ib ia)
                      map c nc nexits (ihc map s nc s0 ic hc WF))
  | XElet a b ih =>
      intro map s ns s' INCR TR WF
      change RTLgen.bind RTLgen.new_reg
        (fun r => RTLgen.bind (RTLgen.transl_exitexpr (RTLgen.add_letvar map r) b nexits)
          (fun n1 => RTLgen.transl_expr map a r n1)) s = .OK ns s' INCR at TR
      cases hnew : RTLgen.new_reg s with
      | Error msg => simp [RTLgen.bind, hnew] at TR
      | OK r s0 inew =>
          simp [RTLgen.bind, hnew] at TR
          cases hbody : RTLgen.transl_exitexpr (RTLgen.add_letvar map r) b nexits s0 with
          | Error msg => simp [RTLgen.bind, hbody] at TR
          | OK n1 s1 ibody =>
              simp [RTLgen.bind, hbody] at TR
              cases hbound : RTLgen.transl_expr map a r n1 s1 with
              | Error msg => simp [RTLgen.bind, hbound] at TR
              | OK ns2 sfin ibound =>
                  simp [RTLgen.bind, hbound] at TR
                  rcases TR with ⟨hns, hs⟩
                  cases hns
                  cases hs
                  have hr0 := test_new_reg_valid s r s0 inew hnew
                  have hmap0 := test_map_valid_incr map s s0 inew WF
                  have hmap1 := test_map_valid_incr map s0 s1 ibody hmap0
                  have hfresh := new_reg_not_in_map s s0 map r inew hnew WF
                  exact tr_exitexpr.tr_XElet map a b ns nexits r n1 hfresh
                    (transl_expr_charact a map r n1 s1 ns s' [] ibound hbound hmap1
                      (target_reg_ok.target_reg_other a r hfresh (by simp))
                      (by intro r hr; simp at hr)
                      (reg_valid_incr r s0 s1 ibody hr0))
                    (tr_exitexpr_incr s1 s' ibound (RTLgen.add_letvar map r) b n1 nexits
                      (ih (RTLgen.add_letvar map r) s0 n1 s1 ibody hbody
                        (add_letvar_valid map s0 r hmap0 hr0)))

end CompCert4Lean.Backend.RTLgenspec
