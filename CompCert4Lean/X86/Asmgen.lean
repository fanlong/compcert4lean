import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.AST
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.Asm
import CompCert4Lean.Backend.Mach

namespace CompCert4Lean.X86.Asmgen

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.Asm
open CompCert4Lean.Backend.Mach

private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev int := CompCert4Lean.Lib.Integers.Int.int
private abbrev int64 := CompCert4Lean.Lib.Integers.Int64.int
private abbrev ptrofs := CompCert4Lean.Lib.Integers.Ptrofs.int
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev signature := CompCert4Lean.Common.AST.signature
private abbrev code := CompCert4Lean.X86.Asm.code
private abbrev res := CompCert4Lean.Common.Errors.res
private abbrev mreg := CompCert4Lean.X86.Machregs.mreg
private abbrev ireg := CompCert4Lean.X86.Asm.ireg
private abbrev freg := CompCert4Lean.X86.Asm.freg
private abbrev preg := CompCert4Lean.X86.Asm.preg
private abbrev instruction := CompCert4Lean.X86.Asm.instruction
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub

private def decEqSumbool {A : Type} [DecidableEq A] (x y : A) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

private def ofString (s : String) :
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

private def fail {A : Type} (s : String) : res A := .Error (msg (ofString s))

private def bindRes {A B : Type} (x : res A) (f : A → res B) : res B :=
  CompCert4Lean.Common.Errors.bind x f

private def sumboolBool {P Q : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

instance : Monad CompCert4Lean.Common.Errors.res where
  pure := fun x => .OK x
  bind := fun x f => CompCert4Lean.Common.Errors.bind x f

private def mreg_eq (x y : mreg) : Bool :=
  match CompCert4Lean.Backend.Mach.RegEq.eq x y with
  | .left _ => true
  | .right _ => false

private def ireg_eq (x y : ireg) : Bool := decide (x = y)

private def freg_eq (x y : freg) : Bool := decide (x = y)

private def preg_eq (x y : preg) : Bool := decide (x = y)

private def isIntZero (n : int) : Bool :=
  CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero
private def isLongZero (n : int64) : Bool :=
  CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.zero

private def Archi_ptr64 : Bool := CompCert4Lean.X86_64.Archi.ptr64

/-! Register extraction and small instruction constructors. -/

def ireg_of (r : mreg) : res ireg :=
  match CompCert4Lean.X86.Asm.preg_of r with
  | .IR mr => .OK mr
  | _ => fail "Asmgen.ireg_of"

def freg_of (r : mreg) : res freg :=
  match CompCert4Lean.X86.Asm.preg_of r with
  | .FR mr => .OK mr
  | _ => fail "Asmgen.freg_of"

def mk_mov (rd rs : preg) (k : code) : res code :=
  match rd, rs with
  | .IR rd, .IR rs => .OK (.Pmov_rr rd rs :: k)
  | .FR rd, .FR rs => .OK (.Pmovsd_ff rd rs :: k)
  | _, _ => fail "Asmgen.mk_mov"

def mk_shrximm (n : int) (k : code) : res code :=
  let p := CompCert4Lean.Lib.Integers.Int.sub
    (CompCert4Lean.Lib.Integers.Int.shl CompCert4Lean.Lib.Integers.Int.one n)
    CompCert4Lean.Lib.Integers.Int.one
  .OK (.Ptestl_rr .RAX .RAX ::
      .Pleal .RCX (.Addrmode (some .RAX) none
        (Sum.inl (CompCert4Lean.Lib.Integers.Int.unsigned p))) ::
      .Pcmov .Cond_l .RAX .RCX ::
      .Psarl_ri .RAX n :: k)

def mk_shrxlimm (n : int) (k : code) : res code :=
  .OK (if isIntZero n then .Pmov_rr .RAX .RAX :: k else
      .Pcqto ::
      .Pshrq_ri .RDX
        (CompCert4Lean.Lib.Integers.Int.sub
          (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 64)) n) ::
      .Pleaq .RAX (.Addrmode (some .RAX) (some (.RDX, ZArith.BinInt.Z.of_nat 1))
        (Sum.inl z0)) ::
      .Psarq_ri .RAX n :: k)

def low_ireg (r : ireg) : Bool :=
  match r with
  | .RAX | .RBX | .RCX | .RDX => true
  | _ => false

def mk_intconv (mk : ireg → ireg → instruction) (rd rs : ireg) (k : code) : res code :=
  if Archi_ptr64 || low_ireg rs then .OK (mk rd rs :: k)
  else .OK (.Pmov_rr .RAX rs :: mk rd .RAX :: k)

def addressing_mentions (addr : addrmode) (r : ireg) : Bool :=
  match addr with
  | .Addrmode base displ _ =>
      (match base with | some r' => ireg_eq r r' | none => false) ||
      (match displ with | some (r', _) => ireg_eq r r' | none => false)

def mk_storebyte (addr : addrmode) (rs : ireg) (k : code) : res code :=
  if Archi_ptr64 || low_ireg rs then .OK (.Pmovb_mr addr rs :: k)
  else if addressing_mentions addr .RAX then
    .OK (.Pleal .RCX addr :: .Pmov_rr .RAX rs ::
      .Pmovb_mr (.Addrmode (some .RCX) none (Sum.inl z0)) .RAX :: k)
  else .OK (.Pmov_rr .RAX rs :: .Pmovb_mr addr .RAX :: k)

def loadind (base : ireg) (ofs : ptrofs) (ty : typ) (dst : mreg) (k : code) : res code :=
  let a := .Addrmode (some base) none
    (Sum.inl (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs))
  match ty, CompCert4Lean.X86.Asm.preg_of dst with
  | .Tint, .IR r => .OK (.Pmovl_rm r a :: k)
  | .Tlong, .IR r => .OK (.Pmovq_rm r a :: k)
  | .Tsingle, .FR r => .OK (.Pmovss_fm r a :: k)
  | .Tsingle, .ST0 => .OK (.Pflds_m a :: k)
  | .Tfloat, .FR r => .OK (.Pmovsd_fm r a :: k)
  | .Tfloat, .ST0 => .OK (.Pfldl_m a :: k)
  | .Tany32, .IR r => if Archi_ptr64 then fail "Asmgen.loadind1" else .OK (.Pmov_rm_a r a :: k)
  | .Tany64, .IR r => if Archi_ptr64 then .OK (.Pmov_rm_a r a :: k) else fail "Asmgen.loadind2"
  | .Tany64, .FR r => .OK (.Pmovsd_fm_a r a :: k)
  | _, _ => fail "Asmgen.loadind"

def storeind (src : mreg) (base : ireg) (ofs : ptrofs) (ty : typ) (k : code) : res code :=
  let a := .Addrmode (some base) none
    (Sum.inl (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs))
  match ty, CompCert4Lean.X86.Asm.preg_of src with
  | .Tint, .IR r => .OK (.Pmovl_mr a r :: k)
  | .Tlong, .IR r => .OK (.Pmovq_mr a r :: k)
  | .Tsingle, .FR r => .OK (.Pmovss_mf a r :: k)
  | .Tsingle, .ST0 => .OK (.Pfstps_m a :: k)
  | .Tfloat, .FR r => .OK (.Pmovsd_mf a r :: k)
  | .Tfloat, .ST0 => .OK (.Pfstpl_m a :: k)
  | .Tany32, .IR r => if Archi_ptr64 then fail "Asmgen.storeind1" else .OK (.Pmov_mr_a a r :: k)
  | .Tany64, .IR r => if Archi_ptr64 then .OK (.Pmov_mr_a a r :: k) else fail "Asmgen.storeind2"
  | .Tany64, .FR r => .OK (.Pmovsd_mf_a a r :: k)
  | _, _ => fail "Asmgen.storeind"

def transl_addressing (a : addressing) (args : List mreg) : res addrmode :=
  match a, args with
  | .Aindexed n, [a1] => bindRes (ireg_of a1) (fun r1 => pure (.Addrmode (some r1) none (Sum.inl n)))
  | .Aindexed2 n, [a1, a2] =>
      bindRes (ireg_of a1) (fun r1 =>
        bindRes (ireg_of a2) (fun r2 =>
          pure (.Addrmode (some r1) (some (r2, z1)) (Sum.inl n))))
  | .Ascaled sc n, [a1] =>
      bindRes (ireg_of a1) (fun r1 => pure (.Addrmode none (some (r1, sc)) (Sum.inl n)))
  | .Aindexed2scaled sc n, [a1, a2] =>
      bindRes (ireg_of a1) (fun r1 =>
        bindRes (ireg_of a2) (fun r2 =>
          pure (.Addrmode (some r1) (some (r2, sc)) (Sum.inl n))))
  | .Aglobal id ofs, [] => pure (.Addrmode none none (Sum.inr (id, ofs)))
  | .Abased id ofs, [a1] =>
      bindRes (ireg_of a1) (fun r1 => pure (.Addrmode (some r1) none (Sum.inr (id, ofs))))
  | .Abasedscaled sc id ofs, [a1] =>
      bindRes (ireg_of a1) (fun r1 => pure (.Addrmode none (some (r1, sc)) (Sum.inr (id, ofs))))
  | .Ainstack n, [] => pure (.Addrmode (some .RSP) none
      (Sum.inl (CompCert4Lean.Lib.Integers.Ptrofs.signed n)))
  | _, _ => fail "Asmgen.transl_addressing"

def normalize_addrmode_32 (a : addrmode) : addrmode :=
  match a with
  | .Addrmode base ofs (Sum.inl n) =>
      .Addrmode base ofs (Sum.inl
        (CompCert4Lean.Lib.Integers.Int.signed
          (CompCert4Lean.Lib.Integers.Int.repr n)))
  | .Addrmode _ _ (Sum.inr _) => a

def normalize_addrmode_64 (a : addrmode) : addrmode × Option int64 :=
  match a with
  | .Addrmode base ofs (Sum.inl n) =>
      if CompCert4Lean.X86.Op.offset_in_range n then (a, none)
      else (.Addrmode base ofs (Sum.inl z0), some
        (CompCert4Lean.Lib.Integers.Int64.repr n))
  | .Addrmode base ofs (Sum.inr (id, delta)) =>
      if CompCert4Lean.X86.Op.ptroffset_in_range delta || !Archi_ptr64 then (a, none)
      else (.Addrmode base ofs
        (Sum.inr (id, CompCert4Lean.Lib.Integers.Ptrofs.zero)), some
          (CompCert4Lean.Lib.Integers.Ptrofs.to_int64 delta))

def floatcomp (cmp : comparison) (r1 r2 : freg) : instruction :=
  match cmp with
  | .Clt | .Cle => .Pcomisd_ff r2 r1
  | .Ceq | .Cne | .Cgt | .Cge => .Pcomisd_ff r1 r2

def floatcomp32 (cmp : comparison) (r1 r2 : freg) : instruction :=
  match cmp with
  | .Clt | .Cle => .Pcomiss_ff r2 r1
  | .Ceq | .Cne | .Cgt | .Cge => .Pcomiss_ff r1 r2

def transl_cond (cond : condition) (args : List mreg) (k : code) : res code :=
  match cond, args with
  | .Ccomp _, [a1, a2] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pcmpl_rr r1 r2 :: k)))
  | .Ccompu _, [a1, a2] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pcmpl_rr r1 r2 :: k)))
  | .Ccompimm _ n, [a1] =>
      bindRes (ireg_of a1) (fun r1 =>
        pure ((if isIntZero n then .Ptestl_rr r1 r1 else .Pcmpl_ri r1 n) :: k))
  | .Ccompuimm _ n, [a1] => bindRes (ireg_of a1) (fun r1 => pure (.Pcmpl_ri r1 n :: k))
  | .Ccompl _, [a1, a2] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pcmpq_rr r1 r2 :: k)))
  | .Ccomplu _, [a1, a2] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pcmpq_rr r1 r2 :: k)))
  | .Ccomplimm _ n, [a1] =>
      bindRes (ireg_of a1) (fun r1 =>
        pure ((if isLongZero n then .Ptestq_rr r1 r1 else .Pcmpq_ri r1 n) :: k))
  | .Ccompluimm _ n, [a1] => bindRes (ireg_of a1) (fun r1 => pure (.Pcmpq_ri r1 n :: k))
  | .Ccompf cmp, [a1, a2] => bindRes (freg_of a1) (fun r1 =>
      bindRes (freg_of a2) (fun r2 => pure (floatcomp cmp r1 r2 :: k)))
  | .Cnotcompf cmp, [a1, a2] => bindRes (freg_of a1) (fun r1 =>
      bindRes (freg_of a2) (fun r2 => pure (floatcomp cmp r1 r2 :: k)))
  | .Ccompfs cmp, [a1, a2] => bindRes (freg_of a1) (fun r1 =>
      bindRes (freg_of a2) (fun r2 => pure (floatcomp32 cmp r1 r2 :: k)))
  | .Cnotcompfs cmp, [a1, a2] => bindRes (freg_of a1) (fun r1 =>
      bindRes (freg_of a2) (fun r2 => pure (floatcomp32 cmp r1 r2 :: k)))
  | .Cmaskzero n, [a1] => bindRes (ireg_of a1) (fun r1 => pure (.Ptestl_ri r1 n :: k))
  | .Cmasknotzero n, [a1] => bindRes (ireg_of a1) (fun r1 => pure (.Ptestl_ri r1 n :: k))
  | _, _ => fail "Asmgen.transl_cond"

def testcond_for_signed_comparison (cmp : comparison) : testcond :=
  match cmp with
  | .Ceq => .Cond_e | .Cne => .Cond_ne | .Clt => .Cond_l | .Cle => .Cond_le
  | .Cgt => .Cond_g | .Cge => .Cond_ge

def testcond_for_unsigned_comparison (cmp : comparison) : testcond :=
  match cmp with
  | .Ceq => .Cond_e | .Cne => .Cond_ne | .Clt => .Cond_b | .Cle => .Cond_be
  | .Cgt => .Cond_a | .Cge => .Cond_ae

inductive extcond : Type where
  | Cond_base (c : testcond)
  | Cond_or (c1 c2 : testcond)
  | Cond_and (c1 c2 : testcond)

export extcond (Cond_base Cond_or Cond_and)

def testcond_for_condition (cond : condition) : extcond :=
  match cond with
  | .Ccomp c | .Ccompimm c _ | .Ccompl c | .Ccomplimm c _ =>
      .Cond_base (testcond_for_signed_comparison c)
  | .Ccompu c | .Ccompuimm c _ | .Ccomplu c | .Ccompluimm c _ =>
      .Cond_base (testcond_for_unsigned_comparison c)
  | .Ccompf c | .Ccompfs c =>
      match c with
      | .Ceq => .Cond_and .Cond_np .Cond_e
      | .Cne => .Cond_or .Cond_p .Cond_ne
      | .Clt => .Cond_base .Cond_a
      | .Cle => .Cond_base .Cond_ae
      | .Cgt => .Cond_base .Cond_a
      | .Cge => .Cond_base .Cond_ae
  | .Cnotcompf c | .Cnotcompfs c =>
      match c with
      | .Ceq => .Cond_or .Cond_p .Cond_ne
      | .Cne => .Cond_and .Cond_np .Cond_e
      | .Clt => .Cond_base .Cond_be
      | .Cle => .Cond_base .Cond_b
      | .Cgt => .Cond_base .Cond_be
      | .Cge => .Cond_base .Cond_b
  | .Cmaskzero _ => .Cond_base .Cond_e
  | .Cmasknotzero _ => .Cond_base .Cond_ne

def mk_setcc_base (cond : extcond) (rd : ireg) (k : code) : code :=
  match cond with
  | .Cond_base c => .Psetcc c rd :: k
  | .Cond_and c1 c2 =>
      if ireg_eq rd .RAX then .Psetcc c1 .RAX :: .Psetcc c2 .RCX :: .Pandl_rr .RAX .RCX :: k
      else .Psetcc c1 .RAX :: .Psetcc c2 rd :: .Pandl_rr rd .RAX :: k
  | .Cond_or c1 c2 =>
      if ireg_eq rd .RAX then .Psetcc c1 .RAX :: .Psetcc c2 .RCX :: .Porl_rr .RAX .RCX :: k
      else .Psetcc c1 .RAX :: .Psetcc c2 rd :: .Porl_rr rd .RAX :: k

def mk_setcc (cond : extcond) (rd : ireg) (k : code) : code :=
  if Archi_ptr64 || low_ireg rd then mk_setcc_base cond rd k
  else mk_setcc_base cond .RAX (.Pmov_rr rd .RAX :: k)

def mk_jcc (cond : extcond) (lbl : positive) (k : code) : code :=
  match cond with
  | .Cond_base c => .Pjcc c lbl :: k
  | .Cond_and c1 c2 => .Pjcc2 c1 c2 lbl :: k
  | .Cond_or c1 c2 => .Pjcc c1 lbl :: .Pjcc c2 lbl :: k

def negate_testcond (c : testcond) : testcond :=
  match c with
  | .Cond_e => .Cond_ne | .Cond_ne => .Cond_e
  | .Cond_b => .Cond_ae | .Cond_be => .Cond_a
  | .Cond_ae => .Cond_b | .Cond_a => .Cond_be
  | .Cond_l => .Cond_ge | .Cond_le => .Cond_g
  | .Cond_ge => .Cond_l | .Cond_g => .Cond_le
  | .Cond_p => .Cond_np | .Cond_np => .Cond_p

def mk_sel (cond : extcond) (rd r2 : ireg) (k : code) : res code :=
  match cond with
  | .Cond_base c => pure (.Pcmov (negate_testcond c) rd r2 :: k)
  | .Cond_and c1 c2 => pure (.Pcmov (negate_testcond c1) rd r2 ::
      .Pcmov (negate_testcond c2) rd r2 :: k)
  | .Cond_or _ _ => fail "Asmgen.mk_sel"

def transl_sel (cond : condition) (args : List mreg) (rd r2 : ireg) (k : code) : res code :=
  if ireg_eq rd r2 then pure (.Pmov_rr rd r2 :: k)
  else bindRes (mk_sel (testcond_for_condition cond) rd r2 k)
    (fun k1 => transl_cond cond args k1)

/-! Arithmetic operation translation.  The source checks register-shape
    assertions before emitting instructions; the typed Lean carriers already
    expose the same register classes, so malformed combinations take the
    source error branch. -/

def transl_op (op : operation) (args : List mreg) (dst : mreg) (k : code) : res code :=
  match op, args with
  | .Omove, [a1] => mk_mov (CompCert4Lean.X86.Asm.preg_of dst)
      (CompCert4Lean.X86.Asm.preg_of a1) k
  | .Ointconst n, [] => bindRes (ireg_of dst) (fun r =>
      pure ((if isIntZero n then .Pxorl_r r else .Pmovl_ri r n) :: k))
  | .Olongconst n, [] => bindRes (ireg_of dst) (fun r =>
      pure ((if CompCert4Lean.Lib.Integers.Int64.eq n
          CompCert4Lean.Lib.Integers.Int64.zero then .Pxorq_r r else .Pmovq_ri r n) :: k))
  | .Ofloatconst f, [] => bindRes (freg_of dst) (fun r =>
      pure ((if sumboolBool (CompCert4Lean.Lib.Floats.Float.eq_dec f
          CompCert4Lean.Lib.Floats.Float.zero) then .Pxorpd_f r else .Pmovsd_fi r f) :: k))
  | .Osingleconst f, [] => bindRes (freg_of dst) (fun r =>
      pure ((if sumboolBool (CompCert4Lean.Lib.Floats.Float32.eq_dec f
          CompCert4Lean.Lib.Floats.Float32.zero) then .Pxorps_f r else .Pmovss_fi r f) :: k))
  | .Oindirectsymbol id, [] => bindRes (ireg_of dst)
      (fun r => pure (.Pmov_rs r id :: k))
  | .Ocast8signed, [a1] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of dst) (fun r => mk_intconv .Pmovsb_rr r r1 k))
  | .Ocast8unsigned, [a1] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of dst) (fun r => mk_intconv .Pmovzb_rr r r1 k))
  | .Ocast16signed, [a1] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of dst) (fun r => pure (.Pmovsw_rr r r1 :: k)))
  | .Ocast16unsigned, [a1] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of dst) (fun r => pure (.Pmovzw_rr r r1 :: k)))
  | .Oneg, [_] => bindRes (ireg_of dst) (fun r => pure (.Pnegl r :: k))
  | .Osub, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Psubl_rr r r2 :: k)))
  | .Omul, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pimull_rr r r2 :: k)))
  | .Omulimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pimull_ri r n :: k))
  | .Omulhs, [_, a2] => bindRes (ireg_of a2) (fun r2 => pure (.Pimull_r r2 :: k))
  | .Omulhu, [_, a2] => bindRes (ireg_of a2) (fun r2 => pure (.Pmull_r r2 :: k))
  | .Odiv, [_, _] => pure (.Pcltd :: .Pidivl .RCX :: k)
  | .Odivu, [_, _] => pure (.Pxorl_r .RDX :: .Pdivl .RCX :: k)
  | .Omod, [_, _] => pure (.Pcltd :: .Pidivl .RCX :: k)
  | .Omodu, [_, _] => pure (.Pxorl_r .RDX :: .Pdivl .RCX :: k)
  | .Oand, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pandl_rr r r2 :: k)))
  | .Oandimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pandl_ri r n :: k))
  | .Oor, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Porl_rr r r2 :: k)))
  | .Oorimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Porl_ri r n :: k))
  | .Oxor, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pxorl_rr r r2 :: k)))
  | .Oxorimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pxorl_ri r n :: k))
  | .Onot, [_] => bindRes (ireg_of dst) (fun r => pure (.Pnotl r :: k))
  | .Oshl, [_, _] => bindRes (ireg_of dst) (fun r => pure (.Psall_rcl r :: k))
  | .Oshr, [_, _] => bindRes (ireg_of dst) (fun r => pure (.Psarl_rcl r :: k))
  | .Oshru, [_, _] => bindRes (ireg_of dst) (fun r => pure (.Pshrl_rcl r :: k))
  | .Oshlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Psall_ri r n :: k))
  | .Oshrimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Psarl_ri r n :: k))
  | .Oshruimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pshrl_ri r n :: k))
  | .Oshrximm n, [_] => mk_shrximm n k
  | .Ororimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Prorl_ri r n :: k))
  | .Oshldimm n, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pshld_ri r r2 n :: k)))
  | .Olea addr, _ => bindRes (transl_addressing addr args) (fun am =>
      bindRes (ireg_of dst) (fun r => pure (.Pleal r (normalize_addrmode_32 am) :: k)))
  | .Olowlong, [_] => bindRes (ireg_of dst) (fun r => pure (.Pmovls_rr r :: k))
  | .Ocast32signed, [a1] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of dst) (fun r => pure (.Pmovsl_rr r r1 :: k)))
  | .Ocast32unsigned, [a1] => bindRes (ireg_of a1) (fun r1 =>
      bindRes (ireg_of dst) (fun r => pure (.Pmovzl_rr r r1 :: k)))
  | .Onegl, [_] => bindRes (ireg_of dst) (fun r => pure (.Pnegq r :: k))
  | .Oaddlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Paddq_ri r n :: k))
  | .Osubl, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Psubq_rr r r2 :: k)))
  | .Omull, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pimulq_rr r r2 :: k)))
  | .Omullimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pimulq_ri r n :: k))
  | .Omullhs, [_, a2] => bindRes (ireg_of a2) (fun r2 => pure (.Pimulq_r r2 :: k))
  | .Omullhu, [_, a2] => bindRes (ireg_of a2) (fun r2 => pure (.Pmulq_r r2 :: k))
  | .Odivl, [_, _] => pure (.Pcqto :: .Pidivq .RCX :: k)
  | .Odivlu, [_, _] => pure (.Pxorq_r .RDX :: .Pdivq .RCX :: k)
  | .Omodl, [_, _] => pure (.Pcqto :: .Pidivq .RCX :: k)
  | .Omodlu, [_, _] => pure (.Pxorq_r .RDX :: .Pdivq .RCX :: k)
  | .Oandl, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pandq_rr r r2 :: k)))
  | .Oandlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pandq_ri r n :: k))
  | .Oorl, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Porq_rr r r2 :: k)))
  | .Oorlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Porq_ri r n :: k))
  | .Oxorl, [_, a2] => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => pure (.Pxorq_rr r r2 :: k)))
  | .Oxorlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pxorq_ri r n :: k))
  | .Onotl, [_] => bindRes (ireg_of dst) (fun r => pure (.Pnotq r :: k))
  | .Oshll, [_, _] => bindRes (ireg_of dst) (fun r => pure (.Psalq_rcl r :: k))
  | .Oshrl, [_, _] => bindRes (ireg_of dst) (fun r => pure (.Psarq_rcl r :: k))
  | .Oshrlu, [_, _] => bindRes (ireg_of dst) (fun r => pure (.Pshrq_rcl r :: k))
  | .Oshllimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Psalq_ri r n :: k))
  | .Oshrlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Psarq_ri r n :: k))
  | .Oshrxlimm n, [_] => mk_shrxlimm n k
  | .Oshrluimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Pshrq_ri r n :: k))
  | .Ororlimm n, [_] => bindRes (ireg_of dst) (fun r => pure (.Prorq_ri r n :: k))
  | .Oleal addr, _ => bindRes (transl_addressing addr args) (fun am =>
      bindRes (ireg_of dst) (fun r =>
        let am' := normalize_addrmode_64 am
        pure (match am' with
          | (a, none) => .Pleaq r a :: k
          | (a, some delta) => .Pleaq r a :: .Paddq_ri r delta :: k)))
  | .Onegf, [_] => bindRes (freg_of dst) (fun r => pure (.Pnegd r :: k))
  | .Oabsf, [_] => bindRes (freg_of dst) (fun r => pure (.Pabsd r :: k))
  | .Oaddf, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Paddd_ff r r2 :: k)))
  | .Osubf, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Psubd_ff r r2 :: k)))
  | .Omulf, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Pmuld_ff r r2 :: k)))
  | .Odivf, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Pdivd_ff r r2 :: k)))
  | .Omaxf, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Pmaxsd r r2 :: k)))
  | .Ominf, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Pminsd r r2 :: k)))
  | .Onegfs, [_] => bindRes (freg_of dst) (fun r => pure (.Pnegs r :: k))
  | .Oabsfs, [_] => bindRes (freg_of dst) (fun r => pure (.Pabss r :: k))
  | .Oaddfs, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Padds_ff r r2 :: k)))
  | .Osubfs, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Psubs_ff r r2 :: k)))
  | .Omulfs, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Pmuls_ff r r2 :: k)))
  | .Odivfs, [_, a2] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a2) (fun r2 => pure (.Pdivs_ff r r2 :: k)))
  | .Osingleoffloat, [a1] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a1) (fun r1 => pure (.Pcvtsd2ss_ff r r1 :: k)))
  | .Ofloatofsingle, [a1] => bindRes (freg_of dst) (fun r =>
      bindRes (freg_of a1) (fun r1 => pure (.Pcvtss2sd_ff r r1 :: k)))
  | .Ointoffloat, [a1] => bindRes (ireg_of dst) (fun r =>
      bindRes (freg_of a1) (fun r1 => pure (.Pcvttsd2si_rf r r1 :: k)))
  | .Ofloatofint, [a1] => bindRes (freg_of dst) (fun r =>
      bindRes (ireg_of a1) (fun r1 => pure (.Pcvtsi2sd_fr r r1 :: k)))
  | .Ointofsingle, [a1] => bindRes (ireg_of dst) (fun r =>
      bindRes (freg_of a1) (fun r1 => pure (.Pcvttss2si_rf r r1 :: k)))
  | .Osingleofint, [a1] => bindRes (freg_of dst) (fun r =>
      bindRes (ireg_of a1) (fun r1 => pure (.Pcvtsi2ss_fr r r1 :: k)))
  | .Olongoffloat, [a1] => bindRes (ireg_of dst) (fun r =>
      bindRes (freg_of a1) (fun r1 => pure (.Pcvttsd2sl_rf r r1 :: k)))
  | .Ofloatoflong, [a1] => bindRes (freg_of dst) (fun r =>
      bindRes (ireg_of a1) (fun r1 => pure (.Pcvtsl2sd_fr r r1 :: k)))
  | .Olongofsingle, [a1] => bindRes (ireg_of dst) (fun r =>
      bindRes (freg_of a1) (fun r1 => pure (.Pcvttss2sl_rf r r1 :: k)))
  | .Osingleoflong, [a1] => bindRes (freg_of dst) (fun r =>
      bindRes (ireg_of a1) (fun r1 => pure (.Pcvtsl2ss_fr r r1 :: k)))
  | .Ocmp c, _ => bindRes (ireg_of dst) (fun r =>
      transl_cond c args (mk_setcc (testcond_for_condition c) r k))
  | .Osel c _, a1 :: a2 :: rest => bindRes (ireg_of dst) (fun r =>
      bindRes (ireg_of a2) (fun r2 => transl_sel c rest r r2 k))
  | _, _ => fail "Asmgen.transl_op"

def transl_load (chunk : memory_chunk) (addr : addressing) (args : List mreg)
    (dst : mreg) (k : code) : res code :=
  bindRes (transl_addressing addr args) (fun am =>
    match chunk with
    | .Mint8unsigned => bindRes (ireg_of dst) (fun r => pure (.Pmovzb_rm r am :: k))
    | .Mint8signed => bindRes (ireg_of dst) (fun r => pure (.Pmovsb_rm r am :: k))
    | .Mint16unsigned => bindRes (ireg_of dst) (fun r => pure (.Pmovzw_rm r am :: k))
    | .Mint16signed => bindRes (ireg_of dst) (fun r => pure (.Pmovsw_rm r am :: k))
    | .Mint32 => bindRes (ireg_of dst) (fun r => pure (.Pmovl_rm r am :: k))
    | .Mint64 => bindRes (ireg_of dst) (fun r => pure (.Pmovq_rm r am :: k))
    | .Mfloat32 => bindRes (freg_of dst) (fun r => pure (.Pmovss_fm r am :: k))
    | .Mfloat64 => bindRes (freg_of dst) (fun r => pure (.Pmovsd_fm r am :: k))
    | _ => fail "Asmgen.transl_load")

def transl_store (chunk : memory_chunk) (addr : addressing) (args : List mreg)
    (src : mreg) (k : code) : res code :=
  bindRes (transl_addressing addr args) (fun am =>
    match chunk with
    | .Mint8unsigned => bindRes (ireg_of src) (fun r => mk_storebyte am r k)
    | .Mint16unsigned => bindRes (ireg_of src) (fun r => pure (.Pmovw_mr am r :: k))
    | .Mint32 => bindRes (ireg_of src) (fun r => pure (.Pmovl_mr am r :: k))
    | .Mint64 => bindRes (ireg_of src) (fun r => pure (.Pmovq_mr am r :: k))
    | .Mfloat32 => bindRes (freg_of src) (fun r => pure (.Pmovss_mf am r :: k))
    | .Mfloat64 => bindRes (freg_of src) (fun r => pure (.Pmovsd_mf am r :: k))
    | _ => fail "Asmgen.transl_store")

private abbrev MachFunction := CompCert4Lean.Backend.Mach.function
private abbrev MachInstruction := CompCert4Lean.Backend.Mach.instruction
private abbrev MachCode := CompCert4Lean.Backend.Mach.code
private abbrev MachFundef := CompCert4Lean.Backend.Mach.fundef
private abbrev MachProgram := CompCert4Lean.Backend.Mach.program

def transl_instr (f : MachFunction) (i : MachInstruction)
    (ax_is_parent : Bool) (k : code) : res code :=
  match i with
  | .Mgetstack ofs ty dst => loadind .RSP ofs ty dst k
  | .Msetstack src ofs ty => storeind src .RSP ofs ty k
  | .Mgetparam ofs ty dst =>
      if ax_is_parent then loadind .RAX ofs ty dst k
      else bindRes (loadind .RAX ofs ty dst k) (fun k1 =>
        loadind .RSP f.fn_link_ofs Tptr .AX k1)
  | .Mop op args dst => transl_op op args dst k
  | .Mload chunk addr args dst => transl_load chunk addr args dst k
  | .Mstore chunk addr args src => transl_store chunk addr args src k
  | .Mcall sg (.inl r) => bindRes (ireg_of r) (fun r' => pure (.Pcall_r r' sg :: k))
  | .Mcall sg (.inr symb) => pure (.Pcall_s symb sg :: k)
  | .Mtailcall sg (.inl r) => bindRes (ireg_of r) (fun r' =>
      pure (.Pfreeframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs ::
        .Pjmp_r r' sg :: k))
  | .Mtailcall sg (.inr symb) => pure (.Pfreeframe f.fn_stacksize
      f.fn_retaddr_ofs f.fn_link_ofs :: .Pjmp_s symb sg :: k)
  | .Mlabel lbl => pure (.Plabel lbl :: k)
  | .Mgoto lbl => pure (.Pjmp_l lbl :: k)
  | .Mcond cond args lbl =>
      transl_cond cond args (mk_jcc (testcond_for_condition cond) lbl k)
  | .Mjumptable arg tbl => bindRes (ireg_of arg) (fun r => pure (.Pjmptbl r tbl :: k))
  | .Mreturn => pure (.Pfreeframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs ::
      .Pret :: k)
  | .Mbuiltin ef args result => pure (.Pbuiltin ef
      (args.map (CompCert4Lean.Common.AST.map_builtin_arg
        CompCert4Lean.X86.Asm.preg_of))
      (CompCert4Lean.Common.AST.map_builtin_res CompCert4Lean.X86.Asm.preg_of result) :: k)

def it1_is_parent (before : Bool) (i : MachInstruction) : Bool :=
  match i with
  | .Msetstack _ _ _ => before
  | .Mgetparam _ _ dst => !mreg_eq dst .AX
  | _ => false

def transl_code (f : MachFunction) (il : MachCode) (axp : Bool) : res code :=
  match il with
  | [] => pure []
  | i1 :: il' =>
      bindRes (transl_code f il' (it1_is_parent axp i1)) (fun k =>
        transl_instr f i1 axp k)

def transl_code_rec (f : MachFunction) (il : MachCode) (axp : Bool)
    (k : code → res code) : res code :=
  match il with
  | [] => k []
  | i1 :: il' =>
      transl_code_rec f il' (it1_is_parent axp i1) (fun c1 =>
        bindRes (transl_instr f i1 axp c1) k)

def transl_code' (f : MachFunction) (il : MachCode) (axp : Bool) : res code :=
  transl_code_rec f il axp (fun c => pure c)

def transl_function (f : MachFunction) : res CompCert4Lean.X86.Asm.function :=
  bindRes (transl_code' f f.fn_code true) (fun c =>
    pure { fn_sig := f.fn_sig
           fn_code := .Pallocframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs :: c })

def transf_function (f : MachFunction) : res CompCert4Lean.X86.Asm.function :=
  bindRes (transl_function f) (fun tf =>
    match CompCert4Lean.Lib.Coqlib.zlt
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
      (CompCert4Lean.Lib.Coqlib.list_length_z tf.fn_code) with
    | .left _ => fail "code size exceeded"
    | .right _ => pure tf)

def transf_fundef (f : MachFundef) : res (CompCert4Lean.Common.AST.fundef
    CompCert4Lean.X86.Asm.function) :=
  CompCert4Lean.Common.AST.transf_partial_fundef transf_function f

def transf_program (p : MachProgram) : res CompCert4Lean.X86.Asm.program :=
  CompCert4Lean.Common.AST.transform_partial_program transf_fundef p

end CompCert4Lean.X86.Asmgen
