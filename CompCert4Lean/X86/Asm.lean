import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Config
import CompCert4Lean.Backend.Locations
import CompCert4Lean.X86.Machregs
import CompCert4Lean.X86.Conventions1
import CompCert4Lean.X86.Stacklayout

/-!
# x86 assembly syntax and operational surface

This is the definition-bearing translation of CompCert's `x86/Asm.v`.
The five proof declarations assigned to the later proof phase are retained
as exact proposition descriptors.
-/

namespace CompCert4Lean.X86.Asm

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Conventions1

private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev signature := CompCert4Lean.Common.AST.signature
private abbrev external_function := CompCert4Lean.Common.AST.external_function
private abbrev trace := CompCert4Lean.Common.Events.trace
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev ExternalCalls := CompCert4Lean.Common.ExternalCalls.ExternalCalls
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zeq := CompCert4Lean.Lib.Coqlib.zeq

private def decEqSumbool {A : Type} [DecidableEq A] (x y : A) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

private def boolOfSumbool {P Q : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

/-! ## Registers and flags -/

inductive ireg : Type where
  | RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
deriving DecidableEq

export ireg (RAX RBX RCX RDX RSI RDI RBP RSP R8 R9 R10 R11 R12 R13 R14 R15)

inductive freg : Type where
  | XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15
deriving DecidableEq

export freg (XMM0 XMM1 XMM2 XMM3 XMM4 XMM5 XMM6 XMM7 XMM8 XMM9 XMM10
  XMM11 XMM12 XMM13 XMM14 XMM15)

inductive crbit : Type where
  | ZF | CF | PF | SF | OF
deriving DecidableEq

export crbit (ZF CF PF SF OF)

inductive preg : Type where
  | PC
  | IR (r : ireg)
  | FR (r : freg)
  | ST0
  | CR (r : crbit)
  | RA
deriving DecidableEq

export preg (PC IR FR ST0 CR RA)

def SP : ireg := .RSP

def ireg_eqStatement :=
  ∀ (x y : ireg),
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)

def ireg_eq := ireg_eqStatement

def freg_eqStatement :=
  ∀ (x y : freg),
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)

def freg_eq := freg_eqStatement

def preg_eqStatement :=
  ∀ (x y : preg),
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)

def preg_eq := preg_eqStatement

namespace PregEq

def t : Type := preg

def eq (x y : t) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  decEqSumbool (A := preg) x y

end PregEq

namespace Pregmap

def Pregmap : Type := Unit

def elt : Type := preg

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  PregEq.eq x y

def t (A : Type) := preg → A

def init {A : Type} (x : A) : t A := fun _ => x

def get {A : Type} (r : preg) (rs : t A) : A := rs r

def set {A : Type} (r : preg) (v : A) (rs : t A) : t A :=
  fun r' => if r' = r then v else rs r'

def gi : Prop :=
  ∀ (A : Type) (i : elt) (x : A), init x i = x

def gss : Prop :=
  ∀ (A : Type) (i : elt) (x : A) (m : t A), set i x m i = x

def gso : Prop :=
  ∀ (A : Type) (i j : elt) (x : A) (m : t A),
    i ≠ j → set j x m i = m i

def gsspec : Prop :=
  ∀ (A : Type) (i j : elt) (x : A) (m : t A),
    get i (set j x m) =
      match elt_eq i j with
      | .left _ => x
      | .right _ => get i m

def gsident : Prop :=
  ∀ (A : Type) (i j : elt) (m : t A), get j (set i (get i m) m) = get j m

def map {A B : Type} (f : A → B) (m : t A) : t B := fun x => f (m x)

def gmap : Prop :=
  ∀ (A B : Type) (f : A → B) (i : elt) (m : t A),
    get i (map f m) = f (get i m)

end Pregmap

/-! ## Addressing and instructions -/

def label := positive

inductive addrmode : Type where
  | Addrmode (base : Option ireg)
      (ofs : Option (ireg × Z))
      (const : Sum Z (ident × ptrofs))
deriving DecidableEq

export addrmode (Addrmode)

inductive testcond : Type where
  | Cond_e | Cond_ne | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g | Cond_p | Cond_np
deriving DecidableEq

export testcond (Cond_e Cond_ne Cond_b Cond_be Cond_ae Cond_a Cond_l Cond_le
  Cond_ge Cond_g Cond_p Cond_np)

inductive instruction : Type where
  | Pmov_rr (rd r1 : ireg)
  | Pmovl_ri (rd : ireg) (n : int)
  | Pmovq_ri (rd : ireg) (n : int64)
  | Pmov_rs (rd : ireg) (id : ident)
  | Pmovl_rm (rd : ireg) (a : addrmode)
  | Pmovq_rm (rd : ireg) (a : addrmode)
  | Pmovl_mr (a : addrmode) (rs : ireg)
  | Pmovq_mr (a : addrmode) (rs : ireg)
  | Pmovsd_ff (rd r1 : freg)
  | Pmovsd_fi (rd : freg) (n : CompCert4Lean.Lib.Floats.float)
  | Pmovsd_fm (rd : freg) (a : addrmode)
  | Pmovsd_mf (a : addrmode) (r1 : freg)
  | Pmovss_fi (rd : freg) (n : CompCert4Lean.Lib.Floats.float32)
  | Pmovss_fm (rd : freg) (a : addrmode)
  | Pmovss_mf (a : addrmode) (r1 : freg)
  | Pfldl_m (a : addrmode) | Pfstpl_m (a : addrmode)
  | Pflds_m (a : addrmode) | Pfstps_m (a : addrmode)
  | Pmovb_mr (a : addrmode) (rs : ireg)
  | Pmovw_mr (a : addrmode) (rs : ireg)
  | Pmovzb_rr (rd rs : ireg) | Pmovzb_rm (rd : ireg) (a : addrmode)
  | Pmovsb_rr (rd rs : ireg) | Pmovsb_rm (rd : ireg) (a : addrmode)
  | Pmovzw_rr (rd rs : ireg) | Pmovzw_rm (rd : ireg) (a : addrmode)
  | Pmovsw_rr (rd rs : ireg) | Pmovsw_rm (rd : ireg) (a : addrmode)
  | Pmovzl_rr (rd rs : ireg) | Pmovsl_rr (rd rs : ireg)
  | Pmovls_rr (rd : ireg)
  | Pcvtsd2ss_ff (rd r1 : freg) | Pcvtss2sd_ff (rd r1 : freg)
  | Pcvttsd2si_rf (rd : ireg) (r1 : freg)
  | Pcvtsi2sd_fr (rd : freg) (r1 : ireg)
  | Pcvttss2si_rf (rd : ireg) (r1 : freg)
  | Pcvtsi2ss_fr (rd : freg) (r1 : ireg)
  | Pcvttsd2sl_rf (rd : ireg) (r1 : freg)
  | Pcvtsl2sd_fr (rd : freg) (r1 : ireg)
  | Pcvttss2sl_rf (rd : ireg) (r1 : freg)
  | Pcvtsl2ss_fr (rd : freg) (r1 : ireg)
  | Pleal (rd : ireg) (a : addrmode) | Pleaq (rd : ireg) (a : addrmode)
  | Pnegl (rd : ireg) | Pnegq (rd : ireg)
  | Paddl_ri (rd : ireg) (n : int) | Paddq_ri (rd : ireg) (n : int64)
  | Psubl_rr (rd r1 : ireg) | Psubq_rr (rd r1 : ireg)
  | Pimull_rr (rd r1 : ireg) | Pimulq_rr (rd r1 : ireg)
  | Pimull_ri (rd : ireg) (n : int) | Pimulq_ri (rd : ireg) (n : int64)
  | Pimull_r (r1 : ireg) | Pimulq_r (r1 : ireg)
  | Pmull_r (r1 : ireg) | Pmulq_r (r1 : ireg)
  | Pcltd | Pcqto | Pdivl (r1 : ireg) | Pdivq (r1 : ireg)
  | Pidivl (r1 : ireg) | Pidivq (r1 : ireg)
  | Pandl_rr (rd r1 : ireg) | Pandq_rr (rd r1 : ireg)
  | Pandl_ri (rd : ireg) (n : int) | Pandq_ri (rd : ireg) (n : int64)
  | Porl_rr (rd r1 : ireg) | Porq_rr (rd r1 : ireg)
  | Porl_ri (rd : ireg) (n : int) | Porq_ri (rd : ireg) (n : int64)
  | Pxorl_r (rd : ireg) | Pxorq_r (rd : ireg)
  | Pxorl_rr (rd r1 : ireg) | Pxorq_rr (rd r1 : ireg)
  | Pxorl_ri (rd : ireg) (n : int) | Pxorq_ri (rd : ireg) (n : int64)
  | Pnotl (rd : ireg) | Pnotq (rd : ireg)
  | Psall_rcl (rd : ireg) | Psalq_rcl (rd : ireg)
  | Psall_ri (rd : ireg) (n : int) | Psalq_ri (rd : ireg) (n : int)
  | Pshrl_rcl (rd : ireg) | Pshrq_rcl (rd : ireg)
  | Pshrl_ri (rd : ireg) (n : int) | Pshrq_ri (rd : ireg) (n : int)
  | Psarl_rcl (rd : ireg) | Psarq_rcl (rd : ireg)
  | Psarl_ri (rd : ireg) (n : int) | Psarq_ri (rd : ireg) (n : int)
  | Pshld_ri (rd r1 : ireg) (n : int)
  | Prorl_ri (rd : ireg) (n : int) | Prorq_ri (rd : ireg) (n : int)
  | Pcmpl_rr (r1 r2 : ireg) | Pcmpq_rr (r1 r2 : ireg)
  | Pcmpl_ri (r1 : ireg) (n : int) | Pcmpq_ri (r1 : ireg) (n : int64)
  | Ptestl_rr (r1 r2 : ireg) | Ptestq_rr (r1 r2 : ireg)
  | Ptestl_ri (r1 : ireg) (n : int) | Ptestq_ri (r1 : ireg) (n : int64)
  | Pcmov (c : testcond) (rd r1 : ireg) | Psetcc (c : testcond) (rd : ireg)
  | Paddd_ff (rd r1 : freg) | Psubd_ff (rd r1 : freg)
  | Pmuld_ff (rd r1 : freg) | Pdivd_ff (rd r1 : freg)
  | Pnegd (rd : freg) | Pabsd (rd : freg) | Pcomisd_ff (r1 r2 : freg)
  | Pxorpd_f (rd : freg)
  | Padds_ff (rd r1 : freg) | Psubs_ff (rd r1 : freg)
  | Pmuls_ff (rd r1 : freg) | Pdivs_ff (rd r1 : freg)
  | Pnegs (rd : freg) | Pabss (rd : freg) | Pcomiss_ff (r1 r2 : freg)
  | Pxorps_f (rd : freg)
  | Pjmp_l (l : label) | Pjmp_s (symb : ident) (sg : signature)
  | Pjmp_r (r : ireg) (sg : signature) | Pjcc (c : testcond) (l : label)
  | Pjcc2 (c1 c2 : testcond) (l : label)
  | Pjmptbl (r : ireg) (tbl : List label)
  | Pcall_s (symb : ident) (sg : signature) | Pcall_r (r : ireg) (sg : signature)
  | Pret
  | Pmov_rm_a (rd : ireg) (a : addrmode) | Pmov_mr_a (a : addrmode) (rs : ireg)
  | Pmovsd_fm_a (rd : freg) (a : addrmode) | Pmovsd_mf_a (a : addrmode) (r1 : freg)
  | Plabel (l : label)
  | Pallocframe (sz : Z) (ofs_ra ofs_link : ptrofs)
  | Pfreeframe (sz : Z) (ofs_ra ofs_link : ptrofs)
  | Pbuiltin (ef : external_function) (args : List (builtin_arg preg))
      (res : builtin_res preg)
  | Padcl_ri (rd : ireg) (n : int) | Padcl_rr (rd r2 : ireg)
  | Paddl_mi (a : addrmode) (n : int) | Paddl_rr (rd r2 : ireg)
  | Pbsfl (rd r1 : ireg) | Pbsfq (rd r1 : ireg)
  | Pbsrl (rd r1 : ireg) | Pbsrq (rd r1 : ireg)
  | Pbswap64 (rd : ireg) | Pbswap32 (rd : ireg) | Pbswap16 (rd : ireg)
  | Pcfi_adjust (n : int)
  | Pfmadd132 (rd r2 r3 : freg) | Pfmadd213 (rd r2 r3 : freg)
  | Pfmadd231 (rd r2 r3 : freg) | Pfmsub132 (rd r2 r3 : freg)
  | Pfmsub213 (rd r2 r3 : freg) | Pfmsub231 (rd r2 r3 : freg)
  | Pfnmadd132 (rd r2 r3 : freg) | Pfnmadd213 (rd r2 r3 : freg)
  | Pfnmadd231 (rd r2 r3 : freg) | Pfnmsub132 (rd r2 r3 : freg)
  | Pfnmsub213 (rd r2 r3 : freg) | Pfnmsub231 (rd r2 r3 : freg)
  | Pmaxsd (rd r2 : freg) | Pminsd (rd r2 : freg)
  | Pmovb_rm (rd : ireg) (a : addrmode) | Pmovq_rf (rd : ireg) (r1 : freg)
  | Pmovsq_mr (a : addrmode) (rs : freg) | Pmovsq_rm (rd : freg) (a : addrmode)
  | Pmovsb | Pmovsw | Pmovw_rm (rd : ireg) (a : addrmode) | Pnop | Prep_movsl
  | Psbbl_rr (rd r2 : ireg) | Psqrtsd (rd r1 : freg)
  | Psubl_ri (rd : ireg) (n : int) | Psubq_ri (rd : ireg) (n : int64)
export instruction (Pmov_rr Pmovl_ri Pmovq_ri Pmov_rs Pmovl_rm Pmovq_rm Pmovl_mr
  Pmovq_mr Pmovsd_ff Pmovsd_fi Pmovsd_fm Pmovsd_mf Pmovss_fi Pmovss_fm Pmovss_mf
  Pfldl_m Pfstpl_m Pflds_m Pfstps_m Pmovb_mr Pmovw_mr Pmovzb_rr Pmovzb_rm
  Pmovsb_rr Pmovsb_rm Pmovzw_rr Pmovzw_rm Pmovsw_rr Pmovsw_rm Pmovzl_rr Pmovsl_rr
  Pmovls_rr Pcvtsd2ss_ff Pcvtss2sd_ff Pcvttsd2si_rf Pcvtsi2sd_fr Pcvttss2si_rf
  Pcvtsi2ss_fr Pcvttsd2sl_rf Pcvtsl2sd_fr Pcvttss2sl_rf Pcvtsl2ss_fr Pleal Pleaq
  Pnegl Pnegq Paddl_ri Paddq_ri Psubl_rr Psubq_rr Pimull_rr Pimulq_rr Pimull_ri
  Pimulq_ri Pimull_r Pimulq_r Pmull_r Pmulq_r Pcltd Pcqto Pdivl Pdivq Pidivl
  Pidivq Pandl_rr Pandq_rr Pandl_ri Pandq_ri Porl_rr Porq_rr Porl_ri Porq_ri
  Pxorl_r Pxorq_r Pxorl_rr Pxorq_rr Pxorl_ri Pxorq_ri Pnotl Pnotq Psall_rcl
  Psalq_rcl Psall_ri Psalq_ri Pshrl_rcl Pshrq_rcl Pshrl_ri Pshrq_ri Psarl_rcl
  Psarq_rcl Psarl_ri Psarq_ri Pshld_ri Prorl_ri Prorq_ri Pcmpl_rr Pcmpq_rr
  Pcmpl_ri Pcmpq_ri Ptestl_rr Ptestq_rr Ptestl_ri Ptestq_ri Pcmov Psetcc Paddd_ff
  Psubd_ff Pmuld_ff Pdivd_ff Pnegd Pabsd Pcomisd_ff Pxorpd_f Padds_ff Psubs_ff
  Pmuls_ff Pdivs_ff Pnegs Pabss Pcomiss_ff Pxorps_f Pjmp_l Pjmp_s Pjmp_r Pjcc
  Pjcc2 Pjmptbl Pcall_s Pcall_r Pret Pmov_rm_a Pmov_mr_a Pmovsd_fm_a Pmovsd_mf_a
  Plabel Pallocframe Pfreeframe Pbuiltin Padcl_ri Padcl_rr Paddl_mi Paddl_rr
  Pbsfl Pbsfq Pbsrl Pbsrq Pbswap64 Pbswap32 Pbswap16 Pcfi_adjust Pfmadd132
  Pfmadd213 Pfmadd231 Pfmsub132 Pfmsub213 Pfmsub231 Pfnmadd132 Pfnmadd213
  Pfnmadd231 Pfnmsub132 Pfnmsub213 Pfnmsub231 Pmaxsd Pminsd Pmovb_rm Pmovq_rf
  Pmovsq_mr Pmovsq_rm Pmovsb Pmovsw Pmovw_rm Pnop Prep_movsl Psbbl_rr Psqrtsd
  Psubl_ri Psubq_ri)

def code := List instruction

structure function : Type where
  fn_sig : signature
  fn_code : code

export function (fn_sig fn_code)

def fundef := CompCert4Lean.Common.AST.fundef function
def program := CompCert4Lean.Common.AST.program fundef Unit

/-! ## Register sets and basic operations -/

def regset := Pregmap.t val
def genv := CompCert4Lean.Common.Globalenvs.Genv.t fundef Unit

def undef_regs : List preg → regset → regset
  | [], rs => rs
  | r :: rest, rs => undef_regs rest (Pregmap.set r Vundef rs)

def set_pair (p : rpair preg) (v : val) (rs : regset) : regset :=
  match p with
  | .One r => Pregmap.set r v rs
  | .Twolong rhi rlo => Pregmap.set rlo (Val.loword v) (Pregmap.set rhi (Val.hiword v) rs)

def set_res : builtin_res preg → val → regset → regset
  | .BR r, v, rs => Pregmap.set r v rs
  | .BR_none, _, rs => rs
  | .BR_splitlong hi lo, v, rs =>
      set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)

/-! ## Addressing and conditions -/

def find_instr : Z → code → Option instruction
  | _, [] => none
  | pos, i :: rest =>
      match zeq pos z0 with
      | .left _ => some i
      | .right _ => find_instr (zSub pos z1) rest

def is_label (lbl : label) : instruction → Bool
  | .Plabel lbl' => boolOfSumbool (CompCert4Lean.Lib.Coqlib.peq lbl lbl')
  | _ => false

def label_pos (lbl : label) : Z → code → Option Z
  | _, [] => none
  | pos, i :: rest =>
      if is_label lbl i then some (zAdd pos z1) else label_pos lbl (zAdd pos z1) rest

def eval_addrmode32 (_ge : genv) (a : addrmode) (rs : regset) : val :=
  match a with
  | .Addrmode base ofs const =>
      let vb := match base with | none => Vint CompCert4Lean.Lib.Integers.Int.zero | some r => Pregmap.get (.IR r) rs
      let vo := match ofs with
        | none => Vint CompCert4Lean.Lib.Integers.Int.zero
        | some (r, sc) =>
            match zeq sc z1 with
            | .left _ => Pregmap.get (.IR r) rs
            | .right _ => Val.mul (Pregmap.get (.IR r) rs) (Vint (CompCert4Lean.Lib.Integers.Int.repr sc))
      let vc := match const with
        | Sum.inl ofs => Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)
        | Sum.inr (id, ofs) => CompCert4Lean.Common.Globalenvs.Genv.symbol_address _ge id ofs
      Val.add vb (Val.add vo vc)

def eval_addrmode64 (_ge : genv) (a : addrmode) (rs : regset) : val :=
  match a with
  | .Addrmode base ofs const =>
      let vb := match base with | none => Vlong CompCert4Lean.Lib.Integers.Int64.zero | some r => Pregmap.get (.IR r) rs
      let vo := match ofs with
        | none => Vlong CompCert4Lean.Lib.Integers.Int64.zero
        | some (r, sc) =>
            match zeq sc z1 with
            | .left _ => Pregmap.get (.IR r) rs
            | .right _ => Val.mull (Pregmap.get (.IR r) rs) (Vlong (CompCert4Lean.Lib.Integers.Int64.repr sc))
      let vc := match const with
        | Sum.inl ofs => Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)
        | Sum.inr (id, ofs) => CompCert4Lean.Common.Globalenvs.Genv.symbol_address _ge id ofs
      Val.addl vb (Val.addl vo vc)

def eval_addrmode (ge : genv) (a : addrmode) (rs : regset) : val :=
  if CompCert4Lean.X86_64.Archi.ptr64 then eval_addrmode64 ge a rs else eval_addrmode32 ge a rs

def compare_ints (x y : val) (rs : regset) (m : mem) : regset :=
  Pregmap.set (.CR .ZF) (Val.cmpu (Mem.valid_pointer m) .Ceq x y)
    (Pregmap.set (.CR .CF) (Val.cmpu (Mem.valid_pointer m) .Clt x y)
      (Pregmap.set (.CR .SF) (Val.negative (Val.sub x y))
        (Pregmap.set (.CR .OF) (Val.sub_overflow x y)
          (Pregmap.set (.CR .PF) Vundef rs))))

def compare_longs (x y : val) (rs : regset) (m : mem) : regset :=
  Pregmap.set (.CR .ZF) (Val.maketotal (Val.cmplu (Mem.valid_pointer m) .Ceq x y))
    (Pregmap.set (.CR .CF) (Val.maketotal (Val.cmplu (Mem.valid_pointer m) .Clt x y))
      (Pregmap.set (.CR .SF) (Val.negativel (Val.subl x y))
        (Pregmap.set (.CR .OF) (Val.subl_overflow x y)
          (Pregmap.set (.CR .PF) Vundef rs))))

def compare_floats (vx vy : val) (rs : regset) : regset :=
  match vx, vy with
  | .Vfloat x, .Vfloat y =>
      let zf := Val.of_bool (CompCert4Lean.Lib.Floats.Float.cmp .Ceq x y ||
        !(CompCert4Lean.Lib.Floats.Float.ordered x y))
      let cf := Val.of_bool (!(CompCert4Lean.Lib.Floats.Float.cmp .Cge x y))
      let pf := Val.of_bool (!(CompCert4Lean.Lib.Floats.Float.ordered x y))
      Pregmap.set (.CR .ZF) zf
        (Pregmap.set (.CR .CF) cf
          (Pregmap.set (.CR .PF) pf
            (Pregmap.set (.CR .SF) Vundef (Pregmap.set (.CR .OF) Vundef rs))))
  | _, _ => undef_regs [.CR .ZF, .CR .CF, .CR .PF, .CR .SF, .CR .OF] rs

def compare_floats32 (vx vy : val) (rs : regset) : regset :=
  match vx, vy with
  | .Vsingle x, .Vsingle y =>
      let zf := Val.of_bool (CompCert4Lean.Lib.Floats.Float32.cmp .Ceq x y ||
        !(CompCert4Lean.Lib.Floats.Float32.ordered x y))
      let cf := Val.of_bool (!(CompCert4Lean.Lib.Floats.Float32.cmp .Cge x y))
      let pf := Val.of_bool (!(CompCert4Lean.Lib.Floats.Float32.ordered x y))
      Pregmap.set (.CR .ZF) zf
        (Pregmap.set (.CR .CF) cf
          (Pregmap.set (.CR .PF) pf
            (Pregmap.set (.CR .SF) Vundef (Pregmap.set (.CR .OF) Vundef rs))))
  | _, _ => undef_regs [.CR .ZF, .CR .CF, .CR .PF, .CR .SF, .CR .OF] rs

private def flagValue (r : crbit) (rs : regset) : Option int :=
  match Pregmap.get (.CR r) rs with
  | .Vint v => some v
  | _ => none

def eval_testcond (c : testcond) (rs : regset) : Option Bool :=
  match c with
  | .Cond_e => (flagValue .ZF rs).map (fun n =>
      CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one)
  | .Cond_ne => (flagValue .ZF rs).map (fun n =>
      CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero)
  | .Cond_b => (flagValue .CF rs).map (fun n =>
      CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one)
  | .Cond_be => match flagValue .CF rs, flagValue .ZF rs with
      | some c, some z => some (CompCert4Lean.Lib.Integers.Int.eq c CompCert4Lean.Lib.Integers.Int.one ||
          CompCert4Lean.Lib.Integers.Int.eq z CompCert4Lean.Lib.Integers.Int.one)
      | _, _ => none
  | .Cond_ae => (flagValue .CF rs).map (fun n =>
      CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero)
  | .Cond_a => match flagValue .CF rs, flagValue .ZF rs with
      | some c, some z => some (CompCert4Lean.Lib.Integers.Int.eq c CompCert4Lean.Lib.Integers.Int.zero &&
          CompCert4Lean.Lib.Integers.Int.eq z CompCert4Lean.Lib.Integers.Int.zero)
      | _, _ => none
  | .Cond_l => match flagValue .OF rs, flagValue .SF rs with
      | some o, some s => some (CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.xor o s) CompCert4Lean.Lib.Integers.Int.one)
      | _, _ => none
  | .Cond_le => match flagValue .OF rs, flagValue .SF rs, flagValue .ZF rs with
      | some o, some s, some z => some (CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.xor o s) CompCert4Lean.Lib.Integers.Int.one ||
          CompCert4Lean.Lib.Integers.Int.eq z CompCert4Lean.Lib.Integers.Int.one)
      | _, _, _ => none
  | .Cond_ge => match flagValue .OF rs, flagValue .SF rs with
      | some o, some s => some (CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.xor o s) CompCert4Lean.Lib.Integers.Int.zero)
      | _, _ => none
  | .Cond_g => match flagValue .OF rs, flagValue .SF rs, flagValue .ZF rs with
      | some o, some s, some z => some (CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.xor o s) CompCert4Lean.Lib.Integers.Int.zero &&
          CompCert4Lean.Lib.Integers.Int.eq z CompCert4Lean.Lib.Integers.Int.zero)
      | _, _, _ => none
  | .Cond_p => (flagValue .PF rs).map (fun n =>
      CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one)
  | .Cond_np => (flagValue .PF rs).map (fun n =>
      CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero)

/-! ## Small-step execution surface -/

inductive outcome : Type where
  | Next (rs : regset) (m : mem)
  | Stuck

export outcome (Next Stuck)

def nextinstr (rs : regset) : regset :=
  Pregmap.set (.PC) (Val.offset_ptr (Pregmap.get (.PC) rs) CompCert4Lean.Lib.Integers.Ptrofs.one) rs

def nextinstr_nf (rs : regset) : regset :=
  nextinstr (undef_regs [.CR .ZF, .CR .CF, .CR .PF, .CR .SF, .CR .OF] rs)

def goto_label (f : function) (lbl : label) (rs : regset) (m : mem) : outcome :=
  match label_pos lbl z0 f.fn_code with
  | none => .Stuck
  | some pos =>
      match Pregmap.get .PC rs with
      | .Vptr b _ => .Next (Pregmap.set .PC (.Vptr b (CompCert4Lean.Lib.Integers.Ptrofs.repr pos)) rs) m
      | _ => .Stuck

def exec_load (_ge : genv) (chunk : memory_chunk) (m : mem)
    (a : addrmode) (rs : regset) (rd : preg) : outcome :=
  match Mem.loadv chunk m (eval_addrmode _ge a rs) with
  | some v => .Next (nextinstr_nf (Pregmap.set rd v rs)) m
  | none => .Stuck

def exec_store (_ge : genv) (chunk : memory_chunk) (m : mem)
    (a : addrmode) (rs : regset) (r1 : preg) (destroyed : List preg) : outcome :=
  match Mem.storev chunk m (eval_addrmode _ge a rs) (Pregmap.get r1 rs) with
  | some m' => .Next (nextinstr_nf (undef_regs destroyed rs)) m'
  | none => .Stuck

private def divmodu2Int (nhi nlo d : int) : Option (int × int) :=
  if CompCert4Lean.Lib.Integers.Int.eq d CompCert4Lean.Lib.Integers.Int.zero then none
  else
    let qr := ZArith.BinInt.Z.div_eucl
      (ZArith.BinInt.Z.add
        (ZArith.BinInt.Z.mul
          (CompCert4Lean.Lib.Integers.Int.unsigned nhi)
          CompCert4Lean.Lib.Integers.Int.modulus)
        (CompCert4Lean.Lib.Integers.Int.unsigned nlo))
      (CompCert4Lean.Lib.Integers.Int.unsigned d)
    match CompCert4Lean.Lib.Coqlib.zle qr.1 CompCert4Lean.Lib.Integers.Int.max_unsigned with
    | .left _ => some (CompCert4Lean.Lib.Integers.Int.repr qr.1,
        CompCert4Lean.Lib.Integers.Int.repr qr.2)
    | .right _ => none

private def divmods2Int (nhi nlo d : int) : Option (int × int) :=
  if CompCert4Lean.Lib.Integers.Int.eq d CompCert4Lean.Lib.Integers.Int.zero then none
  else
    let n := ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.mul
        (CompCert4Lean.Lib.Integers.Int.signed nhi)
        CompCert4Lean.Lib.Integers.Int.modulus)
      (CompCert4Lean.Lib.Integers.Int.unsigned nlo)
    let sd := CompCert4Lean.Lib.Integers.Int.signed d
    let q := ZArith.BinInt.Z.quot n sd
    let r := ZArith.BinInt.Z.sub n (ZArith.BinInt.Z.mul q sd)
    match CompCert4Lean.Lib.Coqlib.zle CompCert4Lean.Lib.Integers.Int.min_signed q,
      CompCert4Lean.Lib.Coqlib.zle q CompCert4Lean.Lib.Integers.Int.max_signed with
    | .left _, .left _ => some (CompCert4Lean.Lib.Integers.Int.repr q,
        CompCert4Lean.Lib.Integers.Int.repr r)
    | _, _ => none

private def divmodu2Int64 (nhi nlo d : int64) : Option (int64 × int64) :=
  if CompCert4Lean.Lib.Integers.Int64.eq d CompCert4Lean.Lib.Integers.Int64.zero then none
  else
    let qr := ZArith.BinInt.Z.div_eucl
      (ZArith.BinInt.Z.add
        (ZArith.BinInt.Z.mul
          (CompCert4Lean.Lib.Integers.Int64.unsigned nhi)
          CompCert4Lean.Lib.Integers.Int64.modulus)
        (CompCert4Lean.Lib.Integers.Int64.unsigned nlo))
      (CompCert4Lean.Lib.Integers.Int64.unsigned d)
    match CompCert4Lean.Lib.Coqlib.zle qr.1 CompCert4Lean.Lib.Integers.Int64.max_unsigned with
    | .left _ => some (CompCert4Lean.Lib.Integers.Int64.repr qr.1,
        CompCert4Lean.Lib.Integers.Int64.repr qr.2)
    | .right _ => none

private def divmods2Int64 (nhi nlo d : int64) : Option (int64 × int64) :=
  if CompCert4Lean.Lib.Integers.Int64.eq d CompCert4Lean.Lib.Integers.Int64.zero then none
  else
    let n := ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.mul
        (CompCert4Lean.Lib.Integers.Int64.signed nhi)
        CompCert4Lean.Lib.Integers.Int64.modulus)
      (CompCert4Lean.Lib.Integers.Int64.unsigned nlo)
    let sd := CompCert4Lean.Lib.Integers.Int64.signed d
    let q := ZArith.BinInt.Z.quot n sd
    let r := ZArith.BinInt.Z.sub n (ZArith.BinInt.Z.mul q sd)
    match CompCert4Lean.Lib.Coqlib.zle CompCert4Lean.Lib.Integers.Int64.min_signed q,
      CompCert4Lean.Lib.Coqlib.zle q CompCert4Lean.Lib.Integers.Int64.max_signed with
    | .left _, .left _ => some (CompCert4Lean.Lib.Integers.Int64.repr q,
        CompCert4Lean.Lib.Integers.Int64.repr r)
    | _, _ => none

def exec_instr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ge : genv) (f : function) (i : instruction)
    (rs : regset) (m : mem) : outcome :=
  match i with
  | .Pmov_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd) (Pregmap.get (.IR r1) rs) rs)) m
  | .Pmovl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd) (.Vint n) rs)) m
  | .Pmovq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd) (.Vlong n) rs)) m
  | .Pmov_rs rd id => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Genv.symbol_address ge id CompCert4Lean.Lib.Integers.Ptrofs.zero) rs)) m
  | .Pmovl_rm rd a => exec_load ge Mint32 m a rs (.IR rd)
  | .Pmovq_rm rd a => exec_load ge Mint64 m a rs (.IR rd)
  | .Pmovl_mr a r1 => exec_store ge Mint32 m a rs (.IR r1) []
  | .Pmovq_mr a r1 => exec_store ge Mint64 m a rs (.IR r1) []
  | .Pmovsd_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd) (Pregmap.get (.FR r1) rs) rs)) m
  | .Pmovsd_fi rd n => .Next (nextinstr (Pregmap.set (.FR rd) (.Vfloat n) rs)) m
  | .Pmovsd_fm rd a => exec_load ge Mfloat64 m a rs (.FR rd)
  | .Pmovsd_mf a r1 => exec_store ge Mfloat64 m a rs (.FR r1) []
  | .Pmovss_fi rd n => .Next (nextinstr (Pregmap.set (.FR rd) (.Vsingle n) rs)) m
  | .Pmovss_fm rd a => exec_load ge Mfloat32 m a rs (.FR rd)
  | .Pmovss_mf a r1 => exec_store ge Mfloat32 m a rs (.FR r1) []
  | .Pfldl_m a => exec_load ge Mfloat64 m a rs .ST0
  | .Pfstpl_m a => exec_store ge Mfloat64 m a rs .ST0 [.ST0]
  | .Pflds_m a => exec_load ge Mfloat32 m a rs .ST0
  | .Pfstps_m a => exec_store ge Mfloat32 m a rs .ST0 [.ST0]
  | .Pmovb_mr a r1 => exec_store ge Mint8unsigned m a rs (.IR r1) []
  | .Pmovw_mr a r1 => exec_store ge Mint16unsigned m a rs (.IR r1) []
  | .Pmovzb_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.zero_ext (zOfNat 8) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pmovzb_rm rd a => exec_load ge Mint8unsigned m a rs (.IR rd)
  | .Pmovsb_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.sign_ext (zOfNat 8) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pmovsb_rm rd a => exec_load ge Mint8signed m a rs (.IR rd)
  | .Pmovzw_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.zero_ext (zOfNat 16) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pmovzw_rm rd a => exec_load ge Mint16unsigned m a rs (.IR rd)
  | .Pmovsw_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.sign_ext (zOfNat 16) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pmovsw_rm rd a => exec_load ge Mint16signed m a rs (.IR rd)
  | .Pmovzl_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.longofintu (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pmovsl_rr rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.longofint (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pmovls_rr rd => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.loword (Pregmap.get (.IR rd) rs)) rs)) m
  | .Pcvtsd2ss_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.singleoffloat (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pcvtss2sd_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.floatofsingle (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pcvttsd2si_rf rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.maketotal (Val.intoffloat (Pregmap.get (.FR r1) rs))) rs)) m
  | .Pcvtsi2sd_fr rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.maketotal (Val.floatofint
        (binary64_certificate := binary64_certificate) (Pregmap.get (.IR r1) rs))) rs)) m
  | .Pcvttss2si_rf rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.maketotal (Val.intofsingle (Pregmap.get (.FR r1) rs))) rs)) m
  | .Pcvtsi2ss_fr rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.maketotal (Val.singleofint
        (binary32_certificate := binary32_certificate) (Pregmap.get (.IR r1) rs))) rs)) m
  | .Pcvttsd2sl_rf rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.maketotal (Val.longoffloat (Pregmap.get (.FR r1) rs))) rs)) m
  | .Pcvtsl2sd_fr rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.maketotal (Val.floatoflong
        (binary64_certificate := binary64_certificate) (Pregmap.get (.IR r1) rs))) rs)) m
  | .Pcvttss2sl_rf rd r1 => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.maketotal (Val.longofsingle (Pregmap.get (.FR r1) rs))) rs)) m
  | .Pcvtsl2ss_fr rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.maketotal (Val.singleoflong
        (binary32_certificate := binary32_certificate) (Pregmap.get (.IR r1) rs))) rs)) m
  | .Pleal rd a => .Next (nextinstr (Pregmap.set (.IR rd) (eval_addrmode32 ge a rs) rs)) m
  | .Pleaq rd a => .Next (nextinstr (Pregmap.set (.IR rd) (eval_addrmode64 ge a rs) rs)) m
  | .Pnegl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.neg (Pregmap.get (.IR rd) rs)) rs)) m
  | .Pnegq rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.negl (Pregmap.get (.IR rd) rs)) rs)) m
  | .Paddl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.add (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Paddq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.addl (Pregmap.get (.IR rd) rs) (.Vlong n)) rs)) m
  | .Psubl_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.sub (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Psubq_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.subl (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pimull_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.mul (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pimulq_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.mull (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pimull_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.mul (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pimulq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.mull (Pregmap.get (.IR rd) rs) (.Vlong n)) rs)) m
  | .Pimull_r r1 => .Next (nextinstr_nf
      (Pregmap.set (.IR .RAX) (Val.mul (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs))
        (Pregmap.set (.IR .RDX) (Val.mulhs (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs)) rs))) m
  | .Pimulq_r r1 => .Next (nextinstr_nf
      (Pregmap.set (.IR .RAX) (Val.mull (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs))
        (Pregmap.set (.IR .RDX) (Val.mullhs (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs)) rs))) m
  | .Pmull_r r1 => .Next (nextinstr_nf
      (Pregmap.set (.IR .RAX) (Val.mul (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs))
        (Pregmap.set (.IR .RDX) (Val.mulhu (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs)) rs))) m
  | .Pmulq_r r1 => .Next (nextinstr_nf
      (Pregmap.set (.IR .RAX) (Val.mull (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs))
        (Pregmap.set (.IR .RDX) (Val.mullhu (Pregmap.get (.IR .RAX) rs) (Pregmap.get (.IR r1) rs)) rs))) m
  | .Pcltd => .Next (nextinstr_nf (Pregmap.set (.IR .RDX)
      (Val.shr (Pregmap.get (.IR .RAX) rs) (.Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 31)))) rs)) m
  | .Pcqto => .Next (nextinstr_nf (Pregmap.set (.IR .RDX)
      (Val.shrl (Pregmap.get (.IR .RAX) rs) (.Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 63)))) rs)) m
  | .Pdivl r1 =>
      match Pregmap.get (.IR .RDX) rs, Pregmap.get (.IR .RAX) rs, Pregmap.get (.IR r1) rs with
      | .Vint nh, .Vint nl, .Vint d =>
          match divmodu2Int nh nl d with
          | some (q, r) => .Next (nextinstr_nf
              (Pregmap.set (.IR .RAX) (.Vint q) (Pregmap.set (.IR .RDX) (.Vint r) rs))) m
          | none => .Stuck
      | _, _, _ => .Stuck
  | .Pdivq r1 =>
      match Pregmap.get (.IR .RDX) rs, Pregmap.get (.IR .RAX) rs, Pregmap.get (.IR r1) rs with
      | .Vlong nh, .Vlong nl, .Vlong d =>
          match divmodu2Int64 nh nl d with
          | some (q, r) => .Next (nextinstr_nf
              (Pregmap.set (.IR .RAX) (.Vlong q) (Pregmap.set (.IR .RDX) (.Vlong r) rs))) m
          | none => .Stuck
      | _, _, _ => .Stuck
  | .Pidivl r1 =>
      match Pregmap.get (.IR .RDX) rs, Pregmap.get (.IR .RAX) rs, Pregmap.get (.IR r1) rs with
      | .Vint nh, .Vint nl, .Vint d =>
          match divmods2Int nh nl d with
          | some (q, r) => .Next (nextinstr_nf
              (Pregmap.set (.IR .RAX) (.Vint q) (Pregmap.set (.IR .RDX) (.Vint r) rs))) m
          | none => .Stuck
      | _, _, _ => .Stuck
  | .Pidivq r1 =>
      match Pregmap.get (.IR .RDX) rs, Pregmap.get (.IR .RAX) rs, Pregmap.get (.IR r1) rs with
      | .Vlong nh, .Vlong nl, .Vlong d =>
          match divmods2Int64 nh nl d with
          | some (q, r) => .Next (nextinstr_nf
              (Pregmap.set (.IR .RAX) (.Vlong q) (Pregmap.set (.IR .RDX) (.Vlong r) rs))) m
          | none => .Stuck
      | _, _, _ => .Stuck
  | .Pandl_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.and (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pandq_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.andl (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pandl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.and (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pandq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.andl (Pregmap.get (.IR rd) rs) (.Vlong n)) rs)) m
  | .Porl_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.or (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Porq_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.orl (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Porl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.or (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Porq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.orl (Pregmap.get (.IR rd) rs) (.Vlong n)) rs)) m
  | .Pxorl_r rd => .Next (nextinstr_nf (Pregmap.set (.IR rd) Vzero rs)) m
  | .Pxorq_r rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (.Vlong CompCert4Lean.Lib.Integers.Int64.zero) rs)) m
  | .Pxorl_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.xor (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pxorq_rr rd r1 => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.xorl (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR r1) rs)) rs)) m
  | .Pxorl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.xor (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pxorq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.xorl (Pregmap.get (.IR rd) rs) (.Vlong n)) rs)) m
  | .Pnotl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.notint (Pregmap.get (.IR rd) rs)) rs)) m
  | .Pnotq rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.notl (Pregmap.get (.IR rd) rs)) rs)) m
  | .Psall_rcl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shl (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR .RCX) rs)) rs)) m
  | .Psalq_rcl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shll (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR .RCX) rs)) rs)) m
  | .Psall_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shl (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Psalq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shll (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pshrl_rcl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shru (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR .RCX) rs)) rs)) m
  | .Pshrq_rcl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shrlu (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR .RCX) rs)) rs)) m
  | .Pshrl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shru (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pshrq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shrlu (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Psarl_rcl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shr (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR .RCX) rs)) rs)) m
  | .Psarq_rcl rd => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shrl (Pregmap.get (.IR rd) rs) (Pregmap.get (.IR .RCX) rs)) rs)) m
  | .Psarl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shr (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Psarq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.shrl (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pshld_ri rd r1 n =>
      let v := Val.or (Val.shl (Pregmap.get (.IR rd) rs) (.Vint n))
        (Val.shru (Pregmap.get (.IR r1) rs)
          (.Vint (CompCert4Lean.Lib.Integers.Int.sub CompCert4Lean.Lib.Integers.Int.iwordsize n)))
      .Next (nextinstr_nf (Pregmap.set (.IR rd) v rs)) m
  | .Prorl_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.ror (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Prorq_ri rd n => .Next (nextinstr_nf (Pregmap.set (.IR rd)
      (Val.rorl (Pregmap.get (.IR rd) rs) (.Vint n)) rs)) m
  | .Pcmpl_rr r1 r2 => .Next (nextinstr (compare_ints
      (Pregmap.get (.IR r1) rs) (Pregmap.get (.IR r2) rs) rs m)) m
  | .Pcmpq_rr r1 r2 => .Next (nextinstr (compare_longs
      (Pregmap.get (.IR r1) rs) (Pregmap.get (.IR r2) rs) rs m)) m
  | .Pcmpl_ri r1 n => .Next (nextinstr (compare_ints
      (Pregmap.get (.IR r1) rs) (.Vint n) rs m)) m
  | .Pcmpq_ri r1 n => .Next (nextinstr (compare_longs
      (Pregmap.get (.IR r1) rs) (.Vlong n) rs m)) m
  | .Ptestl_rr r1 r2 => .Next (nextinstr (compare_ints
      (Val.and (Pregmap.get (.IR r1) rs) (Pregmap.get (.IR r2) rs)) Vzero rs m)) m
  | .Ptestq_rr r1 r2 => .Next (nextinstr (compare_longs
      (Val.andl (Pregmap.get (.IR r1) rs) (Pregmap.get (.IR r2) rs))
        (.Vlong CompCert4Lean.Lib.Integers.Int64.zero) rs m)) m
  | .Ptestl_ri r1 n => .Next (nextinstr (compare_ints
      (Val.and (Pregmap.get (.IR r1) rs) (.Vint n)) Vzero rs m)) m
  | .Ptestq_ri r1 n => .Next (nextinstr (compare_longs
      (Val.andl (Pregmap.get (.IR r1) rs) (.Vlong n))
        (.Vlong CompCert4Lean.Lib.Integers.Int64.zero) rs m)) m
  | .Pcmov c rd r1 =>
      let v := match eval_testcond c rs with
        | some b => if b then Pregmap.get (.IR r1) rs else Pregmap.get (.IR rd) rs
        | none => Vundef
      .Next (nextinstr (Pregmap.set (.IR rd) v rs)) m
  | .Psetcc c rd => .Next (nextinstr (Pregmap.set (.IR rd)
      (Val.of_optbool (eval_testcond c rs)) rs)) m
  | .Paddd_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.addf (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Psubd_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.subf (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pmuld_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.mulf (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pdivd_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.divf (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pnegd rd => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.negf (Pregmap.get (.FR rd) rs)) rs)) m
  | .Pabsd rd => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.absf (Pregmap.get (.FR rd) rs)) rs)) m
  | .Pcomisd_ff r1 r2 => .Next (nextinstr
      (compare_floats (Pregmap.get (.FR r1) rs) (Pregmap.get (.FR r2) rs) rs)) m
  | .Pxorpd_f rd => .Next (nextinstr_nf (Pregmap.set (.FR rd)
      (.Vfloat CompCert4Lean.Lib.Floats.Float.zero) rs)) m
  | .Pmaxsd rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (CompCert4Lean.X86.Op.maxf (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pminsd rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (CompCert4Lean.X86.Op.minf (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Padds_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.addfs (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Psubs_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.subfs (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pmuls_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.mulfs (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pdivs_ff rd r1 => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.divfs (Pregmap.get (.FR rd) rs) (Pregmap.get (.FR r1) rs)) rs)) m
  | .Pnegs rd => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.negfs (Pregmap.get (.FR rd) rs)) rs)) m
  | .Pabss rd => .Next (nextinstr (Pregmap.set (.FR rd)
      (Val.absfs (Pregmap.get (.FR rd) rs)) rs)) m
  | .Pcomiss_ff r1 r2 => .Next (nextinstr
      (compare_floats32 (Pregmap.get (.FR r1) rs) (Pregmap.get (.FR r2) rs) rs)) m
  | .Pxorps_f rd => .Next (nextinstr_nf (Pregmap.set (.FR rd)
      (.Vsingle CompCert4Lean.Lib.Floats.Float32.zero) rs)) m
  | .Pjmp_l l => goto_label f l rs m
  | .Pjmp_s symb _ => .Next (Pregmap.set .PC
      (Genv.symbol_address ge symb CompCert4Lean.Lib.Integers.Ptrofs.zero) rs) m
  | .Pjmp_r r _ => .Next (Pregmap.set .PC (Pregmap.get (.IR r) rs) rs) m
  | .Pjcc c l => match eval_testcond c rs with
      | some true => goto_label f l rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck
  | .Pjcc2 c1 c2 l => match eval_testcond c1 rs, eval_testcond c2 rs with
      | some true, some true => goto_label f l rs m
      | some _, some _ => .Next (nextinstr rs) m
      | _, _ => .Stuck
  | .Pjmptbl r tbl => match Pregmap.get (.IR r) rs with
      | .Vint n => match CompCert4Lean.Lib.Coqlib.list_nth_z tbl
          (CompCert4Lean.Lib.Integers.Int.unsigned n) with
          | none => .Stuck
          | some l => goto_label f l
              (Pregmap.set (.IR .RAX) Vundef (Pregmap.set (.IR .RDX) Vundef rs)) m
      | _ => .Stuck
  | .Pcall_s symb _ => .Next
      (Pregmap.set .RA (Val.offset_ptr (Pregmap.get .PC rs)
          CompCert4Lean.Lib.Integers.Ptrofs.one)
        (Pregmap.set .PC (Genv.symbol_address ge symb
          CompCert4Lean.Lib.Integers.Ptrofs.zero) rs)) m
  | .Pcall_r r _ => .Next
      (Pregmap.set .RA (Val.offset_ptr (Pregmap.get .PC rs)
          CompCert4Lean.Lib.Integers.Ptrofs.one)
        (Pregmap.set .PC (Pregmap.get (.IR r) rs) rs)) m
  | .Pret => .Next (Pregmap.set .PC (Pregmap.get .RA rs) rs) m
  | .Pmov_rm_a rd a => exec_load ge (if CompCert4Lean.X86_64.Archi.ptr64 then Many64 else Many32)
      m a rs (.IR rd)
  | .Pmov_mr_a a r1 => exec_store ge
      (if CompCert4Lean.X86_64.Archi.ptr64 then Many64 else Many32) m a rs (.IR r1) []
  | .Pmovsd_fm_a rd a => exec_load ge Many64 m a rs (.FR rd)
  | .Pmovsd_mf_a a r1 => exec_store ge Many64 m a rs (.FR r1) []
  | .Plabel _ => .Next (nextinstr rs) m
  | .Pallocframe sz ofs_ra ofs_link =>
      let mm := Mem.alloc m z0 sz
      let sp := .Vptr mm.2 CompCert4Lean.Lib.Integers.Ptrofs.zero
      match Mem.storev Mptr mm.1 (Val.offset_ptr sp ofs_link) (Pregmap.get (.IR .RSP) rs) with
      | none => .Stuck
      | some m2 => match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) (Pregmap.get .RA rs) with
          | none => .Stuck
          | some m3 => .Next (nextinstr
              (Pregmap.set (.IR .RAX) (Pregmap.get (.IR .RSP) rs)
                (Pregmap.set (.IR .RSP) sp rs))) m3
  | .Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offset_ptr (Pregmap.get (.IR .RSP) rs) ofs_ra) with
      | none => .Stuck
      | some ra => match Mem.loadv Mptr m
          (Val.offset_ptr (Pregmap.get (.IR .RSP) rs) ofs_link) with
          | none => .Stuck
          | some sp => match Pregmap.get (.IR .RSP) rs with
              | .Vptr stk _ => match Mem.free m stk z0 sz with
                  | none => .Stuck
                  | some m' => .Next (nextinstr
                      (Pregmap.set (.IR .RSP) sp (Pregmap.set .RA ra rs))) m'
              | _ => .Stuck
  | .Pbuiltin _ _ _ => .Stuck
  | .Padcl_ri _ _ | .Padcl_rr _ _ | .Paddl_mi _ _ | .Paddl_rr _ _
  | .Pbsfl _ _ | .Pbsfq _ _ | .Pbsrl _ _ | .Pbsrq _ _ | .Pbswap64 _
  | .Pbswap32 _ | .Pbswap16 _ | .Pcfi_adjust _ | .Pfmadd132 _ _ _
  | .Pfmadd213 _ _ _ | .Pfmadd231 _ _ _ | .Pfmsub132 _ _ _ | .Pfmsub213 _ _ _
  | .Pfmsub231 _ _ _ | .Pfnmadd132 _ _ _ | .Pfnmadd213 _ _ _ | .Pfnmadd231 _ _ _
  | .Pfnmsub132 _ _ _ | .Pfnmsub213 _ _ _ | .Pfnmsub231 _ _ _ | .Pmovb_rm _ _
  | .Pmovq_rf _ _ | .Pmovsq_mr _ _ | .Pmovsq_rm _ _ | .Pmovsb | .Pmovsw
  | .Pmovw_rm _ _ | .Pnop | .Prep_movsl | .Psbbl_rr _ _ | .Psqrtsd _ _
  | .Psubl_ri _ _ | .Psubq_ri _ _ => .Stuck

def preg_of (r : mreg) : preg :=
  match r with
  | .AX => .IR .RAX | .BX => .IR .RBX | .CX => .IR .RCX | .DX => .IR .RDX
  | .SI => .IR .RSI | .DI => .IR .RDI | .BP => .IR .RBP
  | .R8 => .IR .R8 | .R9 => .IR .R9 | .R10 => .IR .R10 | .R11 => .IR .R11
  | .R12 => .IR .R12 | .R13 => .IR .R13 | .R14 => .IR .R14 | .R15 => .IR .R15
  | .X0 => .FR .XMM0 | .X1 => .FR .XMM1 | .X2 => .FR .XMM2 | .X3 => .FR .XMM3
  | .X4 => .FR .XMM4 | .X5 => .FR .XMM5 | .X6 => .FR .XMM6 | .X7 => .FR .XMM7
  | .X8 => .FR .XMM8 | .X9 => .FR .XMM9 | .X10 => .FR .XMM10 | .X11 => .FR .XMM11
  | .X12 => .FR .XMM12 | .X13 => .FR .XMM13 | .X14 => .FR .XMM14 | .X15 => .FR .XMM15
  | .FP0 => .ST0

def undef_caller_save_regs (cfg : CompilerConfig) (rs : regset) : regset :=
  fun r =>
    let saved := List.map preg_of
      (List.filter (fun mr => CompCert4Lean.X86.Conventions1.is_callee_save cfg mr)
        CompCert4Lean.X86.Machregs.all_mregs)
    match CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec PregEq.eq r saved with
    | .left _ => Pregmap.get r rs
    | .right _ =>
        match PregEq.eq r (.IR SP) with
        | .left _ => Pregmap.get r rs
        | .right _ => Vundef

inductive extcall_arg (cfg : CompilerConfig) (rs : regset) (m : mem) : loc → val → Prop where
  | extcall_arg_reg (r : mreg) :
      extcall_arg cfg rs m (.R r) (Pregmap.get (preg_of r) rs)
  | extcall_arg_stack (ofs : Z) (ty : typ) (bofs : Z) (v : val)
      (hb : bofs = zAdd
        (CompCert4Lean.X86.Stacklayout.fe_ofs_arg cfg)
        (zMul (zOfNat 4) ofs))
      (hv : Mem.loadv (chunk_of_type ty) m
        (Val.offset_ptr (Pregmap.get (.IR .RSP) rs) (CompCert4Lean.Lib.Integers.Ptrofs.repr bofs)) = some v) :
      extcall_arg cfg rs m (.S Outgoing ofs ty) v

export extcall_arg (extcall_arg_reg extcall_arg_stack)

inductive extcall_arg_pair (cfg : CompilerConfig) (rs : regset) (m : mem) : rpair loc → val → Prop where
  | extcall_arg_one (l : loc) (v : val) :
      extcall_arg cfg rs m l v → extcall_arg_pair cfg rs m (.One l) v
  | extcall_arg_twolong (hi lo : loc) (vhi vlo : val) :
      extcall_arg cfg rs m hi vhi → extcall_arg cfg rs m lo vlo →
      extcall_arg_pair cfg rs m (.Twolong hi lo) (Val.longofwords vhi vlo)

export extcall_arg_pair (extcall_arg_one extcall_arg_twolong)

def extcall_arguments (cfg : CompilerConfig) (rs : regset) (m : mem)
    (sg : signature) (args : List val) : Prop :=
  CompCert4Lean.Lib.Coqlib.list_forall2 (extcall_arg_pair cfg rs m)
    (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) args

def loc_external_result (sg : signature) : rpair preg :=
  map_rpair preg_of (CompCert4Lean.X86.Conventions1.loc_result sg)

def extcall_arguments_determStatement : Prop :=
  ∀ cfg rs m sg args1 args2, extcall_arguments cfg rs m sg args1 →
    extcall_arguments cfg rs m sg args2 → args1 = args2

def extcall_arguments_determ := extcall_arguments_determStatement

inductive state : Type where
  | State (rs : regset) (m : mem)

export state (State)

def initial_regset (p : program) : regset :=
  let ge := CompCert4Lean.Common.Globalenvs.Genv.globalenv p
  Pregmap.set (.IR .RSP) Vnullptr
    (Pregmap.set .RA Vnullptr
      (Pregmap.set .PC
        (CompCert4Lean.Common.Globalenvs.Genv.symbol_address ge p.prog_main
          CompCert4Lean.Lib.Integers.Ptrofs.zero)
        (Pregmap.init Vundef)))

inductive step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls) (ge : genv) :
    state → trace → state → Prop where
  | exec_step_internal (b : block) (ofs : ptrofs) (f : function)
      (i : instruction) (rs : regset) (m : mem) (rs' : regset) (m' : mem)
      (hpc : Pregmap.get .PC rs = .Vptr b ofs)
      (hf : Genv.find_funct_ptr ge b = some (Internal f))
      (hi : find_instr (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) f.fn_code = some i)
      (he : exec_instr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge f i rs m = .Next rs' m') :
      step cfg xi ge (.State rs m) E0 (.State rs' m')
  | exec_step_builtin (b : block) (ofs : ptrofs) (f : function)
      (ef : external_function) (args : List (builtin_arg preg))
      (res : builtin_res preg) (rs : regset) (m : mem) (vargs : List val)
      (t : trace) (vres : val) (rs' : regset) (m' : mem)
      (hpc : Pregmap.get .PC rs = .Vptr b ofs)
      (hf : Genv.find_funct_ptr ge b = some (Internal f))
      (hi : find_instr (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) f.fn_code =
        some (.Pbuiltin ef args res))
      (hargs : eval_builtin_args (Genv.to_senv ge)
        (fun r => Pregmap.get r rs) (Pregmap.get (.IR .RSP) rs) m args vargs)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m')
      (hrs : rs' = nextinstr_nf
        (set_res res vres
          (undef_regs (List.map preg_of (destroyed_by_builtin ef)) rs))) :
      step cfg xi ge (.State rs m) t (.State rs' m')
  | exec_step_external (b : block) (ef : external_function) (args : List val)
      (res : val) (rs : regset) (m : mem) (t : trace) (rs' : regset) (m' : mem)
      (hpc : Pregmap.get .PC rs = .Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero)
      (hf : Genv.find_funct_ptr ge b = some (External ef))
      (hargs : extcall_arguments cfg rs m (ef_sig ef) args)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) args m t res m')
      (hrs : rs' = Pregmap.set .PC (Pregmap.get .RA rs)
        (set_pair (loc_external_result (ef_sig ef)) res
          (undef_caller_save_regs cfg rs))) :
      step cfg xi ge (.State rs m) t (.State rs' m')

export step (exec_step_internal exec_step_builtin exec_step_external)

inductive initial_state (p : program) : state → Prop where
  | initial_state_intro (m0 : mem)
      (hm : CompCert4Lean.Common.Globalenvs.Genv.init_mem p = some m0) :
      initial_state p (.State (initial_regset p) m0)

export initial_state (initial_state_intro)

inductive final_state : state → int → Prop where
  | final_state_intro (rs : regset) (m : mem) (r : int)
      (hpc : Pregmap.get .PC rs = Vnullptr)
      (hrax : Pregmap.get (.IR .RAX) rs = .Vint r) :
      final_state (.State rs m) r

export final_state (final_state_intro)

def semantics
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls) (p : program) :=
  Semantics
    (step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg xi)
    (CompCert4Lean.X86.Asm.initial_state p)
    final_state
    (CompCert4Lean.Common.Globalenvs.Genv.globalenv p)

def semantics_determinateStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi p, determinate (semantics
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg xi p)

def semantics_determinate
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  semantics_determinateStatement
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)

def data_preg : preg → Bool
  | .PC | .CR _ | .RA => false
  | .IR _ | .FR _ | .ST0 => true

end CompCert4Lean.X86.Asm
