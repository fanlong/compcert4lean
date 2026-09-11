import CompCert4Lean.Config
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Lib.Lattice
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86.Conventions1

/-!
# Abstract value domain

Definition-bearing translation of CompCert's `backend/ValueDomain.v`.
Proofs assigned to later proof migration are represented by transparent
proposition descriptors rather than theorem stubs.
-/

namespace CompCert4Lean.Backend.ValueDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Floats
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev float := CompCert4Lean.Lib.Floats.float
private abbrev float32 := CompCert4Lean.Lib.Floats.float32
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev memval := CompCert4Lean.Common.Memdata.memval
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zMin := ZArith.BinInt.Z.min
private abbrev zAbs := ZArith.BinInt.Z.abs
private abbrev zLog2 := ZArith.BinInt.Z.log2
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zQuot := ZArith.BinInt.Z.quot
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zLtb := ZArith.BinInt.Z.ltb
private abbrev zShiftr := ZArith.BinInt.Z.shiftr

private def boolOfSumbool {P Q : Prop} : Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def zle (x y : Z) : Bool := boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle x y)
private def zlt (x y : Z) : Bool := boolOfSumbool (CompCert4Lean.Lib.Coqlib.zlt x y)
private def zeq (x y : Z) : Bool := boolOfSumbool (CompCert4Lean.Lib.Coqlib.zeq x y)
private def peqBool (x y : positive) : Bool := boolOfSumbool (peq x y)
private def strict (cfg : CompilerConfig) : Bool :=
  CompCert4Lean.Driver.Compopts.va_strict cfg

private def cmpWord (c : comparison) (eqv ltv gtv : Bool) : Bool :=
  match c with
  | .Ceq => eqv
  | .Cne => !eqv
  | .Clt => ltv
  | .Cle => ltv || eqv
  | .Cgt => gtv
  | .Cge => gtv || eqv

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev zwordsize := CompCert4Lean.Lib.Integers.Int.zwordsize
private abbrev max_unsigned := CompCert4Lean.Lib.Integers.Int.max_unsigned
private abbrev max_signed := CompCert4Lean.Lib.Integers.Int.max_signed
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int.min_signed
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev divu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev «and» := CompCert4Lean.Lib.Integers.Int.and
private abbrev «or» := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev «not» := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev rol := CompCert4Lean.Lib.Integers.Int.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int.ror
private abbrev shrx := CompCert4Lean.Lib.Integers.Int.shrx
private abbrev testbit := CompCert4Lean.Lib.Integers.Int.testbit
private abbrev zero_ext := CompCert4Lean.Lib.Integers.Int.zero_ext

private def size (x : int) : Z :=
  match unsigned x with
  | .Z0 => z0
  | .Zpos p => .Zpos (PArith.BinPos.Pos.size p)
  | .Zneg p => .Zpos (PArith.BinPos.Pos.size p)

private def mulhs (x y : int) : int := repr (zShiftr (zMul (signed x) (signed y)) zwordsize)
private def mulhu (x y : int) : int := repr (zShiftr (zMul (unsigned x) (unsigned y)) zwordsize)
private def mods (x y : int) : int := sub x (mul (divs x y) y)
private def modu (x y : int) : int := sub x (mul (divu x y) y)
private def cmp (c : comparison) (x y : int) : Bool := cmpWord c (eq x y) (lt x y) (lt y x)
private def cmpu (c : comparison) (x y : int) : Bool := cmpWord c (eq x y) (ltu x y) (ltu y x)
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int64.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int64.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
private abbrev iwordsize' := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev zwordsize := CompCert4Lean.Lib.Integers.Int64.zwordsize
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int64.min_signed
private abbrev eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int64.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int64.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int64.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int64.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int64.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int64.divs
private abbrev divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev «and» := CompCert4Lean.Lib.Integers.Int64.and
private abbrev «or» := CompCert4Lean.Lib.Integers.Int64.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev «not» := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl' := CompCert4Lean.Lib.Integers.Int64.shl'
private abbrev shru' := CompCert4Lean.Lib.Integers.Int64.shru'
private abbrev shr' := CompCert4Lean.Lib.Integers.Int64.shr'
private abbrev ror := CompCert4Lean.Lib.Integers.Int64.ror
private abbrev shrx' := CompCert4Lean.Lib.Integers.Int64.shrx'
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev hiword := CompCert4Lean.Lib.Integers.Int64.hiword
private abbrev ofwords := CompCert4Lean.Lib.Integers.Int64.ofwords

private def mulhs (x y : int64) : int64 := repr (zShiftr (zMul (signed x) (signed y)) zwordsize)
private def mulhu (x y : int64) : int64 := repr (zShiftr (zMul (unsigned x) (unsigned y)) zwordsize)
private def mods (x y : int64) : int64 := sub x (mul (divs x y) y)
private def modu (x y : int64) : int64 := sub x (mul (divu x y) y)
private def cmp (c : comparison) (x y : int64) : Bool := cmpWord c (eq x y) (lt x y) (lt y x)
private def cmpu (c : comparison) (x y : int64) : Bool := cmpWord c (eq x y) (ltu x y) (ltu y x)
end Int64

namespace Ptrofs
private abbrev add := CompCert4Lean.Lib.Integers.Ptrofs.add
private abbrev sub := CompCert4Lean.Lib.Integers.Ptrofs.sub
private abbrev unsigned := CompCert4Lean.Lib.Integers.Ptrofs.unsigned
private abbrev of_int := CompCert4Lean.Lib.Integers.Ptrofs.of_int
private abbrev of_int64 := CompCert4Lean.Lib.Integers.Ptrofs.of_int64
private abbrev eq := CompCert4Lean.Lib.Integers.Ptrofs.eq
private abbrev ltu := CompCert4Lean.Lib.Integers.Ptrofs.ltu
private def cmpu (c : comparison) (x y : ptrofs) : Bool := cmpWord c (eq x y) (ltu x y) (ltu y x)
end Ptrofs

namespace Float
private abbrev neg := CompCert4Lean.Lib.Floats.Float.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float.cmp
private abbrev to_int := CompCert4Lean.Lib.Floats.Float.to_int
private abbrev to_long := CompCert4Lean.Lib.Floats.Float.to_long
private abbrev of_int := CompCert4Lean.Lib.Floats.Float.of_int
private abbrev of_long := CompCert4Lean.Lib.Floats.Float.of_long
private abbrev to_single := CompCert4Lean.Lib.Floats.Float.to_single
private abbrev of_single := CompCert4Lean.Lib.Floats.Float.of_single
end Float

namespace Float32
private abbrev neg := CompCert4Lean.Lib.Floats.Float32.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float32.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float32.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float32.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float32.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float32.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float32.cmp
private abbrev to_int := CompCert4Lean.Lib.Floats.Float32.to_int
private abbrev to_long := CompCert4Lean.Lib.Floats.Float32.to_long
private abbrev of_int := CompCert4Lean.Lib.Floats.Float32.of_int
private abbrev of_long := CompCert4Lean.Lib.Floats.Float32.of_long
end Float32

/-! ## Blocks, conditions, and abstract pointers -/

inductive block_class : Type where
  | BCinvalid
  | BCglob (id : ident)
  | BCstack
  | BCother
deriving DecidableEq

export block_class (BCinvalid BCglob BCstack BCother)

def block_class_eq (x y : block_class) : Sumbool (x = y) (x ≠ y) := by
  exact if h : x = y then .left h else .right h

structure block_classification : Type where
  bc_img : block → block_class
  bc_stack : ∀ b1 b2, bc_img b1 = BCstack → bc_img b2 = BCstack → b1 = b2
  bc_glob : ∀ b1 b2 id, bc_img b1 = BCglob id → bc_img b2 = BCglob id → b1 = b2

export block_classification (bc_img bc_stack bc_glob)

instance : CoeFun block_classification (fun _ => block → block_class) :=
  ⟨block_classification.bc_img⟩

def bc_below (bc : block_classification) (bound : block) : Prop :=
  ∀ b, bc b ≠ BCinvalid → Plt b bound

inductive abool : Type where
  | Bnone
  | Just (b : Bool)
  | Maybe (b : Bool)
  | Btop
deriving DecidableEq

export abool (Bnone Just Maybe Btop)

inductive cmatch : Option Bool → abool → Prop where
  | noneCase : cmatch none Bnone
  | justCase (b) : cmatch (some b) (Just b)
  | maybeNone (b) : cmatch none (Maybe b)
  | maybeSome (b) : cmatch (some b) (Maybe b)
  | topCase (ob) : cmatch ob Btop

def cnot : abool → abool
  | Just b => Just (!b)
  | Maybe b => Maybe (!b)
  | x => x

inductive aptr : Type where
  | Pbot
  | Gl (id : ident) (ofs : ptrofs)
  | Glo (id : ident)
  | Glob
  | Stk (ofs : ptrofs)
  | Stack
  | Nonstack
  | Ptop
deriving DecidableEq

export aptr (Pbot Gl Glo Glob Stk Stack Nonstack Ptop)

def eq_aptr (p1 p2 : aptr) : Sumbool (p1 = p2) (p1 ≠ p2) :=
  if h : p1 = p2 then .left h else .right h

inductive pmatch (bc : block_classification) (b : block) (ofs : ptrofs) : aptr → Prop where
  | gl (id) : bc b = BCglob id → pmatch bc b ofs (Gl id ofs)
  | glo (id) : bc b = BCglob id → pmatch bc b ofs (Glo id)
  | glob (id) : bc b = BCglob id → pmatch bc b ofs Glob
  | stk : bc b = BCstack → pmatch bc b ofs (Stk ofs)
  | stack : bc b = BCstack → pmatch bc b ofs Stack
  | nonstack : bc b ≠ BCstack → bc b ≠ BCinvalid → pmatch bc b ofs Nonstack
  | top : bc b ≠ BCinvalid → pmatch bc b ofs Ptop

inductive pge : aptr → aptr → Prop where
  | pge_top (p) : pge Ptop p
  | bot (p) : pge p Pbot
  | pge_refl (p) : pge p p
  | gloGl (id ofs) : pge (Glo id) (Gl id ofs)
  | globGl (id ofs) : pge Glob (Gl id ofs)
  | globGlo (id) : pge Glob (Glo id)
  | nsGl (id ofs) : pge Nonstack (Gl id ofs)
  | nsGlo (id) : pge Nonstack (Glo id)
  | nsGlob : pge Nonstack Glob
  | stackStk (ofs) : pge Stack (Stk ofs)

def plub (p q : aptr) : aptr :=
  match p, q with
  | Pbot, _ => q
  | _, Pbot => p
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if id1 = id2 then if ofs1 = ofs2 then p else Glo id1 else Glob
  | Gl id1 _, Glo id2 => if id1 = id2 then q else Glob
  | Glo id1, Gl id2 _ => if id1 = id2 then p else Glob
  | Glo id1, Glo id2 => if id1 = id2 then p else Glob
  | Gl _ _, Glob | Glo _, Glob | Glob, Glob => Glob
  | Glob, Gl _ _ | Glob, Glo _ => Glob
  | Gl _ _, Nonstack | Glo _, Nonstack | Glob, Nonstack | Nonstack, Nonstack => Nonstack
  | Nonstack, Gl _ _ | Nonstack, Glo _ | Nonstack, Glob => Nonstack
  | Stk ofs1, Stk ofs2 => if ofs1 = ofs2 then p else Stack
  | Stk _, Stack | Stack, Stack | Stack, Stk _ => Stack
  | _, _ => Ptop

def pincl (p q : aptr) : Bool :=
  match p, q with
  | Pbot, _ => true
  | Gl id1 ofs1, Gl id2 ofs2 => decide (id1 = id2) && decide (ofs1 = ofs2)
  | Gl id1 _, Glo id2 => decide (id1 = id2)
  | Glo id1, Glo id2 => decide (id1 = id2)
  | Gl _ _, Glob | Glo _, Glob | Glob, Glob => true
  | Gl _ _, Nonstack | Glo _, Nonstack | Glob, Nonstack | Nonstack, Nonstack => true
  | Stk ofs1, Stk ofs2 => decide (ofs1 = ofs2)
  | Stk _, Stack | Stack, Stack => true
  | _, Ptop => true
  | _, _ => false

def padd : aptr → ptrofs → aptr
  | Gl id ofs, n => Gl id (Ptrofs.add ofs n)
  | Stk ofs, n => Stk (Ptrofs.add ofs n)
  | p, _ => p

def psub : aptr → ptrofs → aptr
  | Gl id ofs, n => Gl id (Ptrofs.sub ofs n)
  | Stk ofs, n => Stk (Ptrofs.sub ofs n)
  | p, _ => p

def poffset : aptr → aptr
  | Gl id _ => Glo id
  | Stk _ => Stack
  | p => p

def cmp_different_blocks (cfg : CompilerConfig) (c : comparison) : abool :=
  match c with
  | .Ceq => Maybe false
  | .Cne => Maybe true
  | _ => if strict cfg then Bnone else Btop

def pcmp (cfg : CompilerConfig) (c : comparison) (p1 p2 : aptr) : abool :=
  match p1, p2 with
  | Pbot, _ | _, Pbot => Bnone
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if id1 = id2 then Maybe (Ptrofs.cmpu c ofs1 ofs2) else Btop
  | Stk ofs1, Stk ofs2 => Maybe (Ptrofs.cmpu c ofs1 ofs2)
  | Gl _ _, Stk _ | Gl _ _, Stack | Glo _, Stk _ | Glo _, Stack
  | Glob, Stk _ | Glob, Stack | Nonstack, Stk _ | Nonstack, Stack =>
      cmp_different_blocks cfg c
  | Stk _, Gl _ _ | Stack, Gl _ _ | Stk _, Glo _ | Stack, Glo _
  | Stk _, Glob | Stack, Glob | Stk _, Nonstack | Stack, Nonstack =>
      cmp_different_blocks cfg c
  | _, _ => Btop

/-! ## Abstract values -/

inductive aval : Type where
  | Vbot
  | I (n : int)
  | IU (n : int)
  | Uns (p : aptr) (n : Z)
  | Sgn (p : aptr) (n : Z)
  | L (n : int64)
  | F (f : float)
  | FS (f : float32)
  | Num (p : aptr)
  | Ptr (p : aptr)
  | Ifptr (p : aptr)
deriving DecidableEq

export aval (Vbot I IU Uns Sgn L F FS Num Ptr Ifptr)

def eq_aval (v1 v2 : aval) : Sumbool (v1 = v2) (v1 ≠ v2) :=
  if h : v1 = v2 then .left h else .right h

def Vtop : aval := Ifptr Ptop

def is_uns (n : Z) (i : int) : Prop :=
  ∀ m, zLe z0 m ∧ zLt m Int.zwordsize → zLe n m → Int.testbit i m = false

def is_sgn (n : Z) (i : int) : Prop :=
  ∀ m, zLe z0 m ∧ zLt m Int.zwordsize → zLe (zSub n z1) m →
    Int.testbit i m = Int.testbit i (zSub Int.zwordsize z1)

inductive vmatch (bc : block_classification) : val → aval → Prop where
  | vmatch_i (i) : vmatch bc (Vint i) (I i)
  | vmatch_iu (i) : vmatch bc (Vint i) (IU i)
  | iuUndef (i) : vmatch bc Vundef (IU i)
  | uns (p i n) : zLe z0 n → is_uns n i → vmatch bc (Vint i) (Uns p n)
  | vmatch_Uns_undef (p n) : vmatch bc Vundef (Uns p n)
  | sgn (p i n) : zLt z0 n → is_sgn n i → vmatch bc (Vint i) (Sgn p n)
  | sgnUndef (p n) : vmatch bc Vundef (Sgn p n)
  | long (i) : vmatch bc (Vlong i) (L i)
  | float (f) : vmatch bc (Vfloat f) (F f)
  | single (f) : vmatch bc (Vsingle f) (FS f)
  | numUndef (p) : vmatch bc Vundef (Num p)
  | numInt (i p) : vmatch bc (Vint i) (Num p)
  | numLong (i p) : vmatch bc (Vlong i) (Num p)
  | numFloat (f p) : vmatch bc (Vfloat f) (Num p)
  | numSingle (f p) : vmatch bc (Vsingle f) (Num p)
  | ptr (b ofs p) : pmatch bc b ofs p → vmatch bc (Vptr b ofs) (Ptr p)
  | ptrUndef (p) : vmatch bc Vundef (Ptr p)
  | ifptrUndef (p) : vmatch bc Vundef (Ifptr p)
  | ifptrInt (i p) : vmatch bc (Vint i) (Ifptr p)
  | ifptrLong (i p) : vmatch bc (Vlong i) (Ifptr p)
  | ifptrFloat (f p) : vmatch bc (Vfloat f) (Ifptr p)
  | ifptrSingle (f p) : vmatch bc (Vsingle f) (Ifptr p)
  | ifptrPtr (b ofs p) : pmatch bc b ofs p → vmatch bc (Vptr b ofs) (Ifptr p)

def usize (i : int) : Z := Int.size i

def ssize (i : int) : Z :=
  zAdd (Int.size (if Int.lt i Int.zero then Int.not i else i)) z1

def urange : aval → Z
  | I n | IU n => usize n
  | Uns _ n => n
  | _ => Int.zwordsize

def srange : aval → Z
  | I n | IU n => ssize n
  | Uns _ n => zAdd n z1
  | Sgn _ n => n
  | _ => Int.zwordsize

def provenance : aval → aptr
  | Ptr p | Ifptr p => poffset p
  | Uns p _ | Sgn p _ | Num p => p
  | _ => Pbot

def ntop : aval := Num Pbot
def ntop1 (x : aval) : aval := Num (provenance x)
def ntop2 (x y : aval) : aval := Num (plub (provenance x) (provenance y))

def int_provenance (cfg : CompilerConfig) (i : int) : aptr :=
  if strict cfg || Int.eq i Int.zero then Pbot else Nonstack

def long_provenance (cfg : CompilerConfig) (i : int64) : aptr :=
  if strict cfg || Int64.eq i Int64.zero then Pbot else Nonstack

def uns (p : aptr) (n : Z) : aval :=
  if zle n z0 then IU Int.zero
  else if zle n z1 then Uns p z1
  else if zle n (zOfNat 7) then Uns p (zOfNat 7)
  else if zle n (zOfNat 8) then Uns p (zOfNat 8)
  else if zle n (zOfNat 15) then Uns p (zOfNat 15)
  else if zle n (zOfNat 16) then Uns p (zOfNat 16)
  else Num p

def sgn (p : aptr) (n : Z) : aval :=
  if zle n (zOfNat 8) then Sgn p (zOfNat 8)
  else if zle n (zOfNat 16) then Sgn p (zOfNat 16)
  else Num p

inductive vge : aval → aval → Prop where
  | bot (v) : vge v Vbot
  | int (i) : vge (I i) (I i)
  | long (i) : vge (L i) (L i)
  | float (f) : vge (F f) (F f)
  | single (f) : vge (FS f) (FS f)
  | iu (i) : vge (IU i) (IU i)
  | iuInt (i) : vge (IU i) (I i)
  | unsInt (p n i) : zLe z0 n → is_uns n i → vge (Uns p n) (I i)
  | vge_uns_iu (p n i) : zLe z0 n → is_uns n i → vge (Uns p n) (IU i)
  | vge_uns_uns (p1 n1 p2 n2) : zLe n2 n1 → pge p1 p2 → vge (Uns p1 n1) (Uns p2 n2)
  | sgnInt (p n i) : zLt z0 n → is_sgn n i → vge (Sgn p n) (I i)
  | sgnIU (p n i) : zLt z0 n → is_sgn n i → vge (Sgn p n) (IU i)
  | sgnSgn (p1 n1 p2 n2) : zLe n2 n1 → pge p1 p2 → vge (Sgn p1 n1) (Sgn p2 n2)
  | sgnUns (p1 n1 p2 n2) : zLt n2 n1 → pge p1 p2 → vge (Sgn p1 n1) (Uns p2 n2)
  | numInt (p i) : vge (Num p) (I i)
  | numLong (p i) : vge (Num p) (L i)
  | numFloat (p f) : vge (Num p) (F f)
  | numSingle (p f) : vge (Num p) (FS f)
  | numIU (p i) : vge (Num p) (IU i)
  | numUns (p q n) : pge p q → vge (Num p) (Uns q n)
  | numSgn (p q n) : pge p q → vge (Num p) (Sgn q n)
  | numNum (p q) : pge p q → vge (Num p) (Num q)
  | ptrPtr (p q) : pge p q → vge (Ptr p) (Ptr q)
  | ifptrPtr (p q) : pge p q → vge (Ifptr p) (Ptr q)
  | ifptrIfptr (p q) : pge p q → vge (Ifptr p) (Ifptr q)
  | ifptrInt (p i) : vge (Ifptr p) (I i)
  | ifptrLong (p i) : vge (Ifptr p) (L i)
  | ifptrFloat (p f) : vge (Ifptr p) (F f)
  | ifptrSingle (p f) : vge (Ifptr p) (FS f)
  | ifptrIU (p i) : vge (Ifptr p) (IU i)
  | ifptrUns (p q n) : pge p q → vge (Ifptr p) (Uns q n)
  | ifptrSgn (p q n) : pge p q → vge (Ifptr p) (Sgn q n)
  | ifptrNum (p q) : pge p q → vge (Ifptr p) (Num q)

def uns1 (p : aptr) (n : Z) : aval :=
  if zle n z1 then Uns p z1
  else if zle n (zOfNat 7) then Uns p (zOfNat 7)
  else if zle n (zOfNat 8) then Uns p (zOfNat 8)
  else if zle n (zOfNat 15) then Uns p (zOfNat 15)
  else if zle n (zOfNat 16) then Uns p (zOfNat 16)
  else Num p

def vlub_int (cstr : int → aval) (i1 i2 : int) : aval :=
  if Int.eq i1 i2 then cstr i1
  else if Int.lt i1 Int.zero || Int.lt i2 Int.zero then
    sgn Pbot (zMax (ssize i1) (ssize i2))
  else uns1 Pbot (zMax (usize i1) (usize i2))

def vlub (cfg : CompilerConfig) (v w : aval) : aval :=
  match v, w with
  | Vbot, _ => w
  | _, Vbot => v
  | I i1, I i2 => vlub_int I i1 i2
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => vlub_int IU i1 i2
  | I i, Uns p n | IU i, Uns p n | Uns p n, I i | Uns p n, IU i =>
      if Int.lt i Int.zero then sgn p (zMax (ssize i) (zAdd n z1))
      else uns1 p (zMax (usize i) n)
  | I i, Sgn p n | IU i, Sgn p n | Sgn p n, I i | Sgn p n, IU i =>
      sgn p (zMax (ssize i) n)
  | I _, Num p | IU _, Num p | Num p, I _ | Num p, IU _ => Num p
  | I i, Ptr p | I i, Ifptr p | IU i, Ptr p | IU i, Ifptr p
  | Ptr p, I i | Ifptr p, I i | Ptr p, IU i | Ifptr p, IU i =>
      Ifptr (plub p (int_provenance cfg i))
  | I _, L _ | I _, F _ | I _, FS _ | IU _, L _ | IU _, F _ | IU _, FS _
  | L _, I _ | F _, I _ | FS _, I _ | L _, IU _ | F _, IU _ | FS _, IU _ => ntop
  | Uns p1 n1, Uns p2 n2 => Uns (plub p1 p2) (zMax n1 n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zMax (zAdd n1 z1) n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (plub p1 p2) (zMax n1 (zAdd n2 z1))
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zMax n1 n2)
  | Uns p1 _, Num p2 | Sgn p1 _, Num p2 | Num p1, Uns p2 _ | Num p1, Sgn p2 _ =>
      Num (plub p1 p2)
  | Uns p1 _, Ptr p2 | Uns p1 _, Ifptr p2 | Sgn p1 _, Ptr p2 | Sgn p1 _, Ifptr p2
  | Ptr p1, Uns p2 _ | Ifptr p1, Uns p2 _ | Ptr p1, Sgn p2 _ | Ifptr p1, Sgn p2 _ =>
      Ifptr (plub p1 p2)
  | Uns p _, L _ | Uns p _, F _ | Uns p _, FS _ | Sgn p _, L _ | Sgn p _, F _ | Sgn p _, FS _
  | L _, Uns p _ | F _, Uns p _ | FS _, Uns p _ | L _, Sgn p _ | F _, Sgn p _ | FS _, Sgn p _ => Num p
  | L i1, L i2 => if Int64.eq i1 i2 then v else ntop
  | L _, Num p | Num p, L _ => Num p
  | L i, Ptr p | L i, Ifptr p | Ptr p, L i | Ifptr p, L i =>
      Ifptr (plub p (long_provenance cfg i))
  | L _, F _ | L _, FS _ | F _, L _ | FS _, L _ => ntop
  | F f1, F f2 => if f1 = f2 then v else ntop
  | F _, Num p | Num p, F _ => Num p
  | F _, Ptr p | F _, Ifptr p | Ptr p, F _ | Ifptr p, F _ => Ifptr p
  | F _, FS _ | FS _, F _ => ntop
  | FS f1, FS f2 => if f1 = f2 then v else ntop
  | FS _, Num p | Num p, FS _ => Num p
  | FS _, Ptr p | FS _, Ifptr p | Ptr p, FS _ | Ifptr p, FS _ => Ifptr p
  | Num p1, Num p2 => Num (plub p1 p2)
  | Num p1, Ptr p2 | Num p1, Ifptr p2 | Ptr p1, Num p2 | Ifptr p1, Num p2 =>
      Ifptr (plub p1 p2)
  | Ptr p1, Ptr p2 => Ptr (plub p1 p2)
  | Ptr p1, Ifptr p2 | Ifptr p1, Ptr p2 | Ifptr p1, Ifptr p2 => Ifptr (plub p1 p2)

def aptr_of_aval (cfg : CompilerConfig) : aval → aptr
  | Ptr p | Ifptr p => p
  | Num p | Uns p _ | Sgn p _ => if strict cfg then Pbot else p
  | I i => int_provenance cfg i
  | L i => long_provenance cfg i
  | _ => Pbot

def vplub (v : aval) (p : aptr) : aptr :=
  match v with
  | Ptr q | Ifptr q => plub q p
  | _ => p

def vpincl (v : aval) (p : aptr) : Bool :=
  match v with
  | Ptr q | Ifptr q | Num q | Uns q _ | Sgn q _ => pincl q p
  | _ => true

def vincl (v w : aval) : Bool :=
  match v, w with
  | Vbot, _ => true
  | I i, I j | I i, IU j | IU i, IU j => decide (i = j)
  | I i, Uns _ n | IU i, Uns _ n => decide (Int.zero_ext n i = i) && zle z0 n
  | I i, Sgn _ n | IU i, Sgn _ n =>
      decide (CompCert4Lean.Lib.Integers.Int.sign_ext n i = i) && zlt z0 n
  | Uns p n, Uns q m => zle n m && pincl p q
  | Uns p n, Sgn q m => zlt n m && pincl p q
  | Sgn p n, Sgn q m => zle n m && pincl p q
  | L i, L j => decide (i = j)
  | F i, F j => decide (i = j)
  | FS i, FS j => decide (i = j)
  | I _, Num _ | IU _, Num _ | L _, Num _ | F _, Num _ | FS _, Num _
  | I _, Ifptr _ | IU _, Ifptr _ | L _, Ifptr _ | F _, Ifptr _ | FS _, Ifptr _ => true
  | Uns p _, Num q | Sgn p _, Num q | Num p, Num q => pincl p q
  | Ptr p, Ptr q => pincl p q
  | Ptr p, Ifptr q | Ifptr p, Ifptr q | Num p, Ifptr q | Uns p _, Ifptr q | Sgn p _, Ifptr q => pincl p q
  | _, _ => false

def genv_match (bc : block_classification)
    (ge : CompCert4Lean.Backend.RTL.genv) : Prop :=
  (∀ id b, Genv.find_symbol ge id = some b ↔ bc b = BCglob id) ∧
  (∀ b, Plt b ge.genv_next → bc b ≠ BCinvalid ∧ bc b ≠ BCstack)

/-! ## Arithmetic and conversions -/

def unop_long (sem : int64 → int64) : aval → aval
  | L n => L (sem n)
  | x => ntop1 x

def binop_long (sem : int64 → int64 → int64) : aval → aval → aval
  | L n, L m => L (sem n m)
  | x, y => ntop2 x y

def unop_float (sem : float → float) : aval → aval
  | F n => F (sem n)
  | x => ntop1 x

def binop_float (sem : float → float → float) : aval → aval → aval
  | F n, F m => F (sem n m)
  | x, y => ntop2 x y

def unop_single (sem : float32 → float32) : aval → aval
  | FS n => FS (sem n)
  | x => ntop1 x

def binop_single (sem : float32 → float32 → float32) : aval → aval → aval
  | FS n, FS m => FS (sem n m)
  | x, y => ntop2 x y

def shl (v w : aval) : aval :=
  match w with
  | I amount => if Int.ltu amount Int.iwordsize then
      match v with
      | I i => I (Int.shl i amount)
      | IU i => IU (Int.shl i amount)
      | Uns p n => uns p (zAdd n (Int.unsigned amount))
      | Sgn p n => sgn p (zAdd n (Int.unsigned amount))
      | _ => ntop1 v
    else ntop1 v
  | _ => ntop1 v

def shru (v w : aval) : aval :=
  match w with
  | I amount => if Int.ltu amount Int.iwordsize then
      match v with
      | I i => I (Int.shru i amount)
      | IU i => IU (Int.shru i amount)
      | Uns p n => uns p (zSub n (Int.unsigned amount))
      | _ => uns (provenance v) (zSub Int.zwordsize (Int.unsigned amount))
    else ntop1 v
  | _ => ntop1 v

def shr (v w : aval) : aval :=
  match w with
  | I amount => if Int.ltu amount Int.iwordsize then
      match v with
      | I i => I (Int.shr i amount)
      | IU i => IU (Int.shr i amount)
      | Uns p n => sgn p (zSub (zAdd n z1) (Int.unsigned amount))
      | Sgn p n => sgn p (zSub n (Int.unsigned amount))
      | _ => sgn (provenance v) (zSub Int.zwordsize (Int.unsigned amount))
    else ntop1 v
  | _ => ntop1 v

def «and» (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.and i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.and i1 i2)
  | I i, Uns p n | IU i, Uns p n | Uns p n, I i | Uns p n, IU i => uns p (zMin n (usize i))
  | I i, x | IU i, x | x, I i | x, IU i => uns (provenance x) (usize i)
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (zMin n1 n2)
  | Uns p n, _ => uns (plub p (provenance w)) n
  | _, Uns p n => uns (plub (provenance v) p) n
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zMax n1 n2)
  | _, _ => ntop2 v w

def «or» (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.or i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.or i1 i2)
  | I i, Uns p n | IU i, Uns p n | Uns p n, I i | Uns p n, IU i => uns p (zMax n (usize i))
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (zMax n1 n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zMax n1 n2)
  | _, _ => ntop2 v w

def xor (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.xor i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.xor i1 i2)
  | I i, Uns p n | IU i, Uns p n | Uns p n, I i | Uns p n, IU i => uns p (zMax n (usize i))
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (zMax n1 n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zMax n1 n2)
  | _, _ => ntop2 v w

def notint : aval → aval
  | I i => I (Int.not i)
  | IU i => IU (Int.not i)
  | Uns p n => sgn p (zAdd n z1)
  | Sgn p n => Sgn p n
  | x => ntop1 x

def ror (x y : aval) : aval :=
  match y, x with
  | I j, I i => I (Int.ror i j)
  | I j, IU i => IU (Int.ror i j)
  | _, _ => ntop1 x

def neg : aval → aval
  | I i => I (Int.neg i)
  | IU i => IU (Int.neg i)
  | Sgn p n => sgn p (zAdd n z1)
  | x => ntop1 x

def add (x y : aval) : aval :=
  match x, y with
  | I i, I j => I (Int.add i j)
  | I i, IU j | IU i, I j | IU i, IU j => IU (Int.add i j)
  | I i, Uns p n | IU i, Uns p n | Uns p n, I i | Uns p n, IU i =>
      uns p (zAdd (zMax n (usize i)) z1)
  | I i, Sgn p n | IU i, Sgn p n | Sgn p n, I i | Sgn p n, IU i =>
      sgn p (zAdd (zMax n (ssize i)) z1)
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (zAdd (zMax n1 n2) z1)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zAdd (zMax n1 n2) z1)
  | Uns p1 n1, Sgn p2 n2 | Sgn p2 n2, Uns p1 n1 =>
      sgn (plub p1 p2) (zAdd (zMax (zAdd n1 z1) n2) z1)
  | Ptr p, I i | Ptr p, IU i | I i, Ptr p | IU i, Ptr p =>
      Ptr (if CompCert4Lean.X86_64.Archi.ptr64 then poffset p else padd p (Ptrofs.of_int i))
  | Ptr p, _ | _, Ptr p => Ptr (poffset p)
  | Ifptr p, I i | Ifptr p, IU i | I i, Ifptr p | IU i, Ifptr p =>
      Ifptr (if CompCert4Lean.X86_64.Archi.ptr64 then poffset p else padd p (Ptrofs.of_int i))
  | Ifptr p, Ifptr q => Ifptr (plub (poffset p) (poffset q))
  | Ifptr p, _ | _, Ifptr p => Ifptr (poffset p)
  | _, _ => ntop2 x y

def sub (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.sub i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.sub i1 i2)
  | I i, Uns p n | IU i, Uns p n | Uns p n, I i | Uns p n, IU i =>
      sgn p (zAdd (zMax (zAdd n z1) (ssize i)) z1)
  | I i, Sgn p n | IU i, Sgn p n | Sgn p n, I i | Sgn p n, IU i =>
      sgn p (zAdd (zMax n (ssize i)) z1)
  | Uns p1 n1, Uns p2 n2 => sgn (plub p1 p2) (zAdd (zMax n1 n2) z1)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zAdd (zMax n1 n2) z1)
  | Uns p1 n1, Sgn p2 n2 | Sgn p2 n2, Uns p1 n1 =>
      sgn (plub p1 p2) (zAdd (zMax (zAdd n1 z1) n2) z1)
  | Ptr p, I i | Ptr p, IU i =>
      if CompCert4Lean.X86_64.Archi.ptr64 then Ifptr (poffset p) else Ptr (psub p (Ptrofs.of_int i))
  | Ptr p, _ => Ifptr (poffset p)
  | Ifptr p, I i | Ifptr p, IU i =>
      if CompCert4Lean.X86_64.Archi.ptr64 then Ifptr (plub (poffset p) (provenance w))
      else Ifptr (psub p (Ptrofs.of_int i))
  | Ifptr p, _ => Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w

def mul_base (v w : aval) : aval :=
  match v, w with
  | Uns p n1, I n2 | Uns p n1, IU n2 | I n2, Uns p n1 | IU n2, Uns p n1 =>
      uns p (zAdd n1 (usize n2))
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (zAdd n1 n2)
  | Sgn p n1, I n2 | Sgn p n1, IU n2 | I n2, Sgn p n1 | IU n2, Sgn p n1 =>
      sgn p (zAdd n1 (ssize n2))
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zAdd n1 n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (zAdd (zAdd n1 z1) n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (plub p1 p2) (zAdd n1 (zAdd n2 z1))
  | _, _ => ntop2 v w

def mul (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.mul i1 i2)
  | IU i1, I i2 | I i1, IU i2 | IU i1, IU i2 => IU (Int.mul i1 i2)
  | _, _ => if vincl v (Uns Ptop z0) || vincl w (Uns Ptop z0) then IU Int.zero else mul_base v w

def mulhs_base (v w : aval) : aval :=
  sgn (plub (provenance v) (provenance w)) (zSub (zAdd (srange v) (srange w)) Int.zwordsize)

def mulhs (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.mulhs i1 i2)
  | IU i1, I i2 | I i1, IU i2 | IU i1, IU i2 => IU (Int.mulhs i1 i2)
  | _, _ => if vincl v (Uns Ptop z0) || vincl w (Uns Ptop z0) then IU Int.zero else mulhs_base v w

def mulhu_base (v w : aval) : aval :=
  uns (plub (provenance v) (provenance w)) (zSub (zAdd (urange v) (urange w)) Int.zwordsize)

def mulhu (v w : aval) : aval :=
  match v, w with
  | I i1, I i2 => I (Int.mulhu i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.mulhu i1 i2)
  | _, _ => if vincl v (Uns Ptop z1) || vincl w (Uns Ptop z1) then IU Int.zero else mulhu_base v w

def divs (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | I i2, I i1 | I i2, IU i1 | IU i2, I i1 | IU i2, IU i1 =>
      if Int.eq i2 Int.zero || (Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone) then
        if strict cfg then Vbot else ntop
      else I (Int.divs i1 i2)
  | I i2, _ | IU i2, _ =>
      if Int.eq i2 Int.zero then if strict cfg then Vbot else ntop
      else sgn (provenance v) (zSub (zAdd (srange v) z1) (zLog2 (zAbs (Int.signed i2))))
  | _, _ => ntop2 v w

def divu (cfg : CompilerConfig) (v w : aval) : aval :=
  match w with
  | I i2 | IU i2 => if Int.eq i2 Int.zero then
      if strict cfg then Vbot else ntop
    else match v with
      | I i1 | IU i1 => I (Int.divu i1 i2)
      | _ => uns (provenance v) (zSub (urange v) (zLog2 (Int.unsigned i2)))
  | _ => ntop2 v w

def mods (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | I i2, I i1 | I i2, IU i1 | IU i2, I i1 | IU i2, IU i1 =>
      if Int.eq i2 Int.zero || (Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone) then
        if strict cfg then Vbot else ntop
      else I (Int.mods i1 i2)
  | I i2, _ | IU i2, _ => sgn (provenance v) (ssize i2)
  | _, _ => ntop2 v w

def modu (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | I i2, I i1 | I i2, IU i1 | IU i2, I i1 | IU i2, IU i1 =>
      if Int.eq i2 Int.zero then if strict cfg then Vbot else ntop else I (Int.modu i1 i2)
  | I i2, _ | IU i2, _ => uns (provenance v) (usize i2)
  | _, _ => ntop2 v w

def shrx (v w : aval) : aval :=
  match v, w with
  | I i, I j => if Int.ltu j (Int.repr (zOfNat 31)) then I (Int.shrx i j) else ntop
  | _, _ => ntop1 v

def shift_long (sem : int64 → int → int64) (v w : aval) : aval :=
  match w with
  | I amount => if Int.ltu amount Int64.iwordsize' then
      match v with | L i => L (sem i amount) | _ => ntop1 v
    else ntop1 v
  | _ => ntop1 v

def shll := shift_long Int64.shl'
def shrl := shift_long Int64.shr'
def shrlu := shift_long Int64.shru'
def andl := binop_long Int64.and
def orl := binop_long Int64.or
def xorl := binop_long Int64.xor
def notl := unop_long Int64.not

def rotate_long (sem : int64 → int64 → int64) (v w : aval) : aval :=
  match v, w with
  | L i, I amount => L (sem i (Int64.repr (Int.unsigned amount)))
  | _, _ => ntop1 v

def rorl := rotate_long Int64.ror
def negl := unop_long Int64.neg

def addl (x y : aval) : aval :=
  match x, y with
  | L i, L j => L (Int64.add i j)
  | Ptr p, L i | L i, Ptr p => Ptr (if CompCert4Lean.X86_64.Archi.ptr64 then padd p (Ptrofs.of_int64 i) else poffset p)
  | Ptr p, _ | _, Ptr p => Ptr (poffset p)
  | Ifptr p, L i | L i, Ifptr p => Ifptr (if CompCert4Lean.X86_64.Archi.ptr64 then padd p (Ptrofs.of_int64 i) else poffset p)
  | Ifptr p, Ifptr q => Ifptr (plub (poffset p) (poffset q))
  | Ifptr p, _ | _, Ifptr p => Ifptr (poffset p)
  | _, _ => ntop2 x y

def subl (v w : aval) : aval :=
  match v, w with
  | L i1, L i2 => L (Int64.sub i1 i2)
  | Ptr p, L i => if CompCert4Lean.X86_64.Archi.ptr64 then Ptr (psub p (Ptrofs.of_int64 i)) else Ifptr (poffset p)
  | Ptr p, _ => Ifptr (poffset p)
  | Ifptr p, L i => if CompCert4Lean.X86_64.Archi.ptr64 then Ifptr (psub p (Ptrofs.of_int64 i)) else Ifptr (plub (poffset p) (provenance w))
  | Ifptr p, _ => Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w

def mull := binop_long Int64.mul
def mullhs := binop_long Int64.mulhs
def mullhu := binop_long Int64.mulhu

def divls (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | L i2, L i1 => if Int64.eq i2 Int64.zero || (Int64.eq i1 (Int64.repr Int64.min_signed) && Int64.eq i2 Int64.mone) then
      if strict cfg then Vbot else ntop else L (Int64.divs i1 i2)
  | _, _ => ntop2 v w

def divlu (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | L i2, L i1 => if Int64.eq i2 Int64.zero then if strict cfg then Vbot else ntop else L (Int64.divu i1 i2)
  | _, _ => ntop2 v w

def modls (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | L i2, L i1 => if Int64.eq i2 Int64.zero || (Int64.eq i1 (Int64.repr Int64.min_signed) && Int64.eq i2 Int64.mone) then
      if strict cfg then Vbot else ntop else L (Int64.mods i1 i2)
  | _, _ => ntop2 v w

def modlu (cfg : CompilerConfig) (v w : aval) : aval :=
  match w, v with
  | L i2, L i1 => if Int64.eq i2 Int64.zero then if strict cfg then Vbot else ntop else L (Int64.modu i1 i2)
  | _, _ => ntop2 v w

def shrxl (v w : aval) : aval :=
  match v, w with
  | L i, I j => if Int.ltu j (Int.repr (zOfNat 63)) then L (Int64.shrx' i j) else ntop
  | _, _ => ntop1 v

def negf := unop_float Float.neg
def absf := unop_float Float.abs
def addf := binop_float Float.add
def subf := binop_float Float.sub
def mulf := binop_float Float.mul
def divf := binop_float Float.div
def negfs := unop_single Float32.neg
def absfs := unop_single Float32.abs
def addfs := binop_single Float32.add
def subfs := binop_single Float32.sub
def mulfs := binop_single Float32.mul
def divfs := binop_single Float32.div

def zero_ext (nbits : Z) : aval → aval
  | I i => I (Int.zero_ext nbits i)
  | IU i => IU (Int.zero_ext nbits i)
  | Uns p n => uns p (zMin n nbits)
  | v => uns (provenance v) nbits

def sign_ext (nbits : Z) (v : aval) : aval :=
  if zle nbits z0 then Uns (provenance v) z0 else
  match v with
  | I i => I (CompCert4Lean.Lib.Integers.Int.sign_ext nbits i)
  | IU i => IU (CompCert4Lean.Lib.Integers.Int.sign_ext nbits i)
  | Uns p n => if zlt n nbits then Uns p n else sgn p nbits
  | Sgn p n => sgn p (zMin n nbits)
  | _ => sgn (provenance v) nbits

def longofint : aval → aval
  | I i => L (Int64.repr (Int.signed i))
  | v => ntop1 v

def longofintu : aval → aval
  | I i => L (Int64.repr (Int.unsigned i))
  | v => ntop1 v

def singleoffloat : aval → aval
  | F f => FS (Float.to_single f)
  | v => ntop1 v

def floatofsingle : aval → aval
  | FS f => F (Float.of_single f)
  | v => ntop1 v

private def failedConversion (cfg : CompilerConfig) : aval := if strict cfg then Vbot else ntop

def intoffloat (cfg : CompilerConfig) : aval → aval
  | F f => match Float.to_int f with | some i => I i | none => failedConversion cfg
  | v => ntop1 v

def floatofint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] :
    aval → aval
  | I i => F (Float.of_int (certificate := binary64_certificate) i)
  | v => ntop1 v

def intofsingle (cfg : CompilerConfig) : aval → aval
  | FS f => match Float32.to_int f with | some i => I i | none => failedConversion cfg
  | v => ntop1 v

def singleofint
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    aval → aval
  | I i => FS (Float32.of_int (certificate := binary32_certificate) i)
  | v => ntop1 v

def longoffloat (cfg : CompilerConfig) : aval → aval
  | F f => match Float.to_long f with | some i => L i | none => failedConversion cfg
  | v => ntop1 v

def floatoflong
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] :
    aval → aval
  | L i => F (Float.of_long (certificate := binary64_certificate) i)
  | v => ntop1 v

def longofsingle (cfg : CompilerConfig) : aval → aval
  | FS f => match Float32.to_long f with | some i => L i | none => failedConversion cfg
  | v => ntop1 v

def singleoflong
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    aval → aval
  | L i => FS (Float32.of_long (certificate := binary32_certificate) i)
  | v => ntop1 v

def longofwords (x y : aval) : aval :=
  match y, x with | I j, I i => L (Int64.ofwords i j) | _, _ => ntop2 x y

def loword : aval → aval
  | L i => I (Int64.loword i)
  | v => ntop1 v

def hiword : aval → aval
  | L i => I (Int64.hiword i)
  | v => ntop1 v

def cmp_intv (c : comparison) (i : Z × Z) (n : Z) : abool :=
  let (lo, hi) := i
  match c with
  | .Ceq => if zlt n lo || zlt hi n then Maybe false else Btop
  | .Cne => if zlt n lo || zlt hi n then Maybe true else Btop
  | .Clt => if zlt hi n then Maybe true else if zle n lo then Maybe false else Btop
  | .Cle => if zle hi n then Maybe true else if zlt n lo then Maybe false else Btop
  | .Cgt => if zlt n lo then Maybe true else if zle hi n then Maybe false else Btop
  | .Cge => if zle n lo then Maybe true else if zlt hi n then Maybe false else Btop

def uintv : aval → Z × Z
  | I n => (Int.unsigned n, Int.unsigned n)
  | Uns _ n => if zlt n Int.zwordsize then (z0, zSub (two_p n) z1) else (z0, Int.max_unsigned)
  | _ => (z0, Int.max_unsigned)

def sintv : aval → Z × Z
  | I n => (Int.signed n, Int.signed n)
  | Uns _ n => if zlt n Int.zwordsize then (z0, zSub (two_p n) z1) else (Int.min_signed, Int.max_signed)
  | Sgn _ n => if zlt n Int.zwordsize then
      let x := two_p (zSub n z1); (zOpp x, zSub x z1)
    else (Int.min_signed, Int.max_signed)
  | _ => (Int.min_signed, Int.max_signed)

def cmpu_bool (cfg : CompilerConfig) (c : comparison) (v w : aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmpu c i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => Maybe (Int.cmpu c i1 i2)
  | Ptr _, I i => if Int.eq i Int.zero then cmp_different_blocks cfg c else Btop
  | I i, Ptr _ => if Int.eq i Int.zero then cmp_different_blocks cfg c else Btop
  | Ptr p1, Ptr p2 => pcmp cfg c p1 p2
  | _, I i | _, IU i => cmp_intv c (uintv v) (Int.unsigned i)
  | I i, _ | IU i, _ => cmp_intv (swap_comparison c) (uintv w) (Int.unsigned i)
  | _, _ => Btop

def cmp_bool (c : comparison) (v w : aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmp c i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => Maybe (Int.cmp c i1 i2)
  | _, I i | _, IU i => cmp_intv c (sintv v) (Int.signed i)
  | I i, _ | IU i, _ => cmp_intv (swap_comparison c) (sintv w) (Int.signed i)
  | _, _ => Btop

def cmplu_bool (cfg : CompilerConfig) (c : comparison) (v w : aval) : abool :=
  match v, w with
  | L i1, L i2 => Just (Int64.cmpu c i1 i2)
  | Ptr _, L i => if Int64.eq i Int64.zero then cmp_different_blocks cfg c else Btop
  | L i, Ptr _ => if Int64.eq i Int64.zero then cmp_different_blocks cfg c else Btop
  | Ptr p1, Ptr p2 => pcmp cfg c p1 p2
  | _, _ => Btop

def cmpl_bool (c : comparison) : aval → aval → abool
  | L i1, L i2 => Just (Int64.cmp c i1 i2)
  | _, _ => Btop

def cmpf_bool (c : comparison) : aval → aval → abool
  | F f1, F f2 => Just (Float.cmp c f1 f2)
  | _, _ => Btop

def cmpfs_bool (c : comparison) : aval → aval → abool
  | FS f1, FS f2 => Just (Float32.cmp c f1 f2)
  | _, _ => Btop

def maskzero (x : aval) (mask : int) : abool :=
  match x with
  | I i => Just (Int.eq (Int.and i mask) Int.zero)
  | IU i => Maybe (Int.eq (Int.and i mask) Int.zero)
  | Uns _ n => if Int.eq (Int.zero_ext n mask) Int.zero then Maybe true else Btop
  | _ => Btop

def of_optbool : abool → aval
  | Just b => I (if b then Int.one else Int.zero)
  | Maybe b => IU (if b then Int.one else Int.zero)
  | _ => Uns Pbot z1

def resolve_branch : abool → Option Bool
  | Just b | Maybe b => some b
  | _ => none

def add_undef : aval → aval
  | Vbot => ntop
  | I i => IU i
  | L _ | F _ | FS _ => ntop
  | x => x

def vnormalize_type (ty : typ) (x : aval) : aval :=
  match x, ty with
  | Vbot, _ => Vbot
  | I _, .Tint | L _, .Tlong | F _, .Tfloat | FS _, .Tsingle => x
  | I _, .Tany32 | FS _, .Tany32 => x
  | I _, .Tany64 | L _, .Tany64 | F _, .Tany64 | FS _, .Tany64 => x
  | _, _ => add_undef x

def select (cfg : CompilerConfig) (ab : abool) (x y : aval) (ty : typ) : aval :=
  match ab with
  | Bnone => ntop
  | Just b => vnormalize_type ty (if b then x else y)
  | Maybe b => add_undef (vnormalize_type ty (if b then x else y))
  | Btop => add_undef (vnormalize_type ty (vlub cfg x y))

def vnormalize (chunk : memory_chunk) (v : aval) : aval :=
  match chunk, v with
  | _, Vbot => Vbot
  | .Mbool, I i => let j := Int.zero_ext (zOfNat 8) i; if Int.eq j Int.zero || Int.eq j Int.one then I j else Uns Pbot z1
  | .Mbool, IU i => let j := Int.zero_ext (zOfNat 8) i; if Int.eq j Int.zero || Int.eq j Int.one then IU j else Uns Pbot z1
  | .Mbool, _ => Uns (provenance v) z1
  | .Mint8signed, I i =>
      I (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 8) i)
  | .Mint8signed, IU i =>
      IU (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 8) i)
  | .Mint8signed, Uns _ n => if zlt n (zOfNat 8) then Uns (provenance v) n else Sgn (provenance v) (zOfNat 8)
  | .Mint8signed, Sgn _ n => Sgn (provenance v) (zMin n (zOfNat 8))
  | .Mint8signed, _ => Sgn (provenance v) (zOfNat 8)
  | .Mint8unsigned, I i => I (Int.zero_ext (zOfNat 8) i)
  | .Mint8unsigned, IU i => IU (Int.zero_ext (zOfNat 8) i)
  | .Mint8unsigned, Uns _ n => Uns (provenance v) (zMin n (zOfNat 8))
  | .Mint8unsigned, _ => Uns (provenance v) (zOfNat 8)
  | .Mint16signed, I i =>
      I (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i)
  | .Mint16signed, IU i =>
      IU (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i)
  | .Mint16signed, Uns _ n => if zlt n (zOfNat 16) then Uns (provenance v) n else Sgn (provenance v) (zOfNat 16)
  | .Mint16signed, Sgn _ n => Sgn (provenance v) (zMin n (zOfNat 16))
  | .Mint16signed, _ => Sgn (provenance v) (zOfNat 16)
  | .Mint16unsigned, I i => I (Int.zero_ext (zOfNat 16) i)
  | .Mint16unsigned, IU i => IU (Int.zero_ext (zOfNat 16) i)
  | .Mint16unsigned, Uns _ n => Uns (provenance v) (zMin n (zOfNat 16))
  | .Mint16unsigned, _ => Uns (provenance v) (zOfNat 16)
  | .Mint32, I _ | .Mint32, IU _ | .Mint32, Uns _ _ | .Mint32, Sgn _ _ | .Mint32, Num _ => v
  | .Mint32, Ptr _ | .Mint32, Ifptr _ => if CompCert4Lean.X86_64.Archi.ptr64 then Num (provenance v) else v
  | .Mint32, _ => Num (provenance v)
  | .Mint64, L _ => v
  | .Mint64, Ptr _ | .Mint64, Ifptr _ => if CompCert4Lean.X86_64.Archi.ptr64 then v else Num (provenance v)
  | .Mint64, _ => Num (provenance v)
  | .Mfloat32, FS _ => v
  | .Mfloat32, _ => Num (provenance v)
  | .Mfloat64, F _ => v
  | .Mfloat64, _ => Num (provenance v)
  | .Many32, I _ | .Many32, IU _ | .Many32, Uns _ _ | .Many32, Sgn _ _ | .Many32, FS _ => v
  | .Many32, Ptr _ | .Many32, Ifptr _ => if CompCert4Lean.X86_64.Archi.ptr64 then Num (provenance v) else v
  | .Many32, _ => Num (provenance v)
  | .Many64, _ => v

def val_of_aval : aval → val
  | I n => Vint n
  | L n => Vlong n
  | F f => Vfloat f
  | FS f => Vsingle f
  | _ => Vundef

def aval_of_val : val → Option aval
  | Vint n => some (I n)
  | Vlong n => some (L n)
  | Vfloat f => some (F f)
  | Vsingle f => some (FS f)
  | _ => none

def of_xtype : xtype → aptr → aval
  | .Xbool, p => Uns p z1
  | .Xint8signed, p => Sgn p (zOfNat 8)
  | .Xint8unsigned, p => Uns p (zOfNat 8)
  | .Xint16signed, p => Sgn p (zOfNat 16)
  | .Xint16unsigned, p => Uns p (zOfNat 16)
  | _, p => Ifptr p

/-! ## Abstract memory -/

inductive acontent : Type where
  | ACval (chunk : memory_chunk) (av : aval)
deriving DecidableEq

export acontent (ACval)

def eq_acontent (c1 c2 : acontent) : Sumbool (c1 = c2) (c1 ≠ c2) :=
  if h : c1 = c2 then .left h else .right h

structure ablock : Type where
  ab_contents : ZTree.t acontent
  ab_summary : aptr

def ablock_init (p : aptr) : ablock :=
  { ab_contents := ZTree.empty acontent, ab_summary := p }

def chunk_compat : memory_chunk → memory_chunk → Bool
  | .Mint8signed, .Mint8signed | .Mint8signed, .Mint8unsigned
  | .Mint8unsigned, .Mint8signed | .Mint8unsigned, .Mint8unsigned
  | .Mint16signed, .Mint16signed | .Mint16signed, .Mint16unsigned
  | .Mint16unsigned, .Mint16signed | .Mint16unsigned, .Mint16unsigned
  | .Mint32, .Mint32 | .Mfloat32, .Mfloat32 | .Mint64, .Mint64
  | .Mfloat64, .Mfloat64 | .Many32, .Many32 | .Many64, .Many64 => true
  | _, _ => false

def ablock_load (chunk : memory_chunk) (ab : ablock) (i : Z) : aval :=
  match ZTree.get i ab.ab_contents with
  | none => vnormalize chunk (Ifptr ab.ab_summary)
  | some (ACval chunk' av) =>
      if chunk_compat chunk chunk' then vnormalize chunk av
      else vnormalize chunk (Ifptr ab.ab_summary)

def ablock_load_anywhere (chunk : memory_chunk) (ab : ablock) : aval :=
  vnormalize chunk (Ifptr ab.ab_summary)

private def inval_after_measure (lo hi : Z) : Nat :=
  if zle lo hi then Int.toNat (intOfZ hi - intOfZ lo) + 1 else 0

private theorem zle_true_prop_for_inval {x y : Z} (h : zle x y = true) : zLe x y := by
  unfold zle at h
  cases hd : CompCert4Lean.Lib.Coqlib.zle x y with
  | left hxy => exact hxy
  | right hxy => simp [hd, boolOfSumbool] at h

def inval_after (lo hi : Z) (c : ZTree.t acontent) : ZTree.t acontent :=
  if zle lo hi then inval_after lo (zSub hi z1) (ZTree.remove hi c) else c
termination_by inval_after_measure lo hi
decreasing_by
  dsimp [inval_after_measure]
  rename_i hrec
  by_cases hcur : zle lo hi = true
  · by_cases hnext : zle lo (zSub hi z1) = true
    · rw [if_pos hnext, if_pos hcur]
      have _hlo : intOfZ lo ≤ intOfZ hi := zle_true_prop_for_inval hcur
      have hnextlo : intOfZ lo ≤ intOfZ (zSub hi z1) :=
        zle_true_prop_for_inval hnext
      have hz1 : intOfZ z1 = 1 := by rfl
      have hsub : intOfZ (zSub hi z1) = intOfZ hi - 1 := by
        simp [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt, hz1]
      rw [hsub] at hnextlo
      rw [hsub]
      have _hcur_nonneg : 0 ≤ intOfZ hi - intOfZ lo := by omega
      have _hnext_nonneg : 0 ≤ intOfZ hi - 1 - intOfZ lo := by omega
      have hpos : 0 < intOfZ hi - intOfZ lo := by omega
      apply Nat.succ_lt_succ_iff.mpr
      apply (Int.toNat_lt_toNat hpos).mpr
      omega
    · rw [if_neg hnext, if_pos hcur]
      omega
  · rw [if_neg hcur]
    exact False.elim (hcur hrec)

def inval_if (hi lo : Z) (c : ZTree.t acontent) : ZTree.t acontent :=
  match ZTree.get lo c with
  | none => c
  | some (ACval chunk _) =>
      if zle (zAdd lo (size_chunk chunk)) hi then c else ZTree.remove lo c

private def inval_before_measure (hi lo : Z) : Nat :=
  if zlt lo hi then Int.toNat (intOfZ hi - intOfZ lo) + 1 else 0

private theorem zlt_true_prop_for_inval {x y : Z} (h : zlt x y = true) : zLt x y := by
  unfold zlt at h
  cases hd : CompCert4Lean.Lib.Coqlib.zlt x y with
  | left hxy => exact hxy
  | right hxy => simp [hd, boolOfSumbool] at h

def inval_before (hi lo : Z) (c : ZTree.t acontent) : ZTree.t acontent :=
  if zlt lo hi then inval_before hi (zAdd lo z1) (inval_if hi lo c) else c
termination_by inval_before_measure hi lo
decreasing_by
  dsimp [inval_before_measure]
  rename_i hrec
  by_cases hcur : zlt lo hi = true
  · by_cases hnext : zlt (zAdd lo z1) hi = true
    · rw [if_pos hnext, if_pos hcur]
      have _hlt : intOfZ lo < intOfZ hi := zlt_true_prop_for_inval hcur
      have hnextlt : intOfZ (zAdd lo z1) < intOfZ hi :=
        zlt_true_prop_for_inval hnext
      have hz1 : intOfZ z1 = 1 := by rfl
      have hadd : intOfZ (zAdd lo z1) = intOfZ lo + 1 := by
        simp [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt, hz1]
      rw [hadd] at hnextlt
      rw [hadd]
      have _hcur_nonneg : 0 ≤ intOfZ hi - intOfZ lo := by omega
      have _hnext_nonneg : 0 ≤ intOfZ hi - (intOfZ lo + 1) := by omega
      have hpos : 0 < intOfZ hi - intOfZ lo := by omega
      apply Nat.succ_lt_succ_iff.mpr
      apply (Int.toNat_lt_toNat hpos).mpr
      omega
    · rw [if_neg hnext, if_pos hcur]
      omega
  · rw [if_neg hcur]
    exact False.elim (hcur hrec)

def ablock_store (chunk : memory_chunk) (ab : ablock) (i : Z) (av : aval) : ablock :=
  { ab_contents :=
      ZTree.set i (ACval chunk av)
        (inval_before i (zSub i (zOfNat 7))
          (inval_after (zAdd i z1) (zSub (zAdd i (size_chunk chunk)) z1) ab.ab_contents))
    ab_summary := vplub av ab.ab_summary }

def ablock_store_anywhere (_chunk : memory_chunk) (ab : ablock) (av : aval) : ablock :=
  ablock_init (vplub av ab.ab_summary)

def ablock_loadbytes (ab : ablock) : aptr := ab.ab_summary

def ablock_storebytes (ab : ablock) (p : aptr) (ofs sz : Z) : ablock :=
  { ab_contents :=
      inval_before ofs (zSub ofs (zOfNat 7))
        (inval_after ofs (zSub (zAdd ofs sz) z1) ab.ab_contents)
    ab_summary := plub p ab.ab_summary }

def ablock_storebytes_anywhere (ab : ablock) (p : aptr) : ablock :=
  ablock_init (plub p ab.ab_summary)

def smatch (bc : block_classification) (m : mem) (b : block) (p : aptr) : Prop :=
  (∀ chunk ofs v, Mem.load chunk m b ofs = some v → vmatch bc v (Ifptr p)) ∧
  (∀ ofs b' ofs' q i,
    Mem.loadbytes m b ofs z1 = some [Fragment (Vptr b' ofs') q i] →
    pmatch bc b' ofs' p)

def bmatch (bc : block_classification) (m : mem) (b : block) (ab : ablock) : Prop :=
  smatch bc m b ab.ab_summary ∧
  ∀ chunk ofs v, Mem.load chunk m b ofs = some v →
    vmatch bc v (ablock_load chunk ab ofs)

def combine_acontents (cfg : CompilerConfig)
    (c1 c2 : Option acontent) : Option acontent :=
  match c1, c2 with
  | some (ACval chunk1 v1), some (ACval chunk2 v2) =>
      if chunk1 = chunk2 then some (ACval chunk1 (vlub cfg v1 v2)) else none
  | _, _ => none

def blub (cfg : CompilerConfig) (ab1 ab2 : ablock) : ablock :=
  { ab_contents := ZTree.combine (combine_acontents cfg) ab1.ab_contents ab2.ab_contents
    ab_summary := plub ab1.ab_summary ab2.ab_summary }

def bbeq (ab1 ab2 : ablock) : Bool :=
  proj_sumbool (eq_aptr ab1.ab_summary ab2.ab_summary) &&
    ZTree.beq (fun c1 c2 => proj_sumbool (eq_acontent c1 c2))
      ab1.ab_contents ab2.ab_contents

def romem : Type := PTree.t ablock

def romatch (bc : block_classification) (m : mem) (rm : romem) : Prop :=
  ∀ b id ab,
    bc b = BCglob id →
    PTree.get id rm = some ab →
    pge Glob ab.ab_summary ∧
      bmatch bc m b ab ∧
      ∀ ofs, ¬ Mem.perm m b ofs .Max .Writable

structure amem : Type where
  am_stack : ablock
  am_glob : PTree.t ablock
  am_nonstack : aptr
  am_top : aptr

structure mmatch (bc : block_classification) (m : mem) (am : amem) : Prop where
  mmatch_stack : ∀ b, bc b = BCstack → bmatch bc m b am.am_stack
  mmatch_glob : ∀ id ab b,
    bc b = BCglob id → PTree.get id am.am_glob = some ab → bmatch bc m b ab
  mmatch_nonstack : ∀ b,
    bc b ≠ BCstack → bc b ≠ BCinvalid → smatch bc m b am.am_nonstack
  mmatch_top : ∀ b, bc b ≠ BCinvalid → smatch bc m b am.am_top
  mmatch_below : bc_below bc m.nextblock

def minit (p : aptr) : amem :=
  { am_stack := ablock_init p
    am_glob := PTree.empty ablock
    am_nonstack := p
    am_top := p }

def mtop : amem := minit Ptop

def load (cfg : CompilerConfig) (chunk : memory_chunk)
    (rm : romem) (m : amem) (p : aptr) : aval :=
  match p with
  | Pbot => if strict cfg then Vbot else Vtop
  | Gl id ofs =>
      match PTree.get id rm with
      | some ab => ablock_load chunk ab (Ptrofs.unsigned ofs)
      | none =>
          match PTree.get id m.am_glob with
          | some ab => ablock_load chunk ab (Ptrofs.unsigned ofs)
          | none => vnormalize chunk (Ifptr m.am_nonstack)
  | Glo id =>
      match PTree.get id rm with
      | some ab => ablock_load_anywhere chunk ab
      | none =>
          match PTree.get id m.am_glob with
          | some ab => ablock_load_anywhere chunk ab
          | none => vnormalize chunk (Ifptr m.am_nonstack)
  | Stk ofs => ablock_load chunk m.am_stack (Ptrofs.unsigned ofs)
  | Stack => ablock_load_anywhere chunk m.am_stack
  | Glob | Nonstack => vnormalize chunk (Ifptr m.am_nonstack)
  | Ptop => vnormalize chunk (Ifptr m.am_top)

def loadv (cfg : CompilerConfig) (chunk : memory_chunk)
    (rm : romem) (m : amem) (addr : aval) : aval :=
  load cfg chunk rm m (aptr_of_aval cfg addr)

def store (chunk : memory_chunk) (m : amem) (p : aptr) (av : aval) : amem :=
  { am_stack :=
      match p with
      | Stk ofs => ablock_store chunk m.am_stack (Ptrofs.unsigned ofs) av
      | Stack | Ptop => ablock_store_anywhere chunk m.am_stack av
      | _ => m.am_stack
    am_glob :=
      match p with
      | Gl id ofs =>
          let ab := (PTree.get id m.am_glob).getD (ablock_init m.am_nonstack)
          PTree.set id (ablock_store chunk ab (Ptrofs.unsigned ofs) av) m.am_glob
      | Glo id =>
          let ab := (PTree.get id m.am_glob).getD (ablock_init m.am_nonstack)
          PTree.set id (ablock_store_anywhere chunk ab av) m.am_glob
      | Glob | Nonstack | Ptop => PTree.empty ablock
      | _ => m.am_glob
    am_nonstack :=
      match p with
      | Gl _ _ | Glo _ | Glob | Nonstack | Ptop => vplub av m.am_nonstack
      | _ => m.am_nonstack
    am_top := vplub av m.am_top }

def storev (cfg : CompilerConfig) (chunk : memory_chunk)
    (m : amem) (addr v : aval) : amem :=
  store chunk m (aptr_of_aval cfg addr) v

def loadbytes (cfg : CompilerConfig) (m : amem) (rm : romem) (p : aptr) : aptr :=
  match p with
  | Pbot => if strict cfg then Pbot else Ptop
  | Gl id _ | Glo id =>
      match PTree.get id rm with
      | some ab => ablock_loadbytes ab
      | none =>
          match PTree.get id m.am_glob with
          | some ab => ablock_loadbytes ab
          | none => m.am_nonstack
  | Stk _ | Stack => ablock_loadbytes m.am_stack
  | Glob | Nonstack => m.am_nonstack
  | Ptop => m.am_top

def storebytes (m : amem) (dst : aptr) (sz : Z) (p : aptr) : amem :=
  { am_stack :=
      match dst with
      | Stk ofs => ablock_storebytes m.am_stack p (Ptrofs.unsigned ofs) sz
      | Stack | Ptop => ablock_storebytes_anywhere m.am_stack p
      | _ => m.am_stack
    am_glob :=
      match dst with
      | Gl id ofs =>
          let ab := (PTree.get id m.am_glob).getD (ablock_init m.am_nonstack)
          PTree.set id (ablock_storebytes ab p (Ptrofs.unsigned ofs) sz) m.am_glob
      | Glo id =>
          let ab := (PTree.get id m.am_glob).getD (ablock_init m.am_nonstack)
          PTree.set id (ablock_storebytes_anywhere ab p) m.am_glob
      | Glob | Nonstack | Ptop => PTree.empty ablock
      | _ => m.am_glob
    am_nonstack :=
      match dst with
      | Gl _ _ | Glo _ | Glob | Nonstack | Ptop => plub p m.am_nonstack
      | _ => m.am_nonstack
    am_top := plub p m.am_top }

def combine_ablock (cfg : CompilerConfig)
    (ob1 ob2 : Option ablock) : Option ablock :=
  match ob1, ob2 with
  | some b1, some b2 => some (blub cfg b1 b2)
  | _, _ => none

def mlub (cfg : CompilerConfig) (m1 m2 : amem) : amem :=
  { am_stack := blub cfg m1.am_stack m2.am_stack
    am_glob := PTree.combine (combine_ablock cfg) m1.am_glob m2.am_glob
    am_nonstack := plub m1.am_nonstack m2.am_nonstack
    am_top := plub m1.am_top m2.am_top }

def mbeq (m1 m2 : amem) : Bool :=
  proj_sumbool (eq_aptr m1.am_top m2.am_top) &&
    proj_sumbool (eq_aptr m1.am_nonstack m2.am_nonstack) &&
    bbeq m1.am_stack m2.am_stack &&
    ZTree.beq bbeq m1.am_glob m2.am_glob

def pdisjoint (p1 : aptr) (sz1 : Z) (p2 : aptr) (sz2 : Z) : Bool :=
  match p1, p2 with
  | Pbot, _ | _, Pbot => true
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if id1 = id2 then
        zle (zAdd (Ptrofs.unsigned ofs1) sz1) (Ptrofs.unsigned ofs2) ||
          zle (zAdd (Ptrofs.unsigned ofs2) sz2) (Ptrofs.unsigned ofs1)
      else true
  | Gl id1 _, Glo id2 | Glo id1, Gl id2 _ | Glo id1, Glo id2 => !(peqBool id1 id2)
  | Stk ofs1, Stk ofs2 =>
      zle (zAdd (Ptrofs.unsigned ofs1) sz1) (Ptrofs.unsigned ofs2) ||
        zle (zAdd (Ptrofs.unsigned ofs2) sz2) (Ptrofs.unsigned ofs1)
  | Gl _ _, Stk _ | Gl _ _, Stack | Glo _, Stk _ | Glo _, Stack
  | Glob, Stk _ | Glob, Stack | Nonstack, Stk _ | Nonstack, Stack
  | Stk _, Gl _ _ | Stack, Gl _ _ | Stk _, Glo _ | Stack, Glo _
  | Stk _, Glob | Stack, Glob | Stk _, Nonstack | Stack, Nonstack => true
  | _, _ => false

def bc_incr (bc1 bc2 : block_classification) : Prop :=
  ∀ b, bc1 b ≠ BCinvalid → bc2 b = bc1 b

def inj_of_bc (bc : block_classification) : meminj :=
  fun b => match bc b with | BCinvalid => none | _ => some (b, z0)

/-! ## Generated finite-map surface and abstract environments -/

namespace AE

inductive t' : Type where
  | Bot
  | Top_except (values : PTree.t aval)

abbrev t : Type := t'

def get (p : positive) : t → aval
  | .Bot => Vbot
  | .Top_except values => (PTree.get p values).getD Vtop

def set (p : positive) (v : aval) : t → t
  | .Bot => .Bot
  | .Top_except values =>
      if v = Vbot then .Bot
      else if v = Vtop then .Top_except (PTree.remove p values)
      else .Top_except (PTree.set p v values)

def eq (x y : t) : Prop := ∀ p, get p x = get p y

def beq : t → t → Bool
  | .Bot, .Bot => true
  | .Top_except x, .Top_except y => PTree.beq (fun v1 v2 => proj_sumbool (eq_aval v1 v2)) x y
  | _, _ => false

def ge (x y : t) : Prop := ∀ p, vge (get p x) (get p y)

def bot : t := .Bot
def top : t := .Top_except (PTree.empty aval)

def LM : Type := PTree.t aval

namespace LM

def combine (f : Option aval → Option aval → Option aval)
    (t1 t2 : LM) : LM :=
  PTree.combine f t1 t2

end LM

def opt_lub (cfg : CompilerConfig) (x y : aval) : Option aval :=
  let z := vlub cfg x y
  if z = Vtop then none else some z

def lub (cfg : CompilerConfig) (x y : t) : t :=
  match x, y with
  | .Bot, _ => y
  | _, .Bot => x
  | .Top_except t1, .Top_except t2 =>
      .Top_except
        (LM.combine
          (fun a b =>
            match a, b with
            | some u, some v => opt_lub cfg u v
            | _, _ => none)
          t1 t2)

end AE

def aenv : Type := AE.t

def ematch (bc : block_classification) (e : regset) (ae : aenv) : Prop :=
  ∀ r, vmatch bc (Regmap.get r e) (AE.get r ae)

def einit_regs : List reg → List xtype → aenv
  | [], _ => AE.top
  | r1 :: rs, t1 :: ts =>
      let a1 := if CompCert4Lean.X86.Conventions1.parameter_needs_normalization t1
        then Ifptr Nonstack else of_xtype t1 Nonstack
      AE.set r1 a1 (einit_regs rs ts)
  | r1 :: rs, [] => AE.set r1 (Ifptr Nonstack) (einit_regs rs [])

def eforget : List reg → aenv → aenv
  | [], ae => ae
  | r1 :: rs, ae => eforget rs (AE.set r1 Vtop ae)

namespace VA

inductive t' : Type where
  | Bot
  | State (ae : aenv) (am : amem)

abbrev t : Type := t'

def eq (x y : t) : Prop :=
  match x, y with
  | .Bot, .Bot => True
  | .State ae1 am1, .State ae2 am2 =>
      AE.eq ae1 ae2 ∧ ∀ bc m, mmatch bc m am1 ↔ mmatch bc m am2
  | _, _ => False

def beq (x y : t) : Bool :=
  match x, y with
  | .Bot, .Bot => true
  | .State ae1 am1, .State ae2 am2 => AE.beq ae1 ae2 && mbeq am1 am2
  | _, _ => false

def ge (x y : t) : Prop :=
  match x, y with
  | _, .Bot => True
  | .Bot, .State _ _ => False
  | .State ae1 am1, .State ae2 am2 =>
      AE.ge ae1 ae2 ∧ ∀ bc m, mmatch bc m am2 → mmatch bc m am1

def bot : t := .Bot

def lub (cfg : CompilerConfig) (x y : t) : t :=
  match x, y with
  | .Bot, _ => y
  | _, .Bot => x
  | .State ae1 am1, .State ae2 am2 =>
      .State (AE.lub cfg ae1 ae2) (mlub cfg am1 am2)

end VA

/-! ## Generated finite-map and record surfaces -/

namespace AE

def AE : Type := Unit
abbrev Bot : t' := .Bot

def eq_refl : Prop :=
  ∀ x, eq x x

def eq_sym : Prop :=
  ∀ x y, eq x y → eq y x

def eq_trans : Prop :=
  ∀ x y z, eq x y → eq y z → eq x z

def beq_correct : Prop :=
  ∀ x y, beq x y = true → eq x y

def ge_refl : Prop :=
  ∀ x y, eq x y → ge x y

def ge_trans : Prop :=
  ∀ x y z, ge x y → ge y z → ge x z

def get_bot : Prop :=
  ∀ p, get p bot = Vbot

def ge_bot : Prop :=
  ∀ x, ge x bot

def get_top : Prop :=
  ∀ p, get p top = Vtop

def ge_top : Prop :=
  ∀ x, ge top x

def gsspec : Prop :=
  ∀ p v x q,
    x ≠ Bot → v ≠ Vbot →
    get q (set p v x) = if q = p then v else get q x

def gcombine_top : Prop :=
  ∀ (f : Option aval → Option aval → Option aval) (t1 t2 : LM) p,
    f none none = none →
    get p (.Top_except (LM.combine f t1 t2)) =
      match f (PTree.get p t1) (PTree.get p t2) with
      | some x => x
      | none => Vtop

def ge_lub_left : Prop :=
  ∀ cfg x y, ge (lub cfg x y) x

def ge_lub_right : Prop :=
  ∀ cfg x y, ge (lub cfg x y) y

end AE

namespace VA

export t' (Bot State)

end VA

export ablock (ab_contents ab_summary)
export amem (am_glob am_nonstack am_stack am_top)
export mmatch (mmatch_stack mmatch_glob mmatch_nonstack mmatch_top mmatch_below)

export pge (pge_top pge_refl)
export vge (vge_uns_iu vge_uns_uns)
export vmatch (vmatch_Uns_undef vmatch_i vmatch_iu)

/-! ## Exact statement descriptors for deferred proofs -/

def VA.ge_transStatement : Prop :=
  ∀ x y z, VA.ge x y → VA.ge y z → VA.ge x z

def bc_below_invalidStatement : Prop :=
  ∀ b bc bound, ¬ Plt b bound → bc_below bc bound → bc b = BCinvalid

def pdisjoint_sound_strongStatement : Prop :=
  ∀ (sz1 : Z) (b1 : block) (ofs1 : ptrofs)
    (bc1 : block_classification) (p1 : aptr) (sz2 : Z) (b2 : block)
    (ofs2 : ptrofs) (bc2 : block_classification) (p2 : aptr)
    (ge : CompCert4Lean.Backend.RTL.genv) (sp : block),
    pdisjoint p1 sz1 p2 sz2 = true →
    pmatch bc1 b1 ofs1 p1 → pmatch bc2 b2 ofs2 p2 →
    genv_match bc1 ge → bc1 sp = BCstack →
    genv_match bc2 ge → bc2 sp = BCstack →
    b1 ≠ b2 ∨
      zLe (zAdd (Ptrofs.unsigned ofs1) sz1) (Ptrofs.unsigned ofs2) ∨
      zLe (zAdd (Ptrofs.unsigned ofs2) sz2) (Ptrofs.unsigned ofs1)

def genv_match_extenStatement : Prop :=
  ∀ (ge : CompCert4Lean.Backend.RTL.genv) (bc1 bc2 : block_classification),
    genv_match bc1 ge →
    (∀ b id, bc1 b = BCglob id ↔ bc2 b = BCglob id) →
    (∀ b, bc1 b = BCother → bc2 b = BCother) →
    genv_match bc2 ge

def romatch_extenStatement : Prop :=
  ∀ (bc1 bc2 : block_classification) (m : mem) (rm : romem),
    romatch bc1 m rm →
    (∀ b id, bc2 b = BCglob id ↔ bc1 b = BCglob id) →
    romatch bc2 m rm

def pmatch_incrStatement : Prop :=
  ∀ (bc1 bc2 : block_classification), bc_incr bc1 bc2 →
    ∀ b ofs p, pmatch bc1 b ofs p → pmatch bc2 b ofs p

def vmatch_incrStatement : Prop :=
  ∀ (bc1 bc2 : block_classification), bc_incr bc1 bc2 →
    ∀ v x, vmatch bc1 v x → vmatch bc2 v x

def smatch_incrStatement : Prop :=
  ∀ (bc1 bc2 : block_classification), bc_incr bc1 bc2 →
    ∀ m b p, smatch bc1 m b p → smatch bc2 m b p

def bmatch_incrStatement : Prop :=
  ∀ (bc1 bc2 : block_classification), bc_incr bc1 bc2 →
    ∀ m b ab, bmatch bc1 m b ab → bmatch bc2 m b ab

def inj_of_bc_validStatement : Prop :=
  ∀ (bc : block_classification) b, bc b ≠ BCinvalid →
    inj_of_bc bc b = some (b, z0)

def inj_of_bc_invStatement : Prop :=
  ∀ (bc : block_classification) b b' delta,
    inj_of_bc bc b = some (b', delta) →
    bc b ≠ BCinvalid ∧ b' = b ∧ delta = z0

def pmatch_injStatement : Prop :=
  ∀ bc b ofs p, pmatch bc b ofs p → inj_of_bc bc b = some (b, z0)

def vmatch_injStatement : Prop :=
  ∀ bc v x, vmatch bc v x → Val.inject (inj_of_bc bc) v v

def mmatch_injStatement : Prop :=
  ∀ bc m am, mmatch bc m am → bc_below bc m.nextblock →
    Mem.inject (inj_of_bc bc) m m

def inj_of_bc_preserves_globalsStatement : Prop :=
  ∀ (bc : block_classification) (ge : CompCert4Lean.Backend.RTL.genv),
    genv_match bc ge →
      meminj_preserves_globals CompCert4Lean.Backend.RTL.fundef Unit ge
        (inj_of_bc bc)

def pmatch_inj_topStatement : Prop :=
  ∀ bc b b' delta ofs,
    inj_of_bc bc b = some (b', delta) → pmatch bc b ofs Ptop

def vmatch_inj_topStatement : Prop :=
  ∀ bc v v', Val.inject (inj_of_bc bc) v v' → vmatch bc v Vtop

def mmatch_inj_topStatement : Prop :=
  ∀ bc m m', Mem.inject (inj_of_bc bc) m m' → mmatch bc m mtop

def eforget_geStatement : Prop :=
  ∀ rl ae, AE.ge (eforget rl ae) ae

def ematch_geStatement : Prop :=
  ∀ bc e ae1 ae2, ematch bc e ae1 → AE.ge ae2 ae1 → ematch bc e ae2

def ematch_updateStatement : Prop :=
  ∀ bc e ae v av r,
    ematch bc e ae → vmatch bc v av →
    ematch bc (Regmap.set r v e) (AE.set r av ae)

def ematch_initStatement : Prop :=
  ∀ bc rl vl tl,
    Val.has_argtype_list vl tl →
    (∀ v, v ∈ vl → vmatch bc v (Ifptr Nonstack)) →
    ematch bc (init_regs vl rl) (einit_regs rl tl)

def ematch_incrStatement : Prop :=
  ∀ bc bc' e ae, ematch bc e ae → bc_incr bc bc' → ematch bc' e ae

def pge_transStatement : Prop :=
  ∀ p q, pge p q → ∀ r, pge q r → pge p r

def pmatch_geStatement : Prop :=
  ∀ bc b ofs p q, pge p q → pmatch bc b ofs q → pmatch bc b ofs p

def pmatch_top'Statement : Prop :=
  ∀ bc b ofs p, pmatch bc b ofs p → pmatch bc b ofs Ptop

def plub_commStatement : Prop :=
  ∀ p q, plub p q = plub q p

def pge_lub_lStatement : Prop :=
  ∀ p q, pge (plub p q) p

def pge_lub_rStatement : Prop :=
  ∀ p q, pge (plub p q) q

def pmatch_lub_lStatement : Prop :=
  ∀ bc b ofs p q, pmatch bc b ofs p → pmatch bc b ofs (plub p q)

def pmatch_lub_rStatement : Prop :=
  ∀ bc b ofs p q, pmatch bc b ofs q → pmatch bc b ofs (plub p q)

def plub_leastStatement : Prop :=
  ∀ r p q, pge r p → pge r q → pge r (plub p q)

def pincl_geStatement : Prop :=
  ∀ p q, pincl p q = true → pge q p

def vmatch_ifptrStatement : Prop :=
  ∀ bc v p, (∀ b ofs, v = Vptr b ofs → pmatch bc b ofs p) → vmatch bc v (Ifptr p)

def vmatch_topStatement : Prop :=
  ∀ bc v x, vmatch bc v x → vmatch bc v Vtop

def usize_posStatement : Prop :=
  ∀ n, zLe z0 (usize n)

def ssize_posStatement : Prop :=
  ∀ n, zLt z0 (ssize n)

def is_uns_usizeStatement : Prop :=
  ∀ i, is_uns (usize i) i

def is_uns_zero_extStatement : Prop :=
  ∀ n i, is_uns n i ↔ Int.zero_ext n i = i

def is_sgn_sign_extStatement : Prop :=
  ∀ n i, zLt z0 n →
    (is_sgn n i ↔ CompCert4Lean.Lib.Integers.Int.sign_ext n i = i)

def is_zero_ext_unsStatement : Prop :=
  ∀ i n m, is_uns m i ∨ zLe n m → is_uns m (Int.zero_ext n i)

def is_sign_ext_unsStatement : Prop :=
  ∀ i n m, (zLe z0 m ∧ zLt m n) →
    is_uns m i → is_uns m (CompCert4Lean.Lib.Integers.Int.sign_ext n i)

def is_sign_ext_sgnStatement : Prop :=
  ∀ i n m, zLt z0 n → zLt z0 m →
    is_sgn m i ∨ zLe n m →
      is_sgn m (CompCert4Lean.Lib.Integers.Int.sign_ext n i)

def is_uns_1Statement : Prop :=
  ∀ n, is_uns z1 n → n = Int.zero ∨ n = Int.one

def vmatch_Uns_1Statement : Prop :=
  ∀ bc p v, vmatch bc v (Uns p z1) →
    v = Vundef ∨ v = Vint Int.zero ∨ v = Vint Int.one

def vge_transStatement : Prop :=
  ∀ x y z, vge x y → vge y z → vge x z

def vmatch_geStatement : Prop :=
  ∀ bc v x y, vge x y → vmatch bc v y → vmatch bc v x

def vlub_commStatement : Prop :=
  ∀ cfg v w, vlub cfg v w = vlub cfg w v

def vge_uns_uns'Statement : Prop :=
  ∀ p n, vge (uns1 p n) (Uns p n)

def vge_uns_i'Statement : Prop :=
  ∀ p n i, zLe z0 n → is_uns n i → vge (uns1 p n) (I i)

def vge_uns_iu'Statement : Prop :=
  ∀ p n i, zLe z0 n → is_uns n i → vge (uns1 p n) (IU i)

def vge_sgn_sgn'Statement : Prop :=
  ∀ p n, vge (sgn p n) (Sgn p n)

def vge_sgn_i'Statement : Prop :=
  ∀ p n i, zLt z0 n → is_sgn n i → vge (sgn p n) (I i)

def vge_sgn_iu'Statement : Prop :=
  ∀ p n i, zLt z0 n → is_sgn n i → vge (sgn p n) (IU i)

def vge_lub_lStatement : Prop :=
  ∀ cfg x y, vge (vlub cfg x y) x

def vge_lub_rStatement : Prop :=
  ∀ cfg x y, vge (vlub cfg x y) y

def vmatch_lub_lStatement : Prop :=
  ∀ cfg bc v x y, vmatch bc v x → vmatch bc v (vlub cfg x y)

def vmatch_lub_rStatement : Prop :=
  ∀ cfg bc v x y, vmatch bc v y → vmatch bc v (vlub cfg x y)

def match_aptr_of_avalStatement : Prop :=
  ∀ cfg bc b ofs av, vmatch bc (Vptr b ofs) av → pmatch bc b ofs (aptr_of_aval cfg av)

def vmatch_vplub_lStatement : Prop :=
  ∀ bc v x p, vmatch bc v x → vmatch bc v (Ifptr (vplub x p))

def pmatch_vplubStatement : Prop :=
  ∀ bc b ofs x p, pmatch bc b ofs p → pmatch bc b ofs (vplub x p)

def vmatch_vplub_rStatement : Prop :=
  ∀ bc v x p, vmatch bc v (Ifptr p) → vmatch bc v (Ifptr (vplub x p))

def vpincl_geStatement : Prop :=
  ∀ x p, vpincl x p = true → vge (Ifptr p) x

def vincl_geStatement : Prop :=
  ∀ v w, vincl v w = true → vge w v

def symbol_address_soundStatement : Prop :=
  ∀ (bc : block_classification) (ge : CompCert4Lean.Backend.RTL.genv) id ofs,
    genv_match bc ge →
    vmatch bc (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs))

def vmatch_ptr_glStatement : Prop :=
  ∀ (bc : block_classification) (ge : CompCert4Lean.Backend.RTL.genv) v id ofs,
    genv_match bc ge → vmatch bc v (Ptr (Gl id ofs)) →
    Val.lessdef v (Genv.symbol_address ge id ofs)

def binop_float_soundStatement : Prop :=
  ∀ bc sem v x w y,
    vmatch bc v x → vmatch bc w y →
    vmatch bc
      (match v, w with | Vfloat i, Vfloat j => Vfloat (sem i j) | _, _ => Vundef)
      (binop_float sem x y)

def of_optbool_soundStatement : Prop :=
  ∀ bc ob ab, cmatch ob ab → vmatch bc (Val.of_optbool ob) (of_optbool ab)

def resolve_branch_soundStatement : Prop :=
  ∀ b ab b', cmatch (some b) ab → resolve_branch ab = some b' → b' = b

def add_undef_soundStatement : Prop :=
  ∀ bc v x, vmatch bc v x → vmatch bc v (add_undef x)

def add_undef_undefStatement : Prop :=
  ∀ bc x, vmatch bc Vundef (add_undef x)

def vnormalize_type_soundStatement : Prop :=
  ∀ bc v x ty, vmatch bc v x →
    vmatch bc (Val.normalize v ty) (vnormalize_type ty x)

def select_soundStatement : Prop :=
  ∀ cfg bc ob v w ab x y ty,
    cmatch ob ab → vmatch bc v x → vmatch bc w y →
    vmatch bc (Val.select ob v w ty) (select cfg ab x y ty)

def vnormalize_soundStatement : Prop :=
  ∀ bc chunk v x, vmatch bc v x →
    vmatch bc (Val.load_result chunk v) (vnormalize chunk x)

def vnormalize_castStatement : Prop :=
  ∀ bc chunk m b ofs v p,
    Mem.load chunk m b ofs = some v → vmatch bc v (Ifptr p) →
    vmatch bc v (vnormalize chunk (Ifptr p))

def poffset_geStatement : Prop :=
  ∀ p, pge (poffset p) p

def poffset_monotoneStatement : Prop :=
  ∀ p q, pge p q → pge (poffset p) (poffset q)

def provenance_monotoneStatement : Prop :=
  ∀ x y, vge x y → pge (provenance x) (provenance y)

def provenance_ifptr_geStatement : Prop :=
  ∀ p q, pge p q → pge (provenance (Ifptr p)) q

def vnormalize_monotoneStatement : Prop :=
  ∀ chunk x y, vge x y → vge (vnormalize chunk x) (vnormalize chunk y)

def val_of_aval_soundStatement : Prop :=
  ∀ bc v a, vmatch bc v a → Val.lessdef (val_of_aval a) v

def list_val_of_aval_soundStatement : Prop :=
  ∀ bc vl al, list_forall2 (vmatch bc) vl al →
    Val.lessdef_list (List.map val_of_aval al) vl

def aval_of_val_soundStatement : Prop :=
  ∀ bc v a, aval_of_val v = some a → vmatch bc v a

def of_xtype_arg_soundStatement : Prop :=
  ∀ bc v x p, Val.has_argtype v x → vmatch bc v (Ifptr p) → vmatch bc v (of_xtype x p)

def loadbytes_load_extStatement : Prop :=
  ∀ b m m',
    (∀ ofs n bytes,
      Mem.loadbytes m' b ofs n = some bytes → zLe z0 n →
      Mem.loadbytes m b ofs n = some bytes) →
    ∀ chunk ofs v, Mem.load chunk m' b ofs = some v → Mem.load chunk m b ofs = some v

def smatch_extStatement : Prop :=
  ∀ bc m b p m', smatch bc m b p →
    (∀ ofs n bytes,
      Mem.loadbytes m' b ofs n = some bytes → zLe z0 n →
      Mem.loadbytes m b ofs n = some bytes) →
    smatch bc m' b p

def smatch_invStatement : Prop :=
  ∀ bc m b p m', smatch bc m b p →
    (∀ ofs n, zLe z0 n → Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) →
    smatch bc m' b p

def smatch_geStatement : Prop :=
  ∀ bc m b p q, smatch bc m b p → pge q p → smatch bc m b q

def In_loadbytesStatement : Prop :=
  ∀ m b byte n ofs bytes,
    Mem.loadbytes m b ofs n = some bytes → byte ∈ bytes →
    ∃ ofs', (zLe ofs ofs' ∧ zLt ofs' (zAdd ofs n)) ∧
      Mem.loadbytes m b ofs' z1 = some [byte]

def smatch_loadbytesStatement : Prop :=
  ∀ bc m b p b' ofs' q i n ofs bytes,
    Mem.loadbytes m b ofs n = some bytes → smatch bc m b p →
    Fragment (Vptr b' ofs') q i ∈ bytes → pmatch bc b' ofs' p

def loadbytes_provenanceStatement : Prop :=
  ∀ m b ofs' byte n ofs bytes,
    Mem.loadbytes m b ofs n = some bytes →
    Mem.loadbytes m b ofs' z1 = some [byte] →
    (zLe ofs ofs' ∧ zLt ofs' (zAdd ofs n)) → byte ∈ bytes

def storebytes_provenanceStatement : Prop :=
  ∀ m b ofs bytes m' b' ofs' b'' ofs'' q i,
    Mem.storebytes m b ofs bytes = some m' →
    Mem.loadbytes m' b' ofs' z1 = some [Fragment (Vptr b'' ofs'') q i] →
    Fragment (Vptr b'' ofs'') q i ∈ bytes ∨
      Mem.loadbytes m b' ofs' z1 = some [Fragment (Vptr b'' ofs'') q i]

def store_provenanceStatement : Prop :=
  ∀ chunk m b ofs v m' b' ofs' b'' ofs'' q i,
    Mem.store chunk m b ofs v = some m' →
    Mem.loadbytes m' b' ofs' z1 = some [Fragment (Vptr b'' ofs'') q i] →
    (v = Vptr b'' ofs'' ∧
      (chunk = .Mint32 ∨ chunk = .Many32 ∨ chunk = .Mint64 ∨ chunk = .Many64)) ∨
      Mem.loadbytes m b' ofs' z1 = some [Fragment (Vptr b'' ofs'') q i]

def smatch_storeStatement : Prop :=
  ∀ bc chunk m b ofs v m' b' p av,
    Mem.store chunk m b ofs v = some m' → smatch bc m b' p → vmatch bc v av →
    smatch bc m' b' (vplub av p)

def smatch_storebytesStatement : Prop :=
  ∀ bc m b ofs bytes m' b' p p',
    Mem.storebytes m b ofs bytes = some m' → smatch bc m b' p →
    (∀ bx ofsx q i, Fragment (Vptr bx ofsx) q i ∈ bytes → pmatch bc bx ofsx p') →
    smatch bc m' b' (plub p' p)

def bmatch_extStatement : Prop :=
  ∀ bc m b ab m', bmatch bc m b ab →
    (∀ ofs n bytes,
      Mem.loadbytes m' b ofs n = some bytes → zLe z0 n →
      Mem.loadbytes m b ofs n = some bytes) →
    bmatch bc m' b ab

def bmatch_invStatement : Prop :=
  ∀ bc m b ab m', bmatch bc m b ab →
    (∀ ofs n, zLe z0 n → Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) →
    bmatch bc m' b ab

def ablock_load_soundStatement : Prop :=
  ∀ bc chunk m b ofs v ab,
    Mem.load chunk m b ofs = some v → bmatch bc m b ab →
    vmatch bc v (ablock_load chunk ab ofs)

def ablock_load_anywhere_soundStatement : Prop :=
  ∀ bc chunk m b ofs v ab,
    Mem.load chunk m b ofs = some v → bmatch bc m b ab →
    vmatch bc v (ablock_load_anywhere chunk ab)

def ablock_init_soundStatement : Prop :=
  ∀ bc m b p, smatch bc m b p → bmatch bc m b (ablock_init p)

def ablock_store_anywhere_soundStatement : Prop :=
  ∀ bc chunk m b ofs v m' b' ab av,
    Mem.store chunk m b ofs v = some m' → bmatch bc m b' ab → vmatch bc v av →
    bmatch bc m' b' (ablock_store_anywhere chunk ab av)

def inval_after_outsideStatement : Prop :=
  ∀ i lo hi c, (zLt i lo ∨ zLt hi i) → ZTree.get i (inval_after lo hi c) = ZTree.get i c

def inval_after_contentsStatement : Prop :=
  ∀ chunk av i lo hi c,
    ZTree.get i (inval_after lo hi c) = some (ACval chunk av) →
    ZTree.get i c = some (ACval chunk av) ∧ (zLt i lo ∨ zLt hi i)

def inval_before_outsideStatement : Prop :=
  ∀ i hi lo c, (zLt i lo ∨ zLe hi i) → ZTree.get i (inval_before hi lo c) = ZTree.get i c

def inval_before_contents_1Statement : Prop :=
  ∀ i chunk av lo hi c,
    (zLe lo i ∧ zLt i hi) →
    ZTree.get i (inval_before hi lo c) = some (ACval chunk av) →
    ZTree.get i c = some (ACval chunk av) ∧ zLe (zAdd i (size_chunk chunk)) hi

def max_size_chunkStatement : Prop :=
  ∀ chunk, zLe (size_chunk chunk) (zOfNat 8)

def inval_before_contentsStatement : Prop :=
  ∀ i c chunk' av' j,
    ZTree.get j (inval_before i (zSub i (zOfNat 7)) c) = some (ACval chunk' av') →
    ZTree.get j c = some (ACval chunk' av') ∧
      (zLe (zAdd j (size_chunk chunk')) i ∨ zLe i j)

def ablock_store_contentsStatement : Prop :=
  ∀ chunk ab i av j chunk' av',
    ZTree.get j (ablock_store chunk ab i av).ab_contents = some (ACval chunk' av') →
    (i = j ∧ chunk' = chunk ∧ av' = av) ∨
      (ZTree.get j ab.ab_contents = some (ACval chunk' av') ∧
        (zLe (zAdd j (size_chunk chunk')) i ∨
          zLe (zAdd i (size_chunk chunk)) j))

def chunk_compat_trueStatement : Prop :=
  ∀ c c', chunk_compat c c' = true →
    size_chunk c = size_chunk c' ∧
      zLe (align_chunk c) (align_chunk c') ∧ type_of_chunk c = type_of_chunk c'

def ablock_store_soundStatement : Prop :=
  ∀ bc chunk m b ofs v m' ab av,
    Mem.store chunk m b ofs v = some m' → bmatch bc m b ab → vmatch bc v av →
    bmatch bc m' b (ablock_store chunk ab ofs av)

def ablock_loadbytes_soundStatement : Prop :=
  ∀ bc m b ab b' ofs' q i n ofs bytes,
    Mem.loadbytes m b ofs n = some bytes → bmatch bc m b ab →
    Fragment (Vptr b' ofs') q i ∈ bytes → pmatch bc b' ofs' (ablock_loadbytes ab)

def ablock_storebytes_anywhere_soundStatement : Prop :=
  ∀ bc m b ofs bytes p m' b' ab,
    Mem.storebytes m b ofs bytes = some m' →
    (∀ bx ofsx q i, Fragment (Vptr bx ofsx) q i ∈ bytes → pmatch bc bx ofsx p) →
    bmatch bc m b' ab → bmatch bc m' b' (ablock_storebytes_anywhere ab p)

def ablock_storebytes_contentsStatement : Prop :=
  ∀ ab p i sz j chunk' av',
    ZTree.get j (ablock_storebytes ab p i sz).ab_contents = some (ACval chunk' av') →
    ZTree.get j ab.ab_contents = some (ACval chunk' av') ∧
      (zLe (zAdd j (size_chunk chunk')) i ∨ zLe (zAdd i (zMax sz z0)) j)

def ablock_storebytes_soundStatement : Prop :=
  ∀ bc m b ofs bytes m' p ab sz,
    Mem.storebytes m b ofs bytes = some m' → bytes.length = zToNat sz →
    (∀ bx ofsx q i, Fragment (Vptr bx ofsx) q i ∈ bytes → pmatch bc bx ofsx p) →
    bmatch bc m b ab → bmatch bc m' b (ablock_storebytes ab p ofs sz)

def smatch_lub_lStatement : Prop :=
  ∀ bc m b p q, smatch bc m b p → smatch bc m b (plub p q)

def smatch_lub_rStatement : Prop :=
  ∀ bc m b p q, smatch bc m b q → smatch bc m b (plub p q)

def bmatch_lub_lStatement : Prop :=
  ∀ cfg bc m b x y, bmatch bc m b x → bmatch bc m b (blub cfg x y)

def bmatch_lub_rStatement : Prop :=
  ∀ cfg bc m b x y, bmatch bc m b y → bmatch bc m b (blub cfg x y)

def romatch_storeStatement : Prop :=
  ∀ bc chunk m b ofs v m' rm,
    Mem.store chunk m b ofs v = some m' → romatch bc m rm → romatch bc m' rm

def romatch_storebytesStatement : Prop :=
  ∀ bc m b ofs bytes m' rm,
    Mem.storebytes m b ofs bytes = some m' → romatch bc m rm → romatch bc m' rm

def romatch_extStatement : Prop :=
  ∀ bc m rm m', romatch bc m rm →
    (∀ b id ofs n bytes, bc b = BCglob id →
      Mem.loadbytes m' b ofs n = some bytes → Mem.loadbytes m b ofs n = some bytes) →
    (∀ b id ofs p, bc b = BCglob id →
      Mem.perm m' b ofs .Max p → Mem.perm m b ofs .Max p) →
    romatch bc m' rm

def romatch_freeStatement : Prop :=
  ∀ bc m b lo hi m' rm,
    Mem.free m b lo hi = some m' → romatch bc m rm → romatch bc m' rm

def romatch_allocStatement : Prop :=
  ∀ bc m b lo hi m' rm,
    Mem.alloc m lo hi = (m', b) → bc_below bc m.nextblock →
    romatch bc m rm → romatch bc m' rm

def load_soundStatement : Prop :=
  ∀ cfg bc chunk m b ofs v rm am p,
    Mem.load chunk m b (Ptrofs.unsigned ofs) = some v → romatch bc m rm →
    mmatch bc m am → pmatch bc b ofs p → vmatch bc v (load cfg chunk rm am p)

def loadv_soundStatement : Prop :=
  ∀ cfg bc chunk m addr v rm am aaddr,
    Mem.loadv chunk m addr = some v → romatch bc m rm → mmatch bc m am →
    vmatch bc addr aaddr → vmatch bc v (loadv cfg chunk rm am aaddr)

def store_soundStatement : Prop :=
  ∀ bc chunk m b ofs v m' am p av,
    Mem.store chunk m b (Ptrofs.unsigned ofs) v = some m' → mmatch bc m am →
    pmatch bc b ofs p → vmatch bc v av → mmatch bc m' (store chunk am p av)

def storev_soundStatement : Prop :=
  ∀ cfg bc chunk m addr v m' am aaddr av,
    Mem.storev chunk m addr v = some m' → mmatch bc m am →
    vmatch bc addr aaddr → vmatch bc v av →
    mmatch bc m' (storev cfg chunk am aaddr av)

def loadbytes_soundStatement : Prop :=
  ∀ cfg bc m b ofs sz bytes am rm p,
    Mem.loadbytes m b (Ptrofs.unsigned ofs) sz = some bytes → romatch bc m rm →
    mmatch bc m am → pmatch bc b ofs p →
    ∀ b' ofs' q i, Fragment (Vptr b' ofs') q i ∈ bytes →
      pmatch bc b' ofs' (loadbytes cfg am rm p)

def storebytes_soundStatement : Prop :=
  ∀ bc m b ofs bytes m' am p sz q,
    Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = some m' → mmatch bc m am →
    pmatch bc b ofs p → bytes.length = zToNat sz →
    (∀ b' ofs' qt i, Fragment (Vptr b' ofs') qt i ∈ bytes → pmatch bc b' ofs' q) →
    mmatch bc m' (storebytes am p sz q)

def mmatch_extStatement : Prop :=
  ∀ bc m am m', mmatch bc m am →
    (∀ b ofs n bytes, bc b ≠ BCinvalid → zLe z0 n →
      Mem.loadbytes m' b ofs n = some bytes → Mem.loadbytes m b ofs n = some bytes) →
    Ple m.nextblock m'.nextblock → mmatch bc m' am

def mmatch_freeStatement : Prop :=
  ∀ bc m b lo hi m' am,
    Mem.free m b lo hi = some m' → mmatch bc m am → mmatch bc m' am

def mmatch_top'Statement : Prop :=
  ∀ bc m am, mmatch bc m am → mmatch bc m mtop

def mmatch_lub_lStatement : Prop :=
  ∀ cfg bc m x y, mmatch bc m x → mmatch bc m (mlub cfg x y)

def mmatch_lub_rStatement : Prop :=
  ∀ cfg bc m x y, mmatch bc m y → mmatch bc m (mlub cfg x y)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem bc_below_invalid : bc_below_invalidStatement := by
  intro b bc bound hnot hbelow
  cases h : bc b with
  | BCinvalid => rfl
  | BCglob id =>
      exact False.elim (hnot (hbelow b (by simp [h])))
  | BCstack =>
      exact False.elim (hnot (hbelow b (by simp [h])))
  | BCother =>
      exact False.elim (hnot (hbelow b (by simp [h])))

theorem pge_trans : pge_transStatement := by
  intro p q hpq r hqr
  induction hpq generalizing r <;> cases hqr <;> constructor

theorem pmatch_ge : pmatch_geStatement := by
  intro bc b ofs p q hpq hmq
  cases hpq with
  | pge_top q =>
      cases hmq with
      | gl id h => exact pmatch.top (by simp [h])
      | glo id h => exact pmatch.top (by simp [h])
      | glob id h => exact pmatch.top (by simp [h])
      | stk h => exact pmatch.top (by simp [h])
      | stack h => exact pmatch.top (by simp [h])
      | nonstack hns hni => exact pmatch.top hni
      | top hni => exact pmatch.top hni
  | bot p => cases hmq
  | pge_refl p => exact hmq
  | gloGl id ofs =>
      cases hmq with
      | gl id h => exact pmatch.glo id h
  | globGl id ofs =>
      cases hmq with
      | gl id h => exact pmatch.glob id h
  | globGlo id =>
      cases hmq with
      | glo id h => exact pmatch.glob id h
  | nsGl id ofs =>
      cases hmq with
      | gl id h => exact pmatch.nonstack (by simp [h]) (by simp [h])
  | nsGlo id =>
      cases hmq with
      | glo id h => exact pmatch.nonstack (by simp [h]) (by simp [h])
  | nsGlob =>
      cases hmq with
      | glob id h => exact pmatch.nonstack (by simp [h]) (by simp [h])
  | stackStk ofs =>
      cases hmq with
      | stk h => exact pmatch.stack h

theorem pmatch_top' : pmatch_top'Statement := by
  intro bc b ofs p h
  exact pmatch_ge bc b ofs Ptop p (pge.pge_top p) h

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

private theorem plub_gl_gl_comm_aux (i j : Common.AST.ident) (o p : CompCert4Lean.Lib.Integers.ptrofs) :
    (if i = j then if o = p then Gl i o else Glo i else Glob) =
      (if j = i then if p = o then Gl j p else Glo j else Glob) := by
  by_cases hij : i = j
  · subst j
    by_cases hop : o = p
    · subst p; simp
    · simp [hop, Ne.symm hop]
  · have hji : ¬j = i := Ne.symm hij
    simp [hij, hji]

private theorem plub_glo_glo_comm_aux (i j : Common.AST.ident) :
    (if i = j then Glo i else Glob) = (if j = i then Glo j else Glob) := by
  by_cases hij : i = j
  · subst j; simp
  · have hji : ¬j = i := Ne.symm hij
    simp [hij, hji]

private theorem plub_glo_rhs_comm_aux (i j : Common.AST.ident) :
    (if i = j then Glo j else Glob) = (if j = i then Glo j else Glob) := by
  by_cases hij : i = j
  · subst j; simp
  · have hji : ¬j = i := Ne.symm hij
    simp [hij, hji]

private theorem plub_glo_lhs_comm_aux (i j : Common.AST.ident) :
    (if i = j then Glo i else Glob) = (if j = i then Glo i else Glob) := by
  by_cases hij : i = j
  · subst j; simp
  · have hji : ¬j = i := Ne.symm hij
    simp [hij, hji]

private theorem plub_stk_stk_comm_aux (o p : CompCert4Lean.Lib.Integers.ptrofs) :
    (if o = p then Stk o else Stack) = (if p = o then Stk p else Stack) := by
  by_cases hop : o = p
  · subst p; simp
  · have hpo : ¬p = o := Ne.symm hop
    simp [hop, hpo]

theorem plub_comm : plub_commStatement := by
  intro p q
  cases p <;> cases q <;> simp only [plub]
  case Gl.Gl i o j p => exact plub_gl_gl_comm_aux i j o p
  case Gl.Glo i o j => exact plub_glo_rhs_comm_aux i j
  case Glo.Gl i j o => exact plub_glo_lhs_comm_aux i j
  case Glo.Glo i j => exact plub_glo_glo_comm_aux i j
  case Stk.Stk o p => exact plub_stk_stk_comm_aux o p

private theorem pge_gl_gl_lub_aux (i j : Common.AST.ident) (o p : CompCert4Lean.Lib.Integers.ptrofs) :
    pge (if i = j then if o = p then Gl i o else Glo i else Glob) (Gl i o) := by
  by_cases hij : i = j
  · subst j
    by_cases hop : o = p
    · subst p; simp; exact pge.pge_refl _
    · simp [hop]
      exact pge.gloGl _ _
  · simp [hij]
    exact pge.globGl _ _

private theorem pge_gl_glo_lub_aux (i j : Common.AST.ident) (o : CompCert4Lean.Lib.Integers.ptrofs) :
    pge (if i = j then Glo j else Glob) (Gl i o) := by
  by_cases hij : i = j
  · subst j; simp; exact pge.gloGl _ _
  · simp [hij]; exact pge.globGl _ _

private theorem pge_glo_gl_lub_aux (i j : Common.AST.ident) (o : CompCert4Lean.Lib.Integers.ptrofs) :
    pge (if i = j then Glo i else Glob) (Glo i) := by
  by_cases hij : i = j
  · subst j; simp; exact pge.pge_refl _
  · simp [hij]; exact pge.globGlo _

private theorem pge_glo_glo_lub_aux (i j : Common.AST.ident) :
    pge (if i = j then Glo i else Glob) (Glo i) := by
  by_cases hij : i = j
  · subst j; simp; exact pge.pge_refl _
  · simp [hij]; exact pge.globGlo _

private theorem pge_stk_stk_lub_aux (o p : CompCert4Lean.Lib.Integers.ptrofs) :
    pge (if o = p then Stk o else Stack) (Stk o) := by
  by_cases hop : o = p
  · subst p; simp; exact pge.pge_refl _
  · simp [hop]; exact pge.stackStk _

theorem pge_lub_l : pge_lub_lStatement := by
  intro p q
  cases p <;> cases q <;> simp only [plub]
  all_goals try constructor
  case Gl.Gl i o j p => exact pge_gl_gl_lub_aux i j o p
  case Gl.Glo i o j => exact pge_gl_glo_lub_aux i j o
  case Glo.Gl i j o => exact pge_glo_gl_lub_aux i j o
  case Glo.Glo i j => exact pge_glo_glo_lub_aux i j
  case Stk.Stk o p => exact pge_stk_stk_lub_aux o p

theorem pge_lub_r : pge_lub_rStatement := by
  intro p q
  rw [show plub p q = plub q p by
    cases p <;> cases q <;> simp only [plub]
    case Gl.Gl i o j p => exact plub_gl_gl_comm_aux i j o p
    case Gl.Glo i o j => exact plub_glo_rhs_comm_aux i j
    case Glo.Gl i j o => exact plub_glo_lhs_comm_aux i j
    case Glo.Glo i j => exact plub_glo_glo_comm_aux i j
    case Stk.Stk o p => exact plub_stk_stk_comm_aux o p]
  exact pge_lub_l q p

theorem pmatch_lub_l : pmatch_lub_lStatement := by
  intro bc b ofs p q h
  exact pmatch_ge bc b ofs (plub p q) p (pge_lub_l p q) h

end CompCert4Lean.Backend.ValueDomain
