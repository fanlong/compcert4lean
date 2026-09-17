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

namespace CompCert4Lean.Backend.ValueDomain

theorem pmatch_lub_r : pmatch_lub_rStatement := by
  intro bc b ofs p q h
  exact pmatch_ge bc b ofs (plub p q) q (pge_lub_r p q) h

theorem vmatch_ifptr : vmatch_ifptrStatement := by
  intro bc v p h
  cases v with
  | Vundef => exact vmatch.ifptrUndef p
  | Vint i => exact vmatch.ifptrInt i p
  | Vlong i => exact vmatch.ifptrLong i p
  | Vfloat f => exact vmatch.ifptrFloat f p
  | Vsingle f => exact vmatch.ifptrSingle f p
  | Vptr b ofs => exact vmatch.ifptrPtr b ofs p (h b ofs rfl)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem plub_least : plub_leastStatement := by
  intro r p q hp hq
  cases r <;> cases p <;> cases q <;> cases hp <;> cases hq <;>
    simp_all [plub]
  all_goals try constructor
  all_goals (try split <;> try simp_all <;> try constructor)
  all_goals (try split <;> try simp_all <;> try constructor)
  all_goals first
    | exact pge.gloGl _ _
    | exact pge.globGl _ _
    | exact pge.globGlo _
    | exact pge.nsGl _ _
    | exact pge.nsGlo _
    | exact pge.nsGlob
    | exact pge.stackStk _
    | exact pge.pge_refl _
    | exact pge.bot _
    | exact pge.pge_top _

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem pincl_ge : pincl_geStatement := by
  intro p q h
  cases p <;> cases q <;> simp [pincl] at h
  all_goals try subst_vars
  all_goals try constructor
  all_goals rcases h with ⟨h1, h2⟩
  all_goals subst_vars
  all_goals constructor

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vmatch_top : vmatch_topStatement := by
  intro bc v x h
  cases h with
  | vmatch_i i => exact vmatch.ifptrInt i Ptop
  | vmatch_iu i => exact vmatch.ifptrInt i Ptop
  | iuUndef i => exact vmatch.ifptrUndef Ptop
  | uns p i n _ _ => exact vmatch.ifptrInt i Ptop
  | vmatch_Uns_undef p n => exact vmatch.ifptrUndef Ptop
  | sgn p i n _ _ => exact vmatch.ifptrInt i Ptop
  | sgnUndef p n => exact vmatch.ifptrUndef Ptop
  | long i => exact vmatch.ifptrLong i Ptop
  | float f => exact vmatch.ifptrFloat f Ptop
  | single f => exact vmatch.ifptrSingle f Ptop
  | numUndef p => exact vmatch.ifptrUndef Ptop
  | numInt i p => exact vmatch.ifptrInt i Ptop
  | numLong i p => exact vmatch.ifptrLong i Ptop
  | numFloat f p => exact vmatch.ifptrFloat f Ptop
  | numSingle f p => exact vmatch.ifptrSingle f Ptop
  | ptr b ofs p hp => exact vmatch.ifptrPtr b ofs Ptop (pmatch_top' bc b ofs p hp)
  | ptrUndef p => exact vmatch.ifptrUndef Ptop
  | ifptrUndef p => exact vmatch.ifptrUndef Ptop
  | ifptrInt i p => exact vmatch.ifptrInt i Ptop
  | ifptrLong i p => exact vmatch.ifptrLong i Ptop
  | ifptrFloat f p => exact vmatch.ifptrFloat f Ptop
  | ifptrSingle f p => exact vmatch.ifptrSingle f Ptop
  | ifptrPtr b ofs p hp => exact vmatch.ifptrPtr b ofs Ptop (pmatch_top' bc b ofs p hp)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem usize_pos : usize_posStatement := by
  intro n
  unfold usize Int.size
  cases Int.unsigned n with
  | Z0 =>
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  | Zpos p =>
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive]
  | Zneg p =>
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive]

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_trans : vge_transStatement := by
  intro x y z hxy hyz
  have zLe_trans_local (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
      zLe a b → zLe b c → zLe a c := by
    intro hab hbc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
    exact Int.le_trans hab hbc
  have zLt_le_trans_local (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
      zLt a b → zLe b c → zLt a c := by
    intro hab hbc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
    exact Int.lt_of_lt_of_le hab hbc
  have zLe_lt_trans_local (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
      zLe a b → zLt b c → zLt a c := by
    intro hab hbc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
    exact Int.lt_of_le_of_lt hab hbc
  have is_uns_mon_local
      (n m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
      is_uns n i → zLe n m → is_uns m i := by
    intro hni hnm k hk hmk
    apply hni k hk
    exact zLe_trans_local n m k hnm hmk
  have is_sgn_mon_local
      (n m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
      is_sgn n i → zLe n m → is_sgn m i := by
    intro hni hnm k hk hmk
    apply hni k hk
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub n z1) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub m z1) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hmk
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hmk ⊢
    omega
  have is_uns_sgn_local
      (n m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
      is_uns n i → zLt n m → is_sgn m i := by
    intro hni hnm k hk hmk
    have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by rfl
    have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
    have hzw : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize = 32 := by rfl
    have hnk : zLe n k := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub m z1) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hmk
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz1, hzw] at hmk ⊢
      omega
    have htop : zLe n (zSub Int.zwordsize z1) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub Int.zwordsize z1)
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub m z1) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hmk
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz1, hzw] at hmk ⊢
      have hk0 := hk.1
      have hkw := hk.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hk0
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize at hkw
      rw [hz0] at hk0
      rw [hzw] at hkw
      omega
    have hkm : zLe z0 k ∧ zLt k Int.zwordsize := hk
    have hb0 := hni k hkm hnk
    have htopbits := hni (zSub Int.zwordsize z1)
      (by
        constructor
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub Int.zwordsize z1)
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz0, hz1, hzw]
          omega
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub Int.zwordsize z1) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz1, hzw]
          omega)
      htop
    rw [hb0, htopbits]
  induction hxy generalizing z <;> cases hyz <;>
    first
    | exact vge.bot _
    | exact vge.int _
    | exact vge.long _
    | exact vge.float _
    | exact vge.single _
    | exact vge.iu _
    | exact vge.iuInt _
    | exact vge.unsInt _ _ _ (by assumption) (by assumption)
    | exact vge.vge_uns_iu _ _ _ (by assumption) (by assumption)
    | exact vge.sgnInt _ _ _ (by assumption) (by assumption)
    | exact vge.sgnIU _ _ _ (by assumption) (by assumption)
    | exact vge.numInt _ _
    | exact vge.numLong _ _
    | exact vge.numFloat _ _
    | exact vge.numSingle _ _
    | exact vge.numIU _ _
    | exact vge.ifptrInt _ _
    | exact vge.ifptrLong _ _
    | exact vge.ifptrFloat _ _
    | exact vge.ifptrSingle _ _
    | exact vge.ifptrIU _ _
    | constructor <;> try assumption
    | apply vge.vge_uns_uns <;> try assumption
    | apply vge.sgnSgn <;> try assumption
    | apply vge.sgnUns <;> try assumption
    | apply vge.numUns <;> try assumption
    | apply vge.numSgn <;> try assumption
    | apply vge.numNum <;> try assumption
    | apply vge.ptrPtr <;> try assumption
    | apply vge.ifptrPtr <;> try assumption
    | apply vge.ifptrIfptr <;> try assumption
    | apply vge.ifptrUns <;> try assumption
    | apply vge.ifptrSgn <;> try assumption
    | apply vge.ifptrNum <;> try assumption
  all_goals try { apply pge_trans <;> assumption }
  all_goals try { apply is_uns_mon_local <;> assumption }
  all_goals try { apply is_sgn_mon_local <;> assumption }
  all_goals try { apply zLe_trans_local <;> assumption }
  all_goals try { apply zLt_le_trans_local <;> assumption }
  all_goals try { apply zLe_lt_trans_local <;> assumption }
  all_goals try { apply is_uns_sgn_local <;> assumption }

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

open Lean Elab Tactic Meta

private def isUns1PrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem is_uns_1_testbit_pos
    (a : CompCert4Lean.Lib.Integers.int)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    CompCert4Lean.Lib.Integers.Int.testbit a
        (.Zpos p) = a.val.testBit
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
  simp only [CompCert4Lean.Lib.Integers.Int.testbit,
    CompCert4Lean.Lib.Integers.WordCore.testbit]
  run_tac
    let lctx ← getLCtx
    let aF := (lctx.findFromUserName? `a).get!
    let pF := (lctx.findFromUserName? `p).get!
    let aE := mkFVar aF.fvarId
    let pE := mkFVar pF.fvarId
    let e ← mkAppM
      (isUns1PrivateName "CompCert4Lean.Lib.Integers.WordCore.positiveToNat_eq_posToNat") #[pE]
    let natTy := mkConst ``Nat
    let aval ← mkAppM ``CompCert4Lean.Lib.Integers.WordCore.Word.val #[aE]
    let f := mkLambda `k BinderInfo.default natTy
      (mkApp2 (mkConst ``Nat.testBit) aval (mkBVar 0))
    let ce ← mkAppM ``congrArg #[f, e]
    closeMainGoal Name.anonymous ce

theorem is_uns_1 : is_uns_1Statement := by
  intro n hn
  by_cases hb : n.val.testBit 0 = true
  · right
    apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
    apply Nat.eq_of_testBit_eq
    intro k
    cases k with
    | zero =>
        change n.val.testBit 0 = CompCert4Lean.Lib.Integers.Int.one.val.testBit 0
        have hone : CompCert4Lean.Lib.Integers.Int.one.val = 1 := by rfl
        rw [hone]
        simpa using hb
    | succ k =>
        have hnlt : n.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
          (CompCert4Lean.Lib.Integers.Int.toFin n).isLt
        have hOneBit : Nat.testBit 1 (Nat.succ k) = false := by
          apply Nat.testBit_lt_two_pow
          exact Nat.one_lt_two_pow (Nat.ne_of_gt (Nat.succ_pos k))
        by_cases hlt : Nat.succ k < CompCert4Lean.Lib.Integers.Int.wordsize
        · let p := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (Nat.succ k)
          have hp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p = Nat.succ k :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (Nat.succ_pos k)
          have hrange : zLe z0 (.Zpos p) ∧ zLt (.Zpos p) Int.zwordsize := by
            constructor
            · change (0 : Int) ≤ Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
              exact Int.ofNat_nonneg _
            · change (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) < Int.ofNat 32
              rw [hp]
              exact Int.ofNat_lt.mpr hlt
          have hge : zLe z1 (.Zpos p) := by
            change (1 : Int) ≤ Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
            have hp0 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
            change Int.ofNat 1 ≤ Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
            apply Int.ofNat_le.mpr
            omega
          have hbit := hn (.Zpos p) hrange hge
          have hbit' : n.val.testBit (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = false := by
            change CompCert4Lean.Lib.Integers.Int.testbit n (.Zpos p) = false at hbit
            rw [is_uns_1_testbit_pos] at hbit
            exact hbit
          rw [hp] at hbit'
          have hone : CompCert4Lean.Lib.Integers.Int.one.val = 1 := by rfl
          rw [hone]
          exact hbit'.trans hOneBit.symm
        · have hpow : 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize ≤
              2 ^ (Nat.succ k) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hlt)
          have hnbit : n.val.testBit (Nat.succ k) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hnlt hpow)
          have hone : CompCert4Lean.Lib.Integers.Int.one.val = 1 := by rfl
          rw [hone]
          exact hnbit.trans hOneBit.symm
  · left
    apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
    apply Nat.eq_of_testBit_eq
    intro k
    cases k with
    | zero =>
        change n.val.testBit 0 = CompCert4Lean.Lib.Integers.Int.zero.val.testBit 0
        have hzero : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := by rfl
        rw [hzero]
        have hb' : n.val.testBit 0 = false := Bool.eq_false_iff.mpr hb
        simpa using hb'
    | succ k =>
        have hnlt : n.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
          (CompCert4Lean.Lib.Integers.Int.toFin n).isLt
        have hZeroBit : Nat.testBit 0 (Nat.succ k) = false := by
          apply Nat.testBit_lt_two_pow
          exact Nat.two_pow_pos _
        by_cases hlt : Nat.succ k < CompCert4Lean.Lib.Integers.Int.wordsize
        · let p := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (Nat.succ k)
          have hp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p = Nat.succ k :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (Nat.succ_pos k)
          have hrange : zLe z0 (.Zpos p) ∧ zLt (.Zpos p) Int.zwordsize := by
            constructor
            · change (0 : Int) ≤ Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
              exact Int.ofNat_nonneg _
            · change (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) < Int.ofNat 32
              rw [hp]
              exact Int.ofNat_lt.mpr hlt
          have hge : zLe z1 (.Zpos p) := by
            change (1 : Int) ≤ Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
            have hp0 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
            change Int.ofNat 1 ≤ Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
            apply Int.ofNat_le.mpr
            omega
          have hbit := hn (.Zpos p) hrange hge
          have hbit' : n.val.testBit (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = false := by
            change CompCert4Lean.Lib.Integers.Int.testbit n (.Zpos p) = false at hbit
            rw [is_uns_1_testbit_pos] at hbit
            exact hbit
          rw [hp] at hbit'
          have hzero : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := by rfl
          rw [hzero]
          exact hbit'.trans hZeroBit.symm
        · have hpow : 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize ≤
              2 ^ (Nat.succ k) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hlt)
          have hnbit : n.val.testBit (Nat.succ k) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hnlt hpow)
          have hzero : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := by rfl
          rw [hzero]
          exact hnbit.trans hZeroBit.symm

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vmatch_Uns_1 : vmatch_Uns_1Statement := by
  intro bc p v h
  cases h with
  | uns p i n hn hi =>
      right
      rcases is_uns_1 i hi with hzero | hone
      · left
        rw [hzero]
      · right
        rw [hone]
  | vmatch_Uns_undef p n =>
      left
      rfl

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_uns_uns' : vge_uns_uns'Statement := by
  intro p n
  unfold uns1
  by_cases h1 : zle n z1 = true
  · simp only [if_pos h1]
    exact vge.vge_uns_uns p z1 p n (zle_true_prop_for_inval h1) (pge.pge_refl p)
  · by_cases h7 : zle n (zOfNat 7) = true
    · simp only [if_neg h1, if_pos h7]
      exact vge.vge_uns_uns p (zOfNat 7) p n
        (zle_true_prop_for_inval h7) (pge.pge_refl p)
    · by_cases h8 : zle n (zOfNat 8) = true
      · simp only [if_neg h1, if_neg h7, if_pos h8]
        exact vge.vge_uns_uns p (zOfNat 8) p n
          (zle_true_prop_for_inval h8) (pge.pge_refl p)
      · by_cases h15 : zle n (zOfNat 15) = true
        · simp only [if_neg h1, if_neg h7, if_neg h8, if_pos h15]
          exact vge.vge_uns_uns p (zOfNat 15) p n
            (zle_true_prop_for_inval h15) (pge.pge_refl p)
        · by_cases h16 : zle n (zOfNat 16) = true
          · simp only [if_neg h1, if_neg h7, if_neg h8, if_neg h15, if_pos h16]
            exact vge.vge_uns_uns p (zOfNat 16) p n
              (zle_true_prop_for_inval h16) (pge.pge_refl p)
          · simp only [if_neg h1, if_neg h7, if_neg h8, if_neg h15, if_neg h16]
            exact vge.numUns p p n (pge.pge_refl p)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

private theorem zMax_comm_for_vlub
    (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : zMax x y = zMax y x := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · by_cases h' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
    · have heq := Int.le_antisymm h h'
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h, h', heq]
    · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h, h']
  · have h' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x :=
      Int.le_of_not_le h
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h, h']

private theorem vlub_int_comm_local (cstr : int → aval) (i j : int) :
    vlub_int cstr i j = vlub_int cstr j i := by
  unfold vlub_int
  by_cases h : Int.eq i j = true
  · have h' : Int.eq j i = true := by
      change decide (j.intval = i.intval) = true
      change decide (i.intval = j.intval) = true at h
      simpa [eq_comm] using h
    change decide (i.intval = j.intval) = true at h
    have hval : i.intval = j.intval := of_decide_eq_true h
    have hij : i = j := CompCert4Lean.Lib.Integers.WordCore.ext hval
    subst j
    simp
  · have h' : ¬ Int.eq j i = true := by
      intro h'
      apply h
      change decide (j.intval = i.intval) = true at h'
      change decide (i.intval = j.intval) = true
      simpa [eq_comm] using h'
    by_cases hi : Int.lt i Int.zero = true <;>
      by_cases hj : Int.lt j Int.zero = true <;>
        simp [h, h', hi, hj, Bool.or_comm, zMax_comm_for_vlub]

private theorem plub_comm_local (p q : aptr) : plub p q = plub q p := by
  exact plub_comm p q

private theorem int64_eq_comm_local (i j : int64) : Int64.eq i j = Int64.eq j i := by
  change decide (i.intval = j.intval) = decide (j.intval = i.intval)
  by_cases h : i.intval = j.intval
  · simp [h]
  · have h' : ¬j.intval = i.intval := by
      intro h'
      exact h h'.symm
    simp [h, h']

private theorem float_eq_comm_local (i j : float) : (i = j) = (j = i) := by
  by_cases h : i = j
  · simp [h]
  · have h' : ¬j = i := Ne.symm h
    simp [h, h']

private theorem float32_eq_comm_local (i j : float32) : (i = j) = (j = i) := by
  by_cases h : i = j
  · simp [h]
  · have h' : ¬j = i := Ne.symm h
    simp [h, h']

private theorem vlub_long_comm_local (i j : int64) :
    (if Int64.eq i j = true then L i else ntop) =
      (if Int64.eq j i = true then L j else ntop) := by
  by_cases h : Int64.eq i j = true
  · have h' : Int64.eq j i = true := by
      change decide (j.intval = i.intval) = true
      change decide (i.intval = j.intval) = true at h
      simpa [eq_comm] using h
    change decide (i.intval = j.intval) = true at h
    have hij : i = j := CompCert4Lean.Lib.Integers.WordCore.ext (of_decide_eq_true h)
    subst j
    simp
  · have h' : ¬ Int64.eq j i = true := by
      intro h'
      apply h
      change decide (j.intval = i.intval) = true at h'
      change decide (i.intval = j.intval) = true
      simpa [eq_comm] using h'
    simp [h, h']

private theorem vlub_float_comm_local (i j : float) :
    (if i = j then F i else ntop) = (if j = i then F j else ntop) := by
  by_cases h : i = j
  · subst j
    simp
  · have h' : ¬j = i := Ne.symm h
    simp [h, h']

private theorem vlub_float32_comm_local (i j : float32) :
    (if i = j then FS i else ntop) = (if j = i then FS j else ntop) := by
  by_cases h : i = j
  · subst j
    simp
  · have h' : ¬j = i := Ne.symm h
    simp [h, h']

theorem vlub_comm : vlub_commStatement := by
  intro cfg v w
  cases v <;> cases w
  case I.I i j => simpa only [vlub] using (vlub_int_comm_local I i j)
  case I.IU i j => simpa only [vlub] using (vlub_int_comm_local IU i j)
  case IU.I i j => simpa only [vlub] using (vlub_int_comm_local IU i j)
  case IU.IU i j => simpa only [vlub] using (vlub_int_comm_local IU i j)
  case L.L i j => simpa only [vlub] using (vlub_long_comm_local i j)
  case F.F i j => simpa only [vlub] using (vlub_float_comm_local i j)
  case FS.FS i j => simpa only [vlub] using (vlub_float32_comm_local i j)
  all_goals
    simp [vlub, zMax_comm_for_vlub, plub_comm_local, int64_eq_comm_local,
      float_eq_comm_local, float32_eq_comm_local]

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_uns_i' : vge_uns_i'Statement := by
  intro p n i hn hi
  exact vge_trans (uns1 p n) (Uns p n) (I i)
    (vge_uns_uns' p n) (vge.unsInt p n i hn hi)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

private theorem zLe_trans_vmatch
    (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    zLe a b → zLe b c → zLe a c := by
  intro hab hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
  exact Int.le_trans hab hbc

private theorem zLt_le_vmatch
    (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    zLt a b → zLe b c → zLt a c := by
  intro hab hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
  exact Int.lt_of_lt_of_le hab hbc

private theorem zLt_trans_vmatch
    (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    zLt a b → zLt b c → zLt a c := by
  intro hab hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
  exact Int.lt_trans hab hbc

private theorem zLe_lt_vmatch
    (a b c : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    zLe a b → zLt b c → zLt a c := by
  intro hab hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
  exact Int.lt_of_le_of_lt hab hbc

private theorem is_uns_mon_vmatch
    (n m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    is_uns n i → zLe n m → is_uns m i := by
  intro hni hnm k hk hmk
  apply hni k hk
  exact zLe_trans_vmatch n m k hnm hmk

private theorem is_sgn_mon_vmatch
    (n m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    is_sgn n i → zLe n m → is_sgn m i := by
  intro hni hnm k hk hmk
  apply hni k hk
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub n z1) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub m z1) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hmk
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hmk ⊢
  omega

private theorem is_uns_sgn_vmatch
    (n m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    is_uns n i → zLt n m → is_sgn m i := by
  intro hni hnm k hk hmk
  have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by rfl
  have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
  have hzw : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize = 32 := by rfl
  have hnk : zLe n k := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub m z1) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hmk
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz1, hzw] at hmk ⊢
    omega
  have htop : zLe n (zSub Int.zwordsize z1) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub Int.zwordsize z1)
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub m z1) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hmk
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz1, hzw] at hmk ⊢
    have hk0 := hk.1
    have hkw := hk.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hk0
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize at hkw
    rw [hz0] at hk0
    rw [hzw] at hkw
    omega
  have hb0 := hni k hk hnk
  have htopbits := hni (zSub Int.zwordsize z1)
    (by
      constructor
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub Int.zwordsize z1)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz0, hz1, hzw]
        omega
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zSub Int.zwordsize z1) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz1, hzw]
        omega)
    htop
  rw [hb0, htopbits]

theorem vmatch_ge : vmatch_geStatement := by
  intro bc v x y hxy hmv
  induction hxy generalizing v <;> cases hmv <;>
    try constructor <;> try assumption
  all_goals try { apply is_uns_mon_vmatch <;> assumption }
  all_goals try { apply is_sgn_mon_vmatch <;> assumption }
  all_goals try { apply zLe_trans_vmatch <;> assumption }
  all_goals try { apply zLt_le_vmatch <;> assumption }
  all_goals try { apply zLt_trans_vmatch <;> assumption }
  all_goals try { apply zLe_lt_vmatch <;> assumption }
  all_goals try { apply is_uns_sgn_vmatch <;> assumption }
  all_goals try { apply pmatch_ge <;> assumption }

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_sgn_sgn' : vge_sgn_sgn'Statement := by
  intro p n
  unfold sgn
  by_cases h8 : zle n (zOfNat 8) = true
  · simp only [if_pos h8]
    exact vge.sgnSgn p (zOfNat 8) p n (zle_true_prop_for_inval h8) (pge.pge_refl p)
  · by_cases h16 : zle n (zOfNat 16) = true
    · simp only [if_neg h8, if_pos h16]
      exact vge.sgnSgn p (zOfNat 16) p n (zle_true_prop_for_inval h16) (pge.pge_refl p)
    · simp only [if_neg h8, if_neg h16]
      exact vge.numSgn p p n (pge.pge_refl p)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_uns_iu' : vge_uns_iu'Statement := by
  intro p n i hn hi
  exact vge_trans (uns1 p n) (Uns p n) (IU i)
    (vge_uns_uns' p n) (vge.vge_uns_iu p n i hn hi)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_sgn_i' : vge_sgn_i'Statement := by
  intro p n i hn hi
  exact vge_trans (sgn p n) (Sgn p n) (I i)
    (vge_sgn_sgn' p n) (vge.sgnInt p n i hn hi)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vge_sgn_iu' : vge_sgn_iu'Statement := by
  intro p n i hn hi
  exact vge_trans (sgn p n) (Sgn p n) (IU i)
    (vge_sgn_sgn' p n) (vge.sgnIU p n i hn hi)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem match_aptr_of_aval : match_aptr_of_avalStatement := by
  intro cfg bc b ofs av h
  cases h <;> simp [aptr_of_aval] <;> assumption

theorem pmatch_vplub : pmatch_vplubStatement := by
  intro bc b ofs x p h
  cases x with
  | Vbot => exact h
  | I _ => exact h
  | IU _ => exact h
  | Uns _ _ => exact h
  | Sgn _ _ => exact h
  | L _ => exact h
  | F _ => exact h
  | FS _ => exact h
  | Num _ => exact h
  | Ptr q => exact pmatch_lub_r bc b ofs q p h
  | Ifptr q => exact pmatch_lub_r bc b ofs q p h

theorem vmatch_vplub_r : vmatch_vplub_rStatement := by
  intro bc v x p h
  cases h with
  | ifptrUndef => exact vmatch.ifptrUndef (vplub x p)
  | ifptrInt i => exact vmatch.ifptrInt i (vplub x p)
  | ifptrLong i => exact vmatch.ifptrLong i (vplub x p)
  | ifptrFloat f => exact vmatch.ifptrFloat f (vplub x p)
  | ifptrSingle f => exact vmatch.ifptrSingle f (vplub x p)
  | ifptrPtr b ofs =>
      exact vmatch.ifptrPtr b ofs (vplub x p)
        (pmatch_vplub bc b ofs x p (by assumption))

theorem vmatch_vplub_l : vmatch_vplub_lStatement := by
  intro bc v x p h
  cases h <;> simp [vplub] <;> try constructor
  all_goals try (apply pmatch_lub_l <;> assumption)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vpincl_ge : vpincl_geStatement := by
  intro x p h
  cases x with
  | Vbot => exact vge.bot _
  | I i => exact vge.ifptrInt p i
  | IU i => exact vge.ifptrIU p i
  | Uns q n => exact vge.ifptrUns p q n (pincl_ge q p h)
  | Sgn q n => exact vge.ifptrSgn p q n (pincl_ge q p h)
  | L i => exact vge.ifptrLong p i
  | F f => exact vge.ifptrFloat p f
  | FS f => exact vge.ifptrSingle p f
  | Num q => exact vge.ifptrNum p q (pincl_ge q p h)
  | Ptr q => exact vge.ifptrPtr p q (pincl_ge q p h)
  | Ifptr q => exact vge.ifptrIfptr p q (pincl_ge q p h)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem symbol_address_sound : symbol_address_soundStatement := by
  intro bc ge id ofs hge
  unfold CompCert4Lean.Common.Globalenvs.Genv.symbol_address
  cases hfind : CompCert4Lean.Common.Globalenvs.Genv.find_symbol ge id with
  | none => exact vmatch.ptrUndef (Gl id ofs)
  | some b =>
      exact vmatch.ptr b ofs (Gl id ofs)
        (pmatch.gl id ((hge.1 id b).mp hfind))

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem vmatch_ptr_gl : vmatch_ptr_glStatement := by
  intro bc ge v id ofs hge hvm
  cases hvm with
  | ptr b ofs' p hp =>
      cases hp with
      | gl id' hbc =>
          unfold CompCert4Lean.Common.Globalenvs.Genv.symbol_address
          rw [show CompCert4Lean.Common.Globalenvs.Genv.find_symbol ge id = some b from
            (hge.1 id b).mpr hbc]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
  | ptrUndef p =>
      exact CompCert4Lean.Common.Values.Val.lessdef_undef _

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem binop_float_sound : binop_float_soundStatement := by
  intro bc sem v x w y hxy hwy
  cases hxy <;> cases hwy <;> simp [binop_float, ntop2, provenance]
  all_goals first
    | exact vmatch.float _
    | exact vmatch.numFloat _ _
    | exact vmatch.numUndef _

theorem of_optbool_sound : of_optbool_soundStatement := by
  intro bc ob ab h
  have hzero : is_uns z1 Int.zero := by
    intro m hm hle
    cases m with
    | Zneg p =>
        have hnonneg := hm.1
        change (0 : Int) ≤ -Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hnonneg
        have hp : (0 : Int) < Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          Int.natCast_pos.mpr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
        omega
    | Z0 => rfl
    | Zpos p =>
        calc
          Int.testbit Int.zero (.Zpos p) =
              Int.zero.val.testBit
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
            is_uns_1_testbit_pos Int.zero p
          _ = false := by
            have hz : Int.zero.val = 0 := by rfl
            rw [hz]
            exact Nat.zero_testBit _
  have hone : is_uns z1 Int.one := by
    intro m hm hle
    cases m with
    | Zneg p =>
        have hnonneg := hm.1
        change (0 : Int) ≤ -Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hnonneg
        have hp : (0 : Int) < Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          Int.natCast_pos.mpr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
        omega
    | Z0 =>
        change (1 : Int) ≤ 0 at hle
        omega
    | Zpos p =>
        calc
          Int.testbit Int.one (.Zpos p) =
              Int.one.val.testBit
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
            is_uns_1_testbit_pos Int.one p
          _ = false := by
            have ho : Int.one.val = 1 := by rfl
            rw [ho]
            have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
            apply Nat.testBit_lt_two_pow
            exact Nat.one_lt_two_pow (Nat.ne_of_gt hp)
  cases h with
  | noneCase =>
      simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool]
      exact vmatch.vmatch_Uns_undef _ _
  | justCase b =>
      cases b <;>
        simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool] <;>
        constructor
  | maybeNone b =>
      simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool]
      exact vmatch.iuUndef _
  | maybeSome b =>
      cases b <;>
        simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool] <;>
        constructor
  | topCase ob =>
      cases ob with
      | none =>
          simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool]
          exact vmatch.vmatch_Uns_undef _ _
      | some b =>
          cases b with
          | false =>
              simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool]
              apply vmatch.uns Pbot Int.zero z1
              · change (0 : Int) ≤ 1
                omega
              · exact hzero
          | true =>
              simp [CompCert4Lean.Common.Values.Val.of_optbool, of_optbool]
              apply vmatch.uns Pbot Int.one z1
              · change (0 : Int) ≤ 1
                omega
              · exact hone

theorem resolve_branch_sound : resolve_branch_soundStatement := by
  intro b ab b' hcm hres
  cases hcm with
  | justCase b =>
      simp [resolve_branch] at hres
      exact hres.symm
  | maybeSome b =>
      simp [resolve_branch] at hres
      exact hres.symm
  | topCase ob => simp [resolve_branch] at hres

theorem add_undef_sound : add_undef_soundStatement := by
  intro bc v x h
  cases h <;> simp [add_undef, ntop] <;> constructor <;> assumption

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem add_undef_undef : add_undef_undefStatement := by
  intro bc x
  cases x <;> simp [add_undef, ntop] <;> constructor

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

private theorem val_lessdef_normalize_local (v : val)
    (ty : CompCert4Lean.Common.AST.typ) :
    CompCert4Lean.Common.Values.Val.lessdef
      (CompCert4Lean.Common.Values.Val.normalize v ty) v := by
  cases v <;> cases ty <;>
    simp [CompCert4Lean.Common.Values.Val.normalize,
      CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor

private theorem vmatch_add_undef_of_lessdef
    (bc : block_classification) (v v' : val) (x : aval) :
    CompCert4Lean.Common.Values.Val.lessdef v' v →
      vmatch bc v x → vmatch bc v' (add_undef x) := by
  intro hld hm
  cases hld with
  | lessdef_refl => exact add_undef_sound bc v x hm
  | lessdef_undef => exact add_undef_undef bc x

theorem vnormalize_type_sound : vnormalize_type_soundStatement := by
  intro bc v x ty h
  have hcases :
      CompCert4Lean.Common.Values.Val.has_type v ty ∧
          vnormalize_type ty x = x ∨
        vnormalize_type ty x = add_undef x := by
    cases h <;> cases ty <;>
      simp [vnormalize_type, CompCert4Lean.Common.Values.Val.has_type,
        CompCert4Lean.X86_64.Archi.ptr64]
  rcases hcases with ⟨hv, hx⟩ | hx
  · rw [hx, CompCert4Lean.Common.Values.Val.normalize_idem v ty hv]
    exact h
  · rw [hx]
    exact vmatch_add_undef_of_lessdef bc v
      (CompCert4Lean.Common.Values.Val.normalize v ty) x
      (val_lessdef_normalize_local v ty) h
private theorem is_uns_usize_select_aux (i : int) : is_uns (usize i) i := by
  intro m hm hle
  cases m with
  | Zneg p =>
      have hnonneg := hm.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hnonneg
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      cases hi : i.intval with
      | Zneg p =>
          have hirange := i.intrange.1
          rw [hi] at hirange
          change (-1 : Int) < -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hirange
          have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          have hp' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
            Int.natCast_pos.mpr hp
          omega
      | Z0 =>
          change i.val.testBit 0 = false
          have hiv : i.val = 0 := by
            unfold CompCert4Lean.Lib.Integers.WordCore.Word.val
            rw [hi]
            rfl
          simp [hiv]
      | Zpos p =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (usize i) ≤ 0 at hle
          unfold usize Int.size at hle
          simp only [CompCert4Lean.Lib.Integers.Int.unsigned,
            CompCert4Lean.Lib.Integers.WordCore.unsigned] at hle
          rw [hi] at hle
          change Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size p)) ≤ 0 at hle
          have hs := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size p)
          have hs' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size p)) :=
            Int.natCast_pos.mpr hs
          omega
  | Zpos p =>
      change CompCert4Lean.Lib.Integers.Int.testbit i (.Zpos p) = false
      rw [is_uns_1_testbit_pos]
      apply Nat.testBit_lt_two_pow
      cases hi : i.intval with
      | Zneg q =>
          have hirange := i.intrange.1
          rw [hi] at hirange
          change (-1 : Int) < -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at hirange
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hq' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
            Int.natCast_pos.mpr hq
          omega
      | Z0 =>
          have hiv : i.val = 0 := by
            unfold CompCert4Lean.Lib.Integers.WordCore.Word.val
            rw [hi]
            rfl
          rw [hiv]
          exact Nat.two_pow_pos _
      | Zpos q =>
          have hiv : i.val =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q := by
            unfold CompCert4Lean.Lib.Integers.WordCore.Word.val
            rw [hi]
            rfl
          rw [hiv]
          have hsize : Nat.log2
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) + 1 ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (usize i) ≤
              Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hle
            unfold usize Int.size at hle
            simp only [CompCert4Lean.Lib.Integers.Int.unsigned,
              CompCert4Lean.Lib.Integers.WordCore.unsigned] at hle
            rw [hi] at hle
            change Int.ofNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size q)) ≤
              Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hle
            have hsz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size q) =
                Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) + 1 := by
              unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size
              exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
                (by omega)
            rw [hsz] at hle
            exact Int.ofNat_le.mp hle
          apply (Nat.log2_lt
            (Nat.ne_of_gt
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q))).mp
          omega

open Lean Elab Tactic Meta

private theorem word_val_repr_zOfNat_select_aux (bits n : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))).val =
      n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let zOfNatE ← mkAppM ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      #[← mkAppM ``Int.ofNat #[nE]]
    let h₁ ← mkAppM
      (isUns1PrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[bitsE, zOfNatE]
    let h₂ ← mkAppM
      (isUns1PrivateName "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")
      #[bitsE, nE]
    let e ← mkAppM ``Eq.trans #[h₁, h₂]
    closeMainGoal Name.anonymous e

private theorem int_not_val_select_aux (i : int) :
    (CompCert4Lean.Lib.Integers.Int.not i).val =
      Nat.xor i.val (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) := by
  unfold CompCert4Lean.Lib.Integers.Int.not
    CompCert4Lean.Lib.Integers.WordCore.not
  change (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (Int.ofNat
          (Nat.xor i.val
            (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1))))).val =
    Nat.xor i.val (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1)
  rw [word_val_repr_zOfNat_select_aux]
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow
  · exact (CompCert4Lean.Lib.Integers.Int.toFin i).isLt
  · have hp : 0 < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := Nat.two_pow_pos _
    omega

private theorem int_testbit_not_select_aux (i : int)
    (m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hm : zLe z0 m ∧ zLt m Int.zwordsize) :
    Int.testbit (Int.not i) m = !(Int.testbit i m) := by
  cases m with
  | Zneg p =>
      have hnonneg := hm.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hnonneg
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      change (CompCert4Lean.Lib.Integers.Int.not i).val.testBit 0 =
        !i.val.testBit 0
      rw [int_not_val_select_aux]
      calc
        (Nat.xor i.val
            (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1)).testBit 0 =
            (i.val.testBit 0 ^^ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1).testBit 0) :=
          Nat.testBit_xor _ _ _
        _ = !i.val.testBit 0 := by
          rw [Nat.testBit_two_pow_sub_one]
          simp [CompCert4Lean.Lib.Integers.Int.wordsize]
  | Zpos p =>
      change CompCert4Lean.Lib.Integers.Int.testbit
        (CompCert4Lean.Lib.Integers.Int.not i) (.Zpos p) =
        !(CompCert4Lean.Lib.Integers.Int.testbit i (.Zpos p))
      rw [is_uns_1_testbit_pos, is_uns_1_testbit_pos,
        int_not_val_select_aux]
      have hp := hm.2
      change (Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat 32 at hp
      have hp' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32 :=
        Int.ofNat_lt.mp hp
      calc
        (Nat.xor i.val
            (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1)).testBit
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
            (i.val.testBit (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) ^^
              (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1).testBit
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) :=
          Nat.testBit_xor _ _ _
        _ = !i.val.testBit (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
          rw [Nat.testBit_two_pow_sub_one]
          simp [CompCert4Lean.Lib.Integers.Int.wordsize, hp']

private theorem is_sgn_ssize_select_aux (i : int) : is_sgn (ssize i) i := by
  by_cases hneg : Int.lt i Int.zero = true
  · intro m hm hge
    have hsize_m : zLe (usize (Int.not i)) m := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (usize (Int.not i)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (zSub (ssize i) z1) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hge
      unfold ssize at hge
      simp only [hneg, if_pos, zAdd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        zSub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hge
      have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
      rw [hz1] at hge
      unfold usize
      omega
    have hjm := is_uns_usize_select_aux (Int.not i) m hm hsize_m
    rw [int_testbit_not_select_aux i m hm] at hjm
    let top := zSub Int.zwordsize z1
    have htoprange : zLe z0 top ∧ zLt top Int.zwordsize := by
      have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by rfl
      have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
      have hzw : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize = 32 := by rfl
      constructor
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ top
        simp only [top, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hz0, hz1, hzw]
        omega
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ top <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize
        simp only [top, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hz1, hzw]
        omega
    have hsize_top : zLe (usize (Int.not i)) top := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (usize (Int.not i)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ top
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (usize (Int.not i)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hsize_m
      have hmw := hm.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize at hmw
      simp only [top, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
      have hzw : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize = 32 := by rfl
      rw [hz1, hzw]
      rw [hzw] at hmw
      omega
    have hjtop := is_uns_usize_select_aux (Int.not i) top htoprange hsize_top
    rw [int_testbit_not_select_aux i top htoprange] at hjtop
    change Int.testbit i m = Int.testbit i top
    cases hmBit : Int.testbit i m <;>
      cases htBit : Int.testbit i top <;>
      simp [hmBit, htBit] at hjm hjtop ⊢
  · apply is_uns_sgn_vmatch (usize i) (ssize i) i
      (is_uns_usize_select_aux i)
    have hfalse : Int.lt i Int.zero = false := Bool.eq_false_iff.mpr hneg
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (usize i) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ssize i)
    unfold ssize usize
    simp only [hfalse, Bool.false_eq_true, if_false, zAdd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
    rw [hz1]
    omega

private theorem ssize_pos_select_aux (i : int) : zLt z0 (ssize i) := by
  cases h : Int.lt i Int.zero with
  | false =>
      have hu := usize_pos i
      unfold usize at hu
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ssize i)
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Int.size i) at hu
      unfold ssize
      simp only [h, Bool.false_eq_true, if_false, zAdd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by rfl
      have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
      rw [hz0] at hu
      rw [hz0, hz1]
      omega
  | true =>
      have hu := usize_pos (Int.not i)
      unfold usize at hu
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ssize i)
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Int.size (Int.not i)) at hu
      unfold ssize
      simp only [h, if_true, zAdd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by rfl
      have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
      rw [hz0] at hu
      rw [hz0, hz1]
      omega

private theorem zle_max_l_select_aux
    (a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : zLe a (zMax a b) := by
  rw [zMax_comm_for_vlub]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_max_r b a

private theorem zle_max_r_select_aux
    (a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : zLe b (zMax a b) := by
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_max_r a b

private theorem vge_vlub_int_i_select_aux (i j : int) :
    vge (vlub_int I i j) (I i) := by
  unfold vlub_int
  by_cases hij : Int.eq i j = true
  · have hij' : i = j := by
      change decide (i.intval = j.intval) = true at hij
      exact CompCert4Lean.Lib.Integers.WordCore.ext (of_decide_eq_true hij)
    subst j
    rw [if_pos hij]
    exact vge.int i
  · by_cases hneg : Int.lt i Int.zero = true ∨ Int.lt j Int.zero = true
    · simp [hij, hneg]
      apply vge_sgn_i'
      · exact zLt_le_vmatch z0 (ssize i) (zMax (ssize i) (ssize j))
          (ssize_pos_select_aux i) (zle_max_l_select_aux _ _)
      · exact is_sgn_mon_vmatch (ssize i) (zMax (ssize i) (ssize j)) i
          (is_sgn_ssize_select_aux i) (zle_max_l_select_aux _ _)
    · have hi : Int.lt i Int.zero = false :=
        Bool.eq_false_iff.mpr (fun h => hneg (Or.inl h))
      have hj : Int.lt j Int.zero = false :=
        Bool.eq_false_iff.mpr (fun h => hneg (Or.inr h))
      simp [hij, hi, hj]
      apply vge_uns_i'
      · exact zLe_trans_vmatch z0 (usize i) (zMax (usize i) (usize j))
          (usize_pos i) (zle_max_l_select_aux _ _)
      · exact is_uns_mon_vmatch (usize i) (zMax (usize i) (usize j)) i
          (is_uns_usize_select_aux i) (zle_max_l_select_aux _ _)

private theorem vge_vlub_int_iu_select_aux (i j : int) :
    vge (vlub_int IU i j) (IU i) := by
  unfold vlub_int
  by_cases hij : Int.eq i j = true
  · have hij' : i = j := by
      change decide (i.intval = j.intval) = true at hij
      exact CompCert4Lean.Lib.Integers.WordCore.ext (of_decide_eq_true hij)
    subst j
    rw [if_pos hij]
    exact vge.iu i
  · by_cases hneg : Int.lt i Int.zero = true ∨ Int.lt j Int.zero = true
    · simp [hij, hneg]
      apply vge_sgn_iu'
      · exact zLt_le_vmatch z0 (ssize i) (zMax (ssize i) (ssize j))
          (ssize_pos_select_aux i) (zle_max_l_select_aux _ _)
      · exact is_sgn_mon_vmatch (ssize i) (zMax (ssize i) (ssize j)) i
          (is_sgn_ssize_select_aux i) (zle_max_l_select_aux _ _)
    · have hi : Int.lt i Int.zero = false :=
        Bool.eq_false_iff.mpr (fun h => hneg (Or.inl h))
      have hj : Int.lt j Int.zero = false :=
        Bool.eq_false_iff.mpr (fun h => hneg (Or.inr h))
      simp [hij, hi, hj]
      apply vge_uns_iu'
      · exact zLe_trans_vmatch z0 (usize i) (zMax (usize i) (usize j))
          (usize_pos i) (zle_max_l_select_aux _ _)
      · exact is_uns_mon_vmatch (usize i) (zMax (usize i) (usize j)) i
          (is_uns_usize_select_aux i) (zle_max_l_select_aux _ _)

private theorem vge_refl_select_aux (x : aval) : vge x x := by
  cases x <;> try constructor
  all_goals first
    | exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_refl _
    | exact pge.pge_refl _

private theorem zlt_max_add_one_l_select_aux
    (n a : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    zLt n (zMax (zAdd n z1) a) := by
  apply zLt_le_vmatch n (zAdd n z1) _
  · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zAdd n z1)
    simp only [zAdd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
    rw [hz1]
    omega
  · exact zle_max_l_select_aux _ _

private theorem zlt_max_add_one_r_select_aux
    (a n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    zLt n (zMax a (zAdd n z1)) := by
  apply zLt_le_vmatch n (zAdd n z1) _
  · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zAdd n z1)
    simp only [zAdd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
    rw [hz1]
    omega
  · exact zle_max_r_select_aux _ _

private theorem vge_sgn_uns_select_aux (q : aptr)
    (m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hnm : zLt n m) (hqp : pge q p) : vge (sgn q m) (Uns p n) := by
  exact vge_trans _ (Sgn q m) _ (vge_sgn_sgn' q m)
    (vge.sgnUns q m p n hnm hqp)

private theorem vge_sgn_sgn_select_aux (q : aptr)
    (m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hnm : zLe n m) (hqp : pge q p) : vge (sgn q m) (Sgn p n) := by
  exact vge_trans _ (Sgn q m) _ (vge_sgn_sgn' q m)
    (vge.sgnSgn q m p n hnm hqp)

private theorem vge_uns_uns_select_aux (q : aptr)
    (m : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hnm : zLe n m) (hqp : pge q p) : vge (uns1 q m) (Uns p n) := by
  exact vge_trans _ (Uns q m) _ (vge_uns_uns' q m)
    (vge.vge_uns_uns q m p n hnm hqp)

private theorem vge_mix_i_select_aux (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    vge (if Int.lt i Int.zero = true then
        sgn p (zMax (ssize i) (zAdd n z1))
      else uns1 p (zMax (usize i) n)) (I i) := by
  by_cases hneg : Int.lt i Int.zero = true
  · rw [if_pos hneg]
    apply vge_sgn_i'
    · exact zLt_le_vmatch z0 (ssize i) _
        (ssize_pos_select_aux i) (zle_max_l_select_aux _ _)
    · exact is_sgn_mon_vmatch (ssize i) _ i
        (is_sgn_ssize_select_aux i) (zle_max_l_select_aux _ _)
  · rw [if_neg hneg]
    apply vge_uns_i'
    · exact zLe_trans_vmatch z0 (usize i) _
        (usize_pos i) (zle_max_l_select_aux _ _)
    · exact is_uns_mon_vmatch (usize i) _ i
        (is_uns_usize_select_aux i) (zle_max_l_select_aux _ _)

private theorem vge_mix_iu_select_aux (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    vge (if Int.lt i Int.zero = true then
        sgn p (zMax (ssize i) (zAdd n z1))
      else uns1 p (zMax (usize i) n)) (IU i) := by
  by_cases hneg : Int.lt i Int.zero = true
  · rw [if_pos hneg]
    apply vge_sgn_iu'
    · exact zLt_le_vmatch z0 (ssize i) _
        (ssize_pos_select_aux i) (zle_max_l_select_aux _ _)
    · exact is_sgn_mon_vmatch (ssize i) _ i
        (is_sgn_ssize_select_aux i) (zle_max_l_select_aux _ _)
  · rw [if_neg hneg]
    apply vge_uns_iu'
    · exact zLe_trans_vmatch z0 (usize i) _
        (usize_pos i) (zle_max_l_select_aux _ _)
    · exact is_uns_mon_vmatch (usize i) _ i
        (is_uns_usize_select_aux i) (zle_max_l_select_aux _ _)

private theorem vge_sgn_i_max_select_aux (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    vge (sgn p (zMax (ssize i) n)) (I i) := by
  apply vge_sgn_i'
  · exact zLt_le_vmatch z0 (ssize i) _
      (ssize_pos_select_aux i) (zle_max_l_select_aux _ _)
  · exact is_sgn_mon_vmatch (ssize i) _ i
      (is_sgn_ssize_select_aux i) (zle_max_l_select_aux _ _)

private theorem vge_sgn_iu_max_select_aux (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    vge (sgn p (zMax (ssize i) n)) (IU i) := by
  apply vge_sgn_iu'
  · exact zLt_le_vmatch z0 (ssize i) _
      (ssize_pos_select_aux i) (zle_max_l_select_aux _ _)
  · exact is_sgn_mon_vmatch (ssize i) _ i
      (is_sgn_ssize_select_aux i) (zle_max_l_select_aux _ _)

private theorem vge_uns_mix_select_aux (p : aptr)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : int) :
    vge (if Int.lt i Int.zero = true then
        sgn p (zMax (ssize i) (zAdd n z1))
      else uns1 p (zMax (usize i) n)) (Uns p n) := by
  by_cases hneg : Int.lt i Int.zero = true
  · rw [if_pos hneg]
    exact vge_sgn_uns_select_aux p _ p n
      (zlt_max_add_one_r_select_aux _ _) (pge.pge_refl p)
  · rw [if_neg hneg]
    exact vge_uns_uns_select_aux p _ p n
      (zle_max_r_select_aux _ _) (pge.pge_refl p)

private theorem vge_lub_l_select_aux : ∀ cfg x y, vge (vlub cfg x y) x := by
  intro cfg x y
  cases x with
  | Vbot => simpa only [vlub] using vge.bot y
  | I i =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (I i)
      | I j => simpa only [vlub] using vge_vlub_int_i_select_aux i j
      | IU j =>
          simpa only [vlub] using
            vge_trans _ (IU i) _ (vge_vlub_int_iu_select_aux i j) (vge.iuInt i)
      | Uns p n => simpa only [vlub] using vge_mix_i_select_aux p n i
      | Sgn p n => simpa only [vlub] using vge_sgn_i_max_select_aux p n i
      | L _ => simpa only [vlub, ntop] using vge.numInt Pbot i
      | F _ => simpa only [vlub, ntop] using vge.numInt Pbot i
      | FS _ => simpa only [vlub, ntop] using vge.numInt Pbot i
      | Num p => simpa only [vlub] using vge.numInt p i
      | Ptr p => simpa only [vlub] using vge.ifptrInt (plub p (int_provenance cfg i)) i
      | Ifptr p => simpa only [vlub] using vge.ifptrInt (plub p (int_provenance cfg i)) i
  | IU i =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (IU i)
      | I j => simpa only [vlub] using vge_vlub_int_iu_select_aux i j
      | IU j => simpa only [vlub] using vge_vlub_int_iu_select_aux i j
      | Uns p n => simpa only [vlub] using vge_mix_iu_select_aux p n i
      | Sgn p n => simpa only [vlub] using vge_sgn_iu_max_select_aux p n i
      | L _ => simpa only [vlub, ntop] using vge.numIU Pbot i
      | F _ => simpa only [vlub, ntop] using vge.numIU Pbot i
      | FS _ => simpa only [vlub, ntop] using vge.numIU Pbot i
      | Num p => simpa only [vlub] using vge.numIU p i
      | Ptr p => simpa only [vlub] using vge.ifptrIU (plub p (int_provenance cfg i)) i
      | Ifptr p => simpa only [vlub] using vge.ifptrIU (plub p (int_provenance cfg i)) i
  | Uns p n =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (Uns p n)
      | I i => simpa only [vlub] using vge_uns_mix_select_aux p n i
      | IU i => simpa only [vlub] using vge_uns_mix_select_aux p n i
      | Uns q m =>
          simpa only [vlub] using
            vge.vge_uns_uns (plub p q) (zMax n m) p n
              (zle_max_l_select_aux n m) (pge_lub_l p q)
      | Sgn q m =>
          simpa only [vlub] using
            vge_sgn_uns_select_aux (plub p q) (zMax (zAdd n z1) m) p n
              (zlt_max_add_one_l_select_aux n m) (pge_lub_l p q)
      | L _ => simpa only [vlub] using vge.numUns p p n (pge.pge_refl p)
      | F _ => simpa only [vlub] using vge.numUns p p n (pge.pge_refl p)
      | FS _ => simpa only [vlub] using vge.numUns p p n (pge.pge_refl p)
      | Num q => simpa only [vlub] using vge.numUns (plub p q) p n (pge_lub_l p q)
      | Ptr q => simpa only [vlub] using vge.ifptrUns (plub p q) p n (pge_lub_l p q)
      | Ifptr q => simpa only [vlub] using vge.ifptrUns (plub p q) p n (pge_lub_l p q)
  | Sgn p n =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (Sgn p n)
      | I i =>
          simpa only [vlub] using
            vge_sgn_sgn_select_aux p (zMax (ssize i) n) p n
              (zle_max_r_select_aux _ _) (pge.pge_refl p)
      | IU i =>
          simpa only [vlub] using
            vge_sgn_sgn_select_aux p (zMax (ssize i) n) p n
              (zle_max_r_select_aux _ _) (pge.pge_refl p)
      | Uns q m =>
          simpa only [vlub] using
            vge_sgn_sgn_select_aux (plub p q) (zMax n (zAdd m z1)) p n
              (zle_max_l_select_aux _ _) (pge_lub_l p q)
      | Sgn q m =>
          simpa only [vlub] using
            vge_sgn_sgn_select_aux (plub p q) (zMax n m) p n
              (zle_max_l_select_aux _ _) (pge_lub_l p q)
      | L _ => simpa only [vlub] using vge.numSgn p p n (pge.pge_refl p)
      | F _ => simpa only [vlub] using vge.numSgn p p n (pge.pge_refl p)
      | FS _ => simpa only [vlub] using vge.numSgn p p n (pge.pge_refl p)
      | Num q => simpa only [vlub] using vge.numSgn (plub p q) p n (pge_lub_l p q)
      | Ptr q => simpa only [vlub] using vge.ifptrSgn (plub p q) p n (pge_lub_l p q)
      | Ifptr q => simpa only [vlub] using vge.ifptrSgn (plub p q) p n (pge_lub_l p q)
  | L i =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (L i)
      | I _ => simpa only [vlub, ntop] using vge.numLong Pbot i
      | IU _ => simpa only [vlub, ntop] using vge.numLong Pbot i
      | Uns p _ => simpa only [vlub] using vge.numLong p i
      | Sgn p _ => simpa only [vlub] using vge.numLong p i
      | L j =>
          change vge (if Int64.eq i j = true then L i else ntop) (L i)
          by_cases h : Int64.eq i j = true
          · rw [if_pos h]
            exact vge.long i
          · rw [if_neg h]
            exact vge.numLong Pbot i
      | F _ => simpa only [vlub, ntop] using vge.numLong Pbot i
      | FS _ => simpa only [vlub, ntop] using vge.numLong Pbot i
      | Num p => simpa only [vlub] using vge.numLong p i
      | Ptr p => simpa only [vlub] using vge.ifptrLong (plub p (long_provenance cfg i)) i
      | Ifptr p => simpa only [vlub] using vge.ifptrLong (plub p (long_provenance cfg i)) i
  | F f =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (F f)
      | I _ => simpa only [vlub, ntop] using vge.numFloat Pbot f
      | IU _ => simpa only [vlub, ntop] using vge.numFloat Pbot f
      | Uns p _ => simpa only [vlub] using vge.numFloat p f
      | Sgn p _ => simpa only [vlub] using vge.numFloat p f
      | L _ => simpa only [vlub, ntop] using vge.numFloat Pbot f
      | F g =>
          change vge (if f = g then F f else ntop) (F f)
          by_cases h : f = g
          · rw [if_pos h]
            exact vge.float f
          · rw [if_neg h]
            exact vge.numFloat Pbot f
      | FS _ => simpa only [vlub, ntop] using vge.numFloat Pbot f
      | Num p => simpa only [vlub] using vge.numFloat p f
      | Ptr p => simpa only [vlub] using vge.ifptrFloat p f
      | Ifptr p => simpa only [vlub] using vge.ifptrFloat p f
  | FS f =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (FS f)
      | I _ => simpa only [vlub, ntop] using vge.numSingle Pbot f
      | IU _ => simpa only [vlub, ntop] using vge.numSingle Pbot f
      | Uns p _ => simpa only [vlub] using vge.numSingle p f
      | Sgn p _ => simpa only [vlub] using vge.numSingle p f
      | L _ => simpa only [vlub, ntop] using vge.numSingle Pbot f
      | F _ => simpa only [vlub, ntop] using vge.numSingle Pbot f
      | FS g =>
          change vge (if f = g then FS f else ntop) (FS f)
          by_cases h : f = g
          · rw [if_pos h]
            exact vge.single f
          · rw [if_neg h]
            exact vge.numSingle Pbot f
      | Num p => simpa only [vlub] using vge.numSingle p f
      | Ptr p => simpa only [vlub] using vge.ifptrSingle p f
      | Ifptr p => simpa only [vlub] using vge.ifptrSingle p f
  | Num p =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (Num p)
      | I _ => simpa only [vlub] using vge_refl_select_aux (Num p)
      | IU _ => simpa only [vlub] using vge_refl_select_aux (Num p)
      | Uns q _ => simpa only [vlub] using vge.numNum (plub p q) p (pge_lub_l p q)
      | Sgn q _ => simpa only [vlub] using vge.numNum (plub p q) p (pge_lub_l p q)
      | L _ => simpa only [vlub] using vge_refl_select_aux (Num p)
      | F _ => simpa only [vlub] using vge_refl_select_aux (Num p)
      | FS _ => simpa only [vlub] using vge_refl_select_aux (Num p)
      | Num q => simpa only [vlub] using vge.numNum (plub p q) p (pge_lub_l p q)
      | Ptr q => simpa only [vlub] using vge.ifptrNum (plub p q) p (pge_lub_l p q)
      | Ifptr q => simpa only [vlub] using vge.ifptrNum (plub p q) p (pge_lub_l p q)
  | Ptr p =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (Ptr p)
      | I i => simpa only [vlub] using vge.ifptrPtr (plub p (int_provenance cfg i)) p (pge_lub_l _ _)
      | IU i => simpa only [vlub] using vge.ifptrPtr (plub p (int_provenance cfg i)) p (pge_lub_l _ _)
      | Uns q _ => simpa only [vlub] using vge.ifptrPtr (plub p q) p (pge_lub_l p q)
      | Sgn q _ => simpa only [vlub] using vge.ifptrPtr (plub p q) p (pge_lub_l p q)
      | L i => simpa only [vlub] using vge.ifptrPtr (plub p (long_provenance cfg i)) p (pge_lub_l _ _)
      | F _ => simpa only [vlub] using vge.ifptrPtr p p (pge.pge_refl p)
      | FS _ => simpa only [vlub] using vge.ifptrPtr p p (pge.pge_refl p)
      | Num q => simpa only [vlub] using vge.ifptrPtr (plub p q) p (pge_lub_l p q)
      | Ptr q => simpa only [vlub] using vge.ptrPtr (plub p q) p (pge_lub_l p q)
      | Ifptr q => simpa only [vlub] using vge.ifptrPtr (plub p q) p (pge_lub_l p q)
  | Ifptr p =>
      cases y with
      | Vbot => simpa only [vlub] using vge_refl_select_aux (Ifptr p)
      | I i => simpa only [vlub] using vge.ifptrIfptr (plub p (int_provenance cfg i)) p (pge_lub_l _ _)
      | IU i => simpa only [vlub] using vge.ifptrIfptr (plub p (int_provenance cfg i)) p (pge_lub_l _ _)
      | Uns q _ => simpa only [vlub] using vge.ifptrIfptr (plub p q) p (pge_lub_l p q)
      | Sgn q _ => simpa only [vlub] using vge.ifptrIfptr (plub p q) p (pge_lub_l p q)
      | L i => simpa only [vlub] using vge.ifptrIfptr (plub p (long_provenance cfg i)) p (pge_lub_l _ _)
      | F _ => simpa only [vlub] using vge_refl_select_aux (Ifptr p)
      | FS _ => simpa only [vlub] using vge_refl_select_aux (Ifptr p)
      | Num q => simpa only [vlub] using vge.ifptrIfptr (plub p q) p (pge_lub_l p q)
      | Ptr q => simpa only [vlub] using vge.ifptrIfptr (plub p q) p (pge_lub_l p q)
      | Ifptr q => simpa only [vlub] using vge.ifptrIfptr (plub p q) p (pge_lub_l p q)

private theorem vmatch_lub_l_select_aux (cfg : CompilerConfig) (bc : block_classification)
    (v : val) (x y : aval) (h : vmatch bc v x) :
    vmatch bc v (vlub cfg x y) := by
  exact vmatch_ge bc v (vlub cfg x y) x (vge_lub_l_select_aux cfg x y) h

private theorem vmatch_lub_r_select_aux (cfg : CompilerConfig) (bc : block_classification)
    (v : val) (x y : aval) (h : vmatch bc v y) :
    vmatch bc v (vlub cfg x y) := by
  rw [vlub_comm cfg x y]
  exact vmatch_lub_l_select_aux cfg bc v y x h

theorem select_sound : select_soundStatement := by
  intro cfg bc ob v w ab x y ty hcm hv hw
  cases hcm with
  | noneCase =>
      simp [CompCert4Lean.Common.Values.Val.select, select, ntop]
      exact vmatch.numUndef Pbot
  | justCase b =>
      cases b <;>
        simp [CompCert4Lean.Common.Values.Val.select, select] <;>
        apply vnormalize_type_sound <;> assumption
  | maybeNone b =>
      simp [CompCert4Lean.Common.Values.Val.select, select]
      exact add_undef_undef bc _
  | maybeSome b =>
      cases b <;>
        simp [CompCert4Lean.Common.Values.Val.select, select] <;>
        apply add_undef_sound <;>
        apply vnormalize_type_sound <;> assumption
  | topCase ob =>
      cases ob with
      | none =>
          simp [CompCert4Lean.Common.Values.Val.select, select]
          exact add_undef_undef bc _
      | some b =>
          cases b with
          | false =>
              simp [CompCert4Lean.Common.Values.Val.select, select]
              apply add_undef_sound
              apply vnormalize_type_sound
              exact vmatch_lub_r_select_aux cfg bc w x y hw
          | true =>
              simp [CompCert4Lean.Common.Values.Val.select, select]
              apply add_undef_sound
              apply vnormalize_type_sound
              exact vmatch_lub_l_select_aux cfg bc v x y hv

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem poffset_ge : poffset_geStatement := by
  intro p
  cases p <;> simp only [poffset] <;> constructor

theorem poffset_monotone : poffset_monotoneStatement := by
  intro p q hpq
  cases hpq with
  | pge_top _ => exact pge.pge_top _
  | bot _ => exact pge.bot _
  | pge_refl _ => exact pge.pge_refl _
  | gloGl id ofs => exact pge.pge_refl _
  | globGl id ofs => exact pge.globGlo id
  | globGlo id => exact pge.globGlo id
  | nsGl id ofs => exact pge.nsGlo id
  | nsGlo id => exact pge.nsGlo id
  | nsGlob => exact pge.nsGlob
  | stackStk ofs => exact pge.pge_refl _

theorem provenance_monotone : provenance_monotoneStatement := by
  intro x y hxy
  cases hxy <;> simp only [provenance] <;>
    first
    | assumption
    | exact pge.bot _
    | exact pge.pge_refl _
    | exact poffset_monotone _ _ (by assumption)
    | exact pge_trans _ _ (poffset_ge _) _ (by assumption)

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem provenance_ifptr_ge : provenance_ifptr_geStatement := by
  intro p q hpq
  simp only [provenance]
  exact pge_trans _ _ (poffset_ge p) _ hpq

theorem val_of_aval_sound : val_of_aval_soundStatement := by
  intro bc v a h
  cases h <;> constructor

theorem list_val_of_aval_sound : list_val_of_aval_soundStatement := by
  intro bc vl al h
  induction h with
  | nil => exact CompCert4Lean.Common.Values.Val.lessdef_list_nil
  | cons v a hhead htail ih =>
      exact CompCert4Lean.Common.Values.Val.lessdef_list_cons _ _ _ _
        (val_of_aval_sound bc v a hhead) ih

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem aval_of_val_sound : aval_of_val_soundStatement := by
  intro bc v a h
  cases v with
  | Vundef => simp [aval_of_val] at h
  | Vint i =>
      have ha : I i = a := by simpa [aval_of_val] using h
      cases ha
      exact vmatch.vmatch_i i
  | Vlong i =>
      have ha : L i = a := by simpa [aval_of_val] using h
      cases ha
      exact vmatch.long i
  | Vfloat f =>
      have ha : F f = a := by simpa [aval_of_val] using h
      cases ha
      exact vmatch.float f
  | Vsingle f =>
      have ha : FS f = a := by simpa [aval_of_val] using h
      cases ha
      exact vmatch.single f
  | Vptr b ofs => simp [aval_of_val] at h

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem loadbytes_load_ext : loadbytes_load_extStatement := by
  intro b m m' h_ext chunk ofs v hload
  obtain ⟨bytes, hbytes, hval⟩ :=
    CompCert4Lean.Common.Memory.Mem.load_loadbytes chunk m' b ofs v hload
  have hvalid :=
    CompCert4Lean.Common.Memory.Mem.load_valid_access m' chunk b ofs v hload
  have hnonneg : zLe z0
      (CompCert4Lean.Common.Memdata.size_chunk chunk) :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zorder.Zlt_le_weak_proof _ _
      (CompCert4Lean.Common.Memdata.size_chunk_pos chunk)
  have hbytes' := h_ext ofs (CompCert4Lean.Common.Memdata.size_chunk chunk)
      bytes hbytes hnonneg
  have hload_m : CompCert4Lean.Common.Memory.Mem.load chunk m b ofs =
      some (CompCert4Lean.Common.Memdata.decode_val chunk bytes) :=
    CompCert4Lean.Common.Memory.Mem.loadbytes_load chunk m b ofs bytes hbytes' hvalid.2
  rw [← hval] at hload_m
  exact hload_m

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem smatch_ext : smatch_extStatement := by
  intro bc m b p m' hsm hloadbytes
  rcases hsm with ⟨hload, hfrag⟩
  constructor
  · intro chunk ofs v h
    apply hload chunk ofs v
    exact loadbytes_load_ext b m m' hloadbytes chunk ofs v h
  · intro ofs b' ofs' q i h
    apply hfrag ofs b' ofs' q i
    apply hloadbytes ofs z1
      [CompCert4Lean.Common.Memdata.Fragment
        (CompCert4Lean.Common.Values.Vptr b' ofs') q i] h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1
    have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by rfl
    have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z1 = 1 := by rfl
    rw [hz0, hz1]
    omega

end CompCert4Lean.Backend.ValueDomain

namespace CompCert4Lean.Backend.ValueDomain

theorem smatch_inv : smatch_invStatement := by
  intro bc m b p m' hsm heq
  apply smatch_ext bc m b p m' hsm
  intro ofs n bytes hload hn
  rw [heq ofs n hn] at hload
  exact hload

end CompCert4Lean.Backend.ValueDomain
