module GaloisCap1

-- > idris -p base
import Data.Fin

%default total
-- %auto_implicits on

{--
/libs/prelude/Prelude/Algebra.idr
interface Semigroup ty where
  (<+>) : ty -> ty -> ty
interface Semigroup ty => Monoid ty where
  neutral : ty
/libs/contrib/Control/Algebra.idr
interface Monoid a => Group a where
  inverse : a -> a
/libs/contrib/Interfaces/Verified.idr
interface Semigroup a => VerifiedSemigroup a where
  semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r
interface (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  monoidNeutralIsNeutralL : (l : a) -> l <+> Algebra.neutral = l
  monoidNeutralIsNeutralR : (r : a) -> Algebra.neutral <+> r = r
interface (VerifiedMonoid a, Group a) => VerifiedGroup a where
  groupInverseIsInverseL : (l : a) -> l <+> inverse l = Algebra.neutral
  groupInverseIsInverseR : (r : a) -> inverse r <+> r = Algebra.neutrals
VerifiedGroup ZZ using PlusZZMonoidV where
  groupInverseIsInverseL k = rewrite sym $ multCommutativeZ (NegS 0) k in
                             rewrite multNegLeftZ 0 k in
                             rewrite multOneLeftNeutralZ k in
                             plusNegateInverseLZ k
  groupInverseIsInverseR k = rewrite sym $ multCommutativeZ (NegS 0) k in
                             rewrite multNegLeftZ 0 k in
                             rewrite multOneLeftNeutralZ k in
                             plusNegateInverseRZ k
--}

-- ----- 群の定義 -----
infixl 6 <+>
interface Group a where
  (<+>)  : a -> a -> a
  gUnit  : a
  gInv   : a -> a
  vAssoc : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r
  vUnit  : (r : a) -> (r <+> gUnit = r, gUnit <+> r = r)
  vInv   : (r : a) -> (r <+> gInv r = gUnit, gInv r <+> r = gUnit)

-- 準同型
record Hom (g : Type)(h : Type)(grp : Group g)(hrp : Group h)(f : g -> h) where
  constructor MkHom
  hom : (a, b : g) -> f (a <+> b) = f a <+> f b

-- 単射
record Mono (g : Type)(h : Type)(f : g -> h) where
  constructor MkMono
  mono : (a, b : g) -> f a = f b -> a = b

-- 全射
record Epi (g : Type)(h : Type)(f : g -> h) where
  constructor MkEpi
  epi : (z : h) -> (a ** f a = z)

-- gはhの部分群である
record Subgroup (g : Type)(h : Type)(grp : Group g)(hrp : Group h)(f : g -> h) where
  constructor MkSubgroup
  sHom  : Hom g h grp hrp f
  sMono : Mono g h f

-- gとhは同型である
record Iso (g : Type)(h : Type)(grp : Group g)(hrp : Group h)(f : g -> h) where
  constructor MkIso
  iSubgroup : Subgroup g h grp hrp f
  iEpi      : Epi g h f
-- ----------------------------------


-- 巡回群
plusModN : (n : Nat) -> Fin n -> Fin n -> Fin n
plusModN Z     finZ    _ = absurd finZ
plusModN (S k) finX finY =
  let n = S k;
      x = toNat finX;
      y = toNat finY
  in fromNat $ modNatNZ (x + y) n SIsNotZ

invModN : (n : Nat) -> Fin n -> Fin n
invModN Z     finZ = absurd finZ
invModN (S k) finX =
  let n = S k;
      x = toNat finX
  in fromNat $ modNatNZ (minus n x) n SIsNotZ

implementation [C6] Group (Fin 6) where
  (<+>)        = plusModN 6
  gUnit        = FZ
  gInv         = invModN 6
  vAssoc l c r = ?rhs1
  vUnit  r     = ?rhs2
  vInv   r     = ?rhs3

implementation [CyN] Group (Fin (S n)) where
  (<+>) {n = n} = plusModN (S n)
  gUnit         = FZ
  gInv  {n = n} = invModN (S n)
  vAssoc l c r  = ?rhs4
  vUnit  r      = ?rhs5
  vInv   r      = ?rhs6

{--
-- 定理1.5 巡回群の部分群は巡回群である
-- 1. 巡回群の部分群は、巡回群と同型
-- LTE k n
cycleSubCycle1 : (n, k : Nat)
  -> Subgroup subG (Fin (S n)) subGrp CyN f1 -> LTE k n
    -> Iso (Fin (S k)) subG CyN subGrp f2
cycleSubCycle1 Z Z (MkSubgroup (MkHom funcHom) (MkMono funcMono)) prfLTE
  = MkIso (MkSubgroup (MkHom ?rhs7) (MkMono ?rhs8)) (MkEpi ?rhs9)
cycleSubCycle1 Z (S k) (MkSubgroup (MkHom funcHom) (MkMono funcMono)) prfLTE
  = absurd prfLTE --MkIso (MkSubgroup (MkHom ?rhs7) (MkMono ?rhs8)) (MkEpi ?rhs9)

cycleSubCycle1 (S n) k (MkSubgroup (MkHom funcHom) (MkMono funcMono)) prfLTE
  = MkIso (MkSubgroup (MkHom ?rhs7_2) (MkMono ?rhs8_2)) (MkEpi ?rhs9_2)


fZZ : subG -> Fin 1
fZZ _ = FZ

cycleSubCycle2_Z_Z :
  Subgroup subG (Fin (S Z)) subGrp CyN fzz -> LTE Z Z
    -> Hom subG (Fin (S Z)) subGrp CyN fzz
cycleSubCycle2_Z_Z (MkSubgroup prfHom (MkMono funcMono)) prfLTE
  = prfHom

cycleSubCycle2 : (k, n : Nat)
  -> Subgroup subG (Fin (S n)) subGrp CyN f1 -> LTE k n
    -> Iso subG (Fin (S k)) subGrp CyN f2
cycleSubCycle2 Z Z prfSubgroup prfLTE
  = MkIso (MkSubgroup ?rhs10 (MkMono ?rhs11)) (MkEpi ?rhs12)
cycleSubCycle2 (S k) Z _ prfLTE
  = absurd prfLTE --MkIso (MkSubgroup (MkHom ?rhs10) (MkMono ?rhs11)) (MkEpi ?rhs12)

cycleSubCycle2 k (S n) (MkSubgroup (MkHom funcHom) (MkMono funcMono)) prfLTE
  = MkIso (MkSubgroup (MkHom ?rhs13) (MkMono ?rhs14)) (MkEpi ?rhs15)
--cycleSubCycle2 (S k) (S n) prfSubgroup (LTESucc prfLTE)
--  = cycleSubCycle2 k n prfSubgroup prfLTE
--}

{--
cycleSubCycle2 : (k, n : Nat)
  -> Subgroup (Fin (S k)) (Fin (S n)) subGrp CyN f -> LTE k n
    -> Iso (Fin (S k)) (Fin (S k)) subGrp CyN Prelude.Basics.id
cycleSubCycle2 k n (MkSubgroup (MkHom funcHom) (MkMono funcMono)) prfLTE
  = MkIso (MkSubgroup (MkHom prfFuncHom) (MkMono (\_, _, prf => prf))) (MkEpi (\z => (z ** Refl)))
    where
      prfFuncHom : (a : Fin (S k)) -> (b : Fin (S k)) -> a <+> b = plusModN (S k) a b
      prfFuncHom a b = ?rhs7
--}

cycleSubCycle2 : (n, k : Nat)
  -> Subgroup (Fin (S n)) (Fin ((S k)*(S n))) subGrp CyN f
    -> Iso (Fin (S n)) (Fin (S n)) subGrp CyN Prelude.Basics.id
cycleSubCycle2 n Z (MkSubgroup (MkHom funcHom) (MkMono funcMono))
  = MkIso (MkSubgroup (MkHom ?rhs7) (MkMono (\_, _, prf => prf))) (MkEpi (\z => (z ** Refl)))
cycleSubCycle2 n (S k) (MkSubgroup (MkHom funcHom) (MkMono funcMono))
  = MkIso (MkSubgroup (MkHom prfFuncHom) (MkMono (\_, _, prf => prf))) (MkEpi (\z => (z ** Refl)))
    where
      prfFuncHom : (a : Fin (S n)) -> (b : Fin (S n)) -> a <+> b = plusModN (S n) a b
      prfFuncHom a b = ?rhs8


cycleSubCycle3 : (n, k : Nat)
  -> Hom (Fin (S n)) (Fin ((S k)*(S n))) CyN CyN f
cycleSubCycle3 n Z     = MkHom ?rhs9
cycleSubCycle3 n (S k) = let hoge = hom $ cycleSubCycle3 n k in MkHom ?rhs10


