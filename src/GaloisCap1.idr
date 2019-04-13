module GaloisCap1

-- > idris -p base
import Data.Fin

%default total
-- %auto_implicits off

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

implementation [CyN] Group (Fin (S n)) where
  (<+>) {n = n} = plusModN (S n)
  gUnit         = FZ
  gInv  {n = n} = invModN (S n)
  vAssoc l c r  = ?rhs4
  vUnit  r      = ?rhs5
  vInv   r      = ?rhs6
-- ----------------------------------


cyclicToCyclic : (n, k : Nat) -> Fin (S n) -> Fin (S (mult k (S n) + n))
cyclicToCyclic n Z     = id --idにするところがミソ
cyclicToCyclic n (S k) = \_ =>
--  let y = S (n + myMult (S k) (S n)) in fromMaybe ?rhs14 $ natToFin y y
  let y = S (mult (S k) (S n) + n) in fromNat y

-- 定理1.5 巡回群の部分群は巡回群である
-- 部分群の位数(S n)が、元の群の位数(S k)*(S n)の約数である事を仮定した
-- S (mult k (S n) + n) = (S k) * (S n)
cyclicSubCyclic : (n : Nat)
  -> ((k : Nat) -> Subgroup (Fin (S n)) (Fin (S (mult k (S n) + n))) subGrp CyN (cyclicToCyclic n k))
    -> Iso (Fin (S n)) (Fin (S n)) subGrp CyN (cyclicToCyclic n Z)
cyclicSubCyclic n fSubG = MkIso (fSubG Z) (MkEpi (\z => (z ** Refl)))



