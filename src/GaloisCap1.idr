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

-- 群の定義
infixl 6 <+>
interface Group a where
  (<+>)  : a -> a -> a
  gUnit  : a
  gInv   : a -> a
  vAssoc : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r
  vUnit  : (c : a) -> (c <+> gUnit = c, gUnit <+> c = c)
  vInv   : (c : a) -> (c <+> gInv c = gUnit, gInv c <+> c = gUnit)

-- 準同型
record Hom (g : Type)(h : Type)(grp : Group g)(hrp : Group h)(f : g -> h) where
  constructor MkHom
  -- 左辺の<+>はgrpのもの、右辺の<+>はhrpのもの
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

implementation [CyN] Group (Fin n) where
  (<+>) {n = n}     = plusModN n
  gUnit {n = Z    } = idris_crash "no constructor!"
  gUnit {n = (S n)} = FZ
  gInv  {n = n}     = invModN n
  vAssoc l c r      = ?rhs1
  vUnit  r          = ?rhs2
  vInv   r          = ?rhs3
-- ----------------------------------

cyclicToCyclic : (n, k : Nat) -> Fin (S n) -> Fin (S (mult k (S n) + n))
cyclicToCyclic n Z     = id -- idにするところがミソ
cyclicToCyclic n (S k) = \_ =>
  let y = S (mult (S k) (S n) + n) in fromNat y

-- ◆定理1.5 巡回群の部分群は巡回群である
-- 部分群の位数(S n)が、元の群の位数(S k)*(S n)の約数である事を仮定した
-- S (mult k (S n) + n) = (S k) * (S n)
cyclicSubCyclic : (n : Nat)
  -> ((k : Nat) -> Subgroup (Fin (S n)) (Fin (S (mult k (S n) + n))) subGrp CyN (cyclicToCyclic n k))
    -> Iso (Fin (S n)) (Fin (S n)) subGrp CyN (cyclicToCyclic n Z)
cyclicSubCyclic n fSubG = MkIso (fSubG Z) (MkEpi (\z => (z ** Refl)))


-- 既約剰余類群
-- 元かどうかは、外からのBool値で判断する
data FinBool : (n : Nat) -> Type where
  Fb : Fin n -> Bool -> FinBool n

multModN : (n : Nat) -> Fin n -> Fin n -> Fin n
multModN Z     finZ    _ = absurd finZ
multModN (S k) finX finY =
  let n = S k;
      x = toNat finX;
      y = toNat finY
  in fromNat $ modNatNZ (x * y) n SIsNotZ

multModNFb : (n : Nat) -> FinBool n -> FinBool n -> FinBool n
multModNFb Z     (Fb finZ _    ) _               = absurd finZ
multModNFb (S _) (Fb _    False) _               = Fb FZ False
multModNFb (S _) (Fb _    True ) (Fb _    False) = Fb FZ False
multModNFb (S k) (Fb finX True ) (Fb finY True ) = Fb (multModN (S k) finX finY) True

invModNFb : (n : Nat) -> FinBool n -> FinBool n
invModNFb Z     (Fb finZ _    ) = absurd finZ
invModNFb (S _) (Fb _    False) = Fb FZ False
invModNFb (S k) (Fb finX True ) = Fb (invModN (S k) finX) True

implementation [Mgm] Group (FinBool n) where
  (<+>) {n = n}     = multModNFb n
  gUnit {n = Z    } = idris_crash "no constructor!"
  gUnit {n = (S n)} = Fb FZ True
  gInv  {n = n}     = invModNFb n
  vAssoc l c r      = ?rhs4
  vUnit    c        = ?rhs5
  vInv     c        = ?rhs6
-- ----------------------------------


-- 群の直積
implementation [GPr] (Group a, Group b) => Group (a, b) where
  (x, y) <+> (z, u) = (x <+> z, y <+> u)
  gUnit             = (gUnit, gUnit)
  gInv (x, y)       = (gInv x, gInv y)
  vAssoc l c r      = ?rhs7
  vUnit    c        = ?rhs8
  vInv     c        = ?rhs9
-- ----------------------------------


-- ◆定理1.9 (Z/(p^e)(q^f)Z)* ≡ (Z/(p^e)Z)* × (Z/(q^f)Z)*
fFinBoolToGPr : (FinBool ((power (S p) (S e))*(power (S q) (S f))))
  -> (Fin (power (S p) (S e)), Fin (power (S q) (S f)))
theorem1_9 : (p, q, e, f : Nat)
  -> Group (Fin (power (S p) (S e)))
    -> Group (Fin (power (S q) (S f)))
      -> Iso
           (FinBool ((power (S p) (S e))*(power (S q) (S f))))
           (Fin (power (S p) (S e)), Fin (power (S q) (S f))) Mgm GPr fFinBoolToGPr

-- ◆定理1.18 (Z/2^nZ)*は巡回群の直積に同型である
-- (Z/2^nZ)* ≡ (Z/2^(n-2)Z) × (Z/2Z)
fTheorem1_18 : (FinBool (power 2 (S (S n)))) -> (FinBool (power 2 n), Fin 2)
theorem1_18 : (n : Nat)
  -> Group (FinBool (power 2 n))
    -> Group (Fin 2)
      -> Iso
           (FinBool (power 2 (S (S n))))
           (FinBool (power 2 n), Fin 2) Mgm GPr fTheorem1_18

-- ◆定理1.19 (Z/奇素数p^nZ)*は巡回群の直積に同型である
-- (Z/p^nZ)* ≡ (Z/p^(n-1)Z) × (Z/(p-1)Z)
fTheorem1_19 : (FinBool (power (S p) (S n))) -> (FinBool (power (S p) n), Fin p)
theorem1_19 : (p, n : Nat)
  -> Group (FinBool (power (S p) n))
    -> Group (Fin p)
      -> Iso
           (FinBool (power (S p) (S n)))
           (FinBool (power (S p) n), Fin p) Mgm GPr fTheorem1_19

-- ◆定理1.20 既約剰余類群は巡回群の直積に同型である
--mgmProduct :



