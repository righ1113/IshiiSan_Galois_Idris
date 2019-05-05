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

implementation [CyN] Group (Fin (S n)) where
  (<+>) {n = n} = plusModN (S n)
  gUnit         = FZ
  gInv  {n = n} = invModN (S n)
  vAssoc l c r  = ?rhs1
  vUnit    c    = ?rhs2
  vInv     c    = ?rhs3
-- ----------------------------------


cyclicToCyclic : (n, k : Nat) -> Fin (S n) -> Fin (S (mult k (S n) + n))
cyclicToCyclic n Z     = id -- idにするところがミソ
cyclicToCyclic n (S k) = \_ =>
--  let y = S (n + myMult (S k) (S n)) in fromMaybe ?rhs14 $ natToFin y y
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

implementation [Mgm] Group (FinBool (S n)) where
  (<+>) {n = n} = multModNFb (S n)
  gUnit         = Fb FZ True
  gInv  {n = n} = invModNFb (S n)
  vAssoc l c r  = ?rhs4
  vUnit    c    = ?rhs5
  vInv     c    = ?rhs6
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
-- S (mult k (S n) + n) = (S k) * (S n)
-- S (mult p (S (pred (power (S p) e))) + (pred (power (S p) e))) = power (S p) (S e)
---power (S p) (S e)
---  = mult (S p) $ power (S p) e
---  = mult (S p) $ (S (pred (power (S p) e)))
---  = S (mult p (S (pred (power (S p) e))) + (pred (power (S p) e)))
-- S (mult p (power (S p) e) + (pred (power (S p) e)))
-- S (mult q (power (S q) f) + (pred (power (S q) f)))
-- S (mult (mult p (power (S p) e) + (pred (power (S p) e))) (S (mult q (power (S q) f) + (pred (power (S q) f)))) + (mult q (power (S q) f) + (pred (power (S q) f))))
fFinBoolToGPr : (FinBool (S (mult (mult p (power (S p) e) + (pred (power (S p) e))) (S (mult q (power (S q) f) + (pred (power (S q) f)))) + (mult q (power (S q) f) + (pred (power (S q) f))))))
  -> (Fin (S (mult p (power (S p) e) + (pred (power (S p) e)))), Fin (S (mult q (power (S q) f) + (pred (power (S q) f)))))
theorem1_9 : (p, q, e, f : Nat)
  -> Group (Fin (S (mult p (power (S p) e) + (pred (power (S p) e)))))
    -> Group (Fin (S (mult q (power (S q) f) + (pred (power (S q) f)))))
      -> Iso
           (FinBool (S (mult (mult p (power (S p) e) + (pred (power (S p) e))) (S (mult q (power (S q) f) + (pred (power (S q) f)))) + (mult q (power (S q) f) + (pred (power (S q) f))))))
           (Fin (S (mult p (power (S p) e) + (pred (power (S p) e)))), Fin (S (mult q (power (S q) f) + (pred (power (S q) f))))) Mgm GPr fFinBoolToGPr

-- ◆定理1.18 (Z/2^nZ)*は巡回群の直積に同型である
-- (Z/2^nZ)* ≡ (Z/2^(n-2)Z) × (Z/2Z)
fTheorem1_18 : FinBool (S (mult (S Z) (S (pred (power (S (S Z)) (S n)))) + (pred (power (S (S Z)) (S n)))))
  -> (Fin (S n), Fin (S (S Z)))
theorem1_18 : (n : Nat)
  -> Group (Fin (S n))
    -> Group (Fin (S (S Z)))
      -> Iso
           (FinBool (S (mult (S Z) (S (pred (power (S (S Z)) (S n)))) + (pred (power (S (S Z)) (S n))))))
           (Fin (S n), Fin (S (S Z))) Mgm GPr fTheorem1_18

fTheorem1_19 : FinBool (S (mult (S (S p)) (S (pred (power (S (S (S p))) (S n)))) + (pred (power (S (S (S p))) (S n)))))
  -> (Fin (S (mult (S (S p)) (S (pred (power (S (S (S p))) n))) + (pred (power (S (S (S p))) n)))), Fin (S (S p)))
-- ◆定理1.19 (Z/奇素数p^nZ)*は巡回群の直積に同型である
theorem1_19 : (p, n : Nat)
  -> Group (Fin (S (mult (S (S p)) (S (pred (power (S (S (S p))) n))) + (pred (power (S (S (S p))) n)))))
    -> Group (Fin (S (S p)))
      -> Iso
           (FinBool (S (mult (S (S p)) (S (pred (power (S (S (S p))) (S n)))) + (pred (power (S (S (S p))) (S n))))))
           (Fin (S (mult (S (S p)) (S (pred (power (S (S (S p))) n))) + (pred (power (S (S (S p))) n)))), Fin (S (S p))) Mgm GPr fTheorem1_19

-- ◆定理1.20 既約剰余類群は巡回群の直積に同型である
--mgmProduct :




