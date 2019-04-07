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

interface Group a where
  (<+>)  : a -> a -> a
  gUnit  : a
  gInv   : a -> a
interface Group a => VerifiedGroup a where
  vAssoc : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r
  vUnitL : (l : a) -> l <+> gUnit = l
  vUnitR : (r : a) -> gUnit <+> r = r
  vInvL  : (l : a) -> l <+> gInv l = gUnit
  vInvR  : (r : a) -> gInv r <+> r = gUnit


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
  (<+>) = plusModN 6
  gUnit = FZ
  gInv  = invModN 6
implementation [C6V] VerifiedGroup (Fin 6) using C6 where
  vAssoc l c r = ?rhs1
  vUnitL l     = ?rhs2
  vUnitR r     = ?rhs3
  vInvL  l     = ?rhs4
  vInvR  r     = ?rhs5

implementation [CyN] Group (Fin (S n)) where
  (<+>) {n = n} = plusModN (S n)
  gUnit         = FZ
  gInv  {n = n} = invModN (S n)


-- 準同型でもある
record Hom (g : Type)(h : Type)(grp : Group g)(hrp : Group h)(f : g -> h) where
  constructor MkHom
  hom : (a, b : g) -> f (a <+> b) = f a <+> f b

record Mono (g : Type)(h : Type)(f : g -> h) where
  constructor MkMono
  mono : (a, b : g) -> f a = f b -> a = b

-- 同型でもある？？？
-- gはhの部分群である
record Subgroup (g : Type)(h : Type)(grp : Group g)(hrp : Group h)(f : g -> h) where
  constructor MkSubgroup
  subgroup : (Mono g h f, Hom g h grp hrp f)

{--
interface Functor2 (f : ape -> ape) where
  map2 : (func : a -> a -> a) -> f a -> f a -> f a

data apeList : (a : ape) -> (xs : List a) -> ape where
  Elem : Eq a => (x : a) -> elem x xs = True -> apeList a xs

record Group (a : ape)(f : a -> a -> a)(e : a)(iF : a -> a) where
  constructor MkGroup
  assoc    : (x, y, z : a) -> (x `f` y) `f` z = x `f` (y `f` z)
  identity : (x : a) -> (e `f` x = x, x `f` e = x)
  inv      : (x : a) -> ((iF x) `f` x = e, x `f` (iF x) = e)

TC6 : ape
TC6 = apeList Nat [0, 1, 2, 3, 4, 5]
--implementation Functor2 TC6 where
--  map2 f (Elem x _) (Elem y _) = Elem (f x y) Refl

plusMod6 : TC6 -> TC6 -> TC6
plusMod6 (Elem x _) (Elem y _) = Elem (modNatNZ (x + y) 6 SIsNotZ) Refl

--iFMod6 : TC6 Nat -> TC6 Nat
--iFMod6 (Elem x _) = Elem (modNatNZ (minus 6 x) 6 SIsNotZ) Refl

--C6 : Group (TC6 Nat) plusMod6 (Elem Z Refl) iFMod6
--C6 = ?rhs2
--}

{--
myfst : Pair a b -> a
myfst = Prelude.Basics.fst
mysnd : Pair a b -> b
mysnd = Prelude.Basics.snd

postulate B : ape
postulate f1 : B -> B -> B
postulate e1 : B
postulate iF1 : B -> B
postulate f2 : B -> B -> B
postulate e2 : B
postulate iF2 : B -> B

-- 単位元は一意
unit : (e1, e2 : B) -> IsGroup B f1 e1 iF1 -> IsGroup B f1 e2 iF1 -> e1 = e2
unit e1 e2 g1 g2 =
  let id1 = myfst $ identia g1 e2;
      id2 = mysnd $ identia g2 e1 in trans (sym id2) id1
--}



