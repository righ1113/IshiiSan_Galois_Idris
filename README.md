# IshiiSan_Galois_Idris
『ガロア理論の頂を踏む』読書ノート

# 変更履歴
19/04/13　定理1.5をIdrisで証明  
19/04/04　「第1章　整数」読書中、Idrisで群論周りを実装中  

# ゴール
- ピークの定理  

```
方程式f(x) = 0の解が根号で表せる
<=> 方程式f(x) = 0のガロア群が可解群である  
```

を理解する  

# Idris
- Idrisで形式化をおこなう（努力目標）。  
=> 本の全ての定理を、Idrisで証明するのは難しいと判断  
- Idrisでの証明は、本の証明とは全く違うものになる  

# 第1章　「整数」
## 1 最大公約数を求める
## 2 余りの計算
## 3 正六角形を回転させよう
### 定義1.3 群の定義
```idris
infixl 6 <+>
interface Group a where
  (<+>)  : a -> a -> a
  gUnit  : a
  gInv   : a -> a
  vAssoc : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r
  vUnit  : (r : a) -> (r <+> gUnit = r, gUnit <+> r = r)
  vInv   : (r : a) -> (r <+> gInv r = gUnit, gInv r <+> r = gUnit)
```
- 群の台集合の元が、値(1とか)の場合と、演算(30度回転とか)の場合がある。  
混乱の元。  

## 4 群が同じということ
## 5 一部の元でも群になる
### 定理1.5 巡回群の部分群は巡回群である
```idris
-- 定理1.5 巡回群の部分群は巡回群である
-- 部分群の位数(S n)が、元の群の位数(S k)*(S n)の約数である事を仮定した
-- S (mult k (S n) + n) = (S k) * (S n)
cyclicSubCyclic : (n : Nat)
  -> ((k : Nat) -> Subgroup (Fin (S n)) (Fin (S (mult k (S n) + n))) subGrp CyN (cyclicToCyclic n k))
    -> Iso (Fin (S n)) (Fin (S n)) subGrp CyN (cyclicToCyclic n Z)
cyclicSubCyclic n fSubG = MkIso (fSubG Z) (MkEpi (\z => (z ** Refl)))
```

## 6 2つの群から群を作る
## 7 掛け算だって群になる！
## 8 (Z/p^nZ)*は直積で書けるか？
## 9 (Z/pZ)*は、巡回群である
## 10 素数pの原始根は確かにある
## 11 既約剰余類群を解剖する

# 第2章　「群」

# 第3章　「多項式」

# 第4章　「複素数」

# 第5章　「体と自己同型群」

# 第6章　「根号で表す」





