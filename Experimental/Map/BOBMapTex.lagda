\begin{code}[hide]
{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMapTex {k ℓ₁} (order : OrdSet k ℓ₁) where

Order : StrictTotalOrder k k ℓ₁
Order = toStrictTotalOrder order

open import Prelude
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _<_; _≤_) renaming (_⊔_ to max)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Maybe
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Function using (_∘_; _$_; const; case_of_)
open import Relation.Binary.Definitions

open StrictTotalOrder Order renaming (Carrier to Key)
open import Data.Tree.AVL.Key Order public

private
  variable
    ℓ ℓ' ℓₚ ℓₐ : Level
    v : Level

ℕ₂ = Fin 2
pattern 0# = fzero
pattern 1# = fsuc fzero
pattern ## = fsuc (fsuc ())

infixl 6 _⊕_

_⊕_ : ℕ₂ → ℕ → ℕ
0# ⊕ n = n
1# ⊕ n = 1 + n

pred[_⊕_] : ℕ₂ → ℕ → ℕ
pred[ i ⊕ zero  ] = 0
pred[ i ⊕ suc n ] = i ⊕ n

infix 4 _~_⊔_

data _~_⊔_ : ℕ → ℕ → ℕ → Set where
  ~+ : ∀ {n} →     n ~ 1 + n ⊔ 1 + n
  ~0 : ∀ {n} →     n ~ n     ⊔ n
  ~- : ∀ {n} → 1 + n ~ n     ⊔ 1 + n

max~ : ∀ {i j m} → i ~ j ⊔ m → m ~ i ⊔ m
max~ ~+ = ~-
max~ ~0 = ~0
max~ ~- = ~0

~max : ∀ {i j m} → i ~ j ⊔ m → j ~ m ⊔ m
~max ~+ = ~0
~max ~0 = ~0
~max ~- = ~+
\end{code}

\newcommand{\AVLMapIndexedDef}{
\begin{code}
data AVLMapIndexed (V : Set v) (l u : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ₁) where
  leaf : {{@erased l<u : l <⁺ u}} → AVLMapIndexed V l u 0
  node : ∀ {hl hr h}
         → ((k , v) : Key × V)
         → (lm : AVLMapIndexed V l [ k ] hl)
         → (rm : AVLMapIndexed V [ k ] u hr)
         → (bal : hl ~ hr ⊔ h)
         → AVLMapIndexed V l u (suc h)
\end{code}
}


\begin{code}[hide]
module _ {v} {V : Set v} where

  record Cons (l u : Key⁺) (h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor cons
    field
      head : Key × V
      @erased l<u : l <⁺ [ proj₁ head ]
      tail : ∃ λ i → AVLMapIndexed V [ proj₁ head ] u (i ⊕ h)

  reduce : ∀ {l y u h}
          → {{@erased l≤y : l <⁺ y}}
          → AVLMapIndexed V y u h
          → AVLMapIndexed V l u h
  reduce {l} {y} {u} {{a}} (leaf {{b}}) = leaf {{trans⁺ l a b}}
  reduce {{a}} (node p l r bal) = node p (reduce {{a}} l) r bal

  raise : ∀ {l y u h}
          → {{@erased y≤u : y <⁺ u}}
          → AVLMapIndexed V l y h
          → AVLMapIndexed V l u h
  raise {x} {y} {z} {{a}} (leaf {{b}}) = leaf {{trans⁺ x b a}}
  raise {{a}} (node p l r bal) = node p l (raise {{a}} r) bal
\end{code}

\newcommand{\mklimEx}{
\begin{code}
  @erased mklim : ∀ {l u h}
          → AVLMapIndexed V l u h
          → l <⁺ u
  mklim (leaf {{p}}) = p
  mklim {l} {u} (node p lt rt bal) = trans⁺ l (mklim lt) (mklim rt)
\end{code}
}

\begin{code}[hide]
-- * JOINS STARTS HERE -----------------------------------------------------
  joinˡ⁺ : ∀ {l u : Key⁺} {h} {hl} {hr}
    → (p : Key × V)
    → ∃ (λ i → AVLMapIndexed V l [ proj₁ p ] (i ⊕ hl))
    → AVLMapIndexed V [ proj₁ p ] u hr
    → hl ~ hr ⊔ h
    → ∃ (λ i → AVLMapIndexed V l u (i ⊕ suc h))
  joinˡ⁺ p (0# , lt) rt bal = 0# , node p lt rt bal
  joinˡ⁺ p (1# , lt) rt ~+  = 0# , node p lt rt ~0
  joinˡ⁺ p (1# , lt) rt ~0  = 1# , node p lt rt ~-
  joinˡ⁺ p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- = 1# , node pᴸ ltᴸ (node p rtᴸ rt ~-) ~+
  joinˡ⁺ p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- = 0# , (node pᴸ ltᴸ (node p rtᴸ rt ~0) ~0)
  joinˡ⁺ p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+) rt ~- =
    0# , (node pᴿ (node pᴸ ltᴸ ltᴿ (max~ b)) (node p rtᴿ rt (~max b)) ~0)

  joinʳ⁺ : ∀ {l u : Key⁺} {h} {hl} {hr}
    → (p : Key × V)
    → AVLMapIndexed V l [ proj₁ p ] hl
    → ∃ (λ i → AVLMapIndexed V [ proj₁ p ] u (i ⊕ hr))
    → hl ~ hr ⊔ h
    → ∃ (λ i → AVLMapIndexed V l u (i ⊕ suc h))
  joinʳ⁺ p lt (0# , rt) bal = 0# , node p lt rt bal
  joinʳ⁺ p lt (1# , rt) ~0 = 1# , node p lt rt ~+
  joinʳ⁺ p lt (1# , rt) ~- = 0# , node p lt rt ~0
  joinʳ⁺ p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ = 0# , (node pᴿ (node p lt ltᴿ ~0) rtᴿ ~0)
  joinʳ⁺ p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ = 1# , node pᴿ (node p lt ltᴿ ~+) rtᴿ ~-
  joinʳ⁺ p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-) ~+ =
    0# , node pᴸ (node p lt ltᴸ (max~ b)) (node pᴿ rtᴸ rtᴿ (~max b)) ~0

  joinˡ⁻ : ∀ {l u} {hl hr h}
          → ((k , v) : Key × V)
          → ∃ (λ i → AVLMapIndexed V l [ k ] pred[ i ⊕ hl ])
          → AVLMapIndexed V [ k ] u hr
          → hl ~ hr ⊔ h
          → ∃ λ i → AVLMapIndexed V l u (i ⊕ h)
  joinˡ⁻ {hl = zero} kv (0# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = zero} kv (1# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~+ = joinʳ⁺ kv lt (1# , rt) ~+
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~0 = 1# , (node kv lt rt ~+)
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~- = 0# , (node kv lt rt ~0)
  joinˡ⁻ {hl = suc hl} kv (1# , lt) rt b = 1# , (node kv lt rt b)

  joinʳ⁻ : ∀ {l u} {hl hr h}
           → ((k , v) : Key × V)
           → AVLMapIndexed V l [ k ] hl
           → ∃ (λ i → AVLMapIndexed V [ k ] u pred[ i ⊕ hr ])
           → hl ~ hr ⊔ h
           → ∃ λ i → AVLMapIndexed V l u (i ⊕ h)
  joinʳ⁻ {hr = zero} kv lt (0# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = zero} kv lt (1# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~+ = 0# , node kv lt rt ~0
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~0 = 1# , node kv lt rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~- = joinˡ⁺ kv (1# , lt) rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (1# , rt) b = 1# , node kv lt rt b

  uncons : ∀ {l u h}
             → AVLMapIndexed V l u (suc h)
             → Cons l u h
  uncons (node p leaf rm ~+) = cons p (mklim leaf) (0# , rm)
  uncons (node p leaf rm ~0) = cons p (mklim leaf) (0# , rm)
  {-# CATCHALL #-}
  uncons (node {suc _} p lm rm bal) with uncons lm
  ... | cons head l<u tail = cons head l<u (joinˡ⁻ p tail rm bal)

  join : {l u : Key⁺} {k : Key} {hl hr h : ℕ}
         → AVLMapIndexed V l [ k ] hl
         → AVLMapIndexed V [ k ] u hr
         → hl ~ hr ⊔ h
         → ∃ λ i → AVLMapIndexed V l u (i ⊕ h)
  join lt leaf ~0 = 0# , raise lt
  join lt leaf ~- = 0# , raise lt
  {-# CATCHALL #-}
  join {hr = suc _} lt rt b with uncons rt
  ... | cons head l<u tail = joinʳ⁻ head (raise ⦃ l<u ⦄ lt) tail b
\end{code}

\newcommand{\insertWith}{
\begin{code}
  insertWith : {l u : Key⁺} {h : ℕ} (k : Key) (f : Maybe V → V)
               {{@erased l≤u : l <⁺ [ k ]}} {{@erased p≤u : [ k ] <⁺ u}}
               → AVLMapIndexed V l u h
               → ∃ λ i → AVLMapIndexed V l u (i ⊕ h)
  insertWith k f leaf = 1# , node (k , f nothing) leaf leaf ~0
  insertWith k f (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁺ p (insertWith k f {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = 0# , node (k , f (just (proj₂ p))) lt rt bal
  ... | tri> _ _ p<k = joinʳ⁺ p lt (insertWith k f {{[ p<k ]ᴿ}} rt) bal

  insert : {l u : Key⁺} {h : ℕ} (kv : Key × V)
           {{@erased l≤p : l <⁺ [ (proj₁ kv) ]}}
           {{@erased p≤u : [ (proj₁ kv) ] <⁺ u}}
           → AVLMapIndexed V l u h
           → ∃ λ i → AVLMapIndexed V l u (i ⊕ h)
  insert (k , v) m = insertWith k (λ _ → v) m
\end{code}
}

\newcommand{\lookup}{
\begin{code}
  lookup : ∀ {l u : Key⁺} {h : ℕ}
           → AVLMapIndexed V l u h
           → Key
           → Maybe V
  lookup leaf k = nothing
  lookup (node p lt rt bal) k with compare k (proj₁ p)
  ... | tri< k<p _ _ = lookup lt k
  ... | tri≈ _ refl _ = just (proj₂ p)
  ... | tri> _ _ p<k = lookup rt k
\end{code}
}


\newcommand{\delete}{
\begin{code}
  delete : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
           {{@erased l≤p : l <⁺ [ k ]}} {{@erased p≤u : [ k ] <⁺ u}}
           → AVLMapIndexed V l u h
           → ∃ λ i → AVLMapIndexed V l u pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁻ p (delete k {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = join lt rt bal
  ... | tri> _ _ p<k = joinʳ⁻ p lt (delete k {{[ p<k ]ᴿ}} rt) bal
\end{code}
}

\newcommand{\anydef}{
\begin{code}
  data Any (P : Pred V ℓₚ) {l u : Key⁺} (kₚ : Key) :
    ∀ {h : ℕ} → @erased AVLMapIndexed V l u h → Set (k ⊔ ℓ₁ ⊔ v ⊔ ℓₚ) where
    here : ∀ {h hl hr} {v : V}
           {{@erased l≤k : l <⁺ [ kₚ ]}} {{@erased k≤u : [ kₚ ] <⁺ u}}
           → P v →
           {@erased lm : AVLMapIndexed V l [ kₚ ] hl}
           {@erased rm : AVLMapIndexed V [ kₚ ] u hr}
           {@erased bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (kₚ , v) lm rm bal)

    left : ∀ {h hl hr} {(k' , v) : Key × V}
           {@erased lm : AVLMapIndexed V l [ k' ] hl}
           {{@erased k≺k' : [ kₚ ] <⁺ [ k' ]}}
           → Any P kₚ lm →
           {@erased rm : AVLMapIndexed V [ k' ] u hr}
           {@erased bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)

    right : ∀ {h hl hr} {(k' , v) : Key × V}
           {@erased lm : AVLMapIndexed V l [ k' ] hl}
           {@erased rm : AVLMapIndexed V [ k' ] u hr}
           {{@erased k'≤k : [ k' ] <⁺ [ kₚ ]}}
           → Any P kₚ rm
           → {@erased bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)
\end{code}
}

\begin{code}[hide]
  foldr : ∀ {l u} {h : ℕ} {n : Level} {A : Set n}
          → (Key × V → A → A)
          → A
          → AVLMapIndexed V l u h
          → A
  foldr f g leaf = g
  foldr f g (node p l r bal) = foldr f (f p (foldr f g r)) l
\end{code}

\newcommand{\alldef}{
\begin{code}
  data All (P : Pred (Key × V) ℓₐ) {l u : Key⁺}
      : ∀ {h : ℕ} → AVLMapIndexed V l u h → Set (k ⊔ ℓ₁ ⊔ v ⊔ ℓₐ) where
    leaf : ⦃ @erased l<u : l <⁺ u ⦄ → All P leaf
    node : ∀ {hl hr h}
           → {p : Key × V}
           (let (k , v) = p)
           {lt : AVLMapIndexed V l [ k ] hl}
           {rt : AVLMapIndexed V [ k ] u hr}
           {bal : hl ~ hr ⊔ h}
           → P (k , v)
           → All P lt
           → All P rt
           → All P (node (k , v) lt rt bal)
\end{code}
}

\newcommand{\allLookup}{
\begin{code}
  allLookup : {l u : Key⁺} {h : ℕ} {m : AVLMapIndexed V l u h} {k : Key} {v : V} {P : Pred (Key × V) ℓₐ}
    → Any (λ v' → v ≡ v') k  m
    → All P m
    → P (k , v)
  allLookup (here refl) (node p lt rt) = p
  allLookup (left prf) (node p lt rt) = allLookup prf lt
  allLookup (right prf) (node p lt rt) = allLookup prf rt
\end{code}
}

\begin{code}[hide]
  alljoinᴸ : ∀ {l u : Key⁺} {hl hr h : ℕ} {P : Pred (Key × V) ℓₐ}
    → {k : Key} {v : V}
    → {lt⁺ : ∃ λ i → AVLMapIndexed V l [ k ] (i ⊕ hl)}
    → {rt : AVLMapIndexed V [ k ] u hr}
    → P (k , v)
    → All P (proj₂ lt⁺)
    → All P rt
    → (bal : hl ~ hr ⊔ h)
    → All P (proj₂ (joinˡ⁺ (k , v) lt⁺ rt bal))
  alljoinᴸ {lt⁺ = (0# , lt)} p allL allR bal = node p allL allR
  alljoinᴸ {lt⁺ = (1# , lt)} p allL allR ~+ = node p allL allR
  alljoinᴸ {lt⁺ = (1# , lt)} p allL allR ~0 = node p allL allR
  alljoinᴸ {lt⁺ = (1# , node _ _ _ ~0)} p (node a aL aR) allR ~- = node a aL (node p aR allR)
  alljoinᴸ {lt⁺ = (1# , node _ _ _ ~-)} p (node a aL aR) allR ~- = node a aL (node p aR allR)
  alljoinᴸ {lt⁺ = (1# , node _ _ (node _ _ _ _) ~+)} {rt} p (node a aL (node aᴿ aLᴿ aRᴿ)) allR ~- =
    node aᴿ (node a aL aLᴿ) (node p aRᴿ allR)

  alljoinᴿ : ∀ {l u : Key⁺} {hl hr h : ℕ} {P : Pred (Key × V) ℓₐ}
    → {k : Key} {v : V}
    → {lt : AVLMapIndexed V l [ k ] hl}
    → {rt⁺ : ∃ λ i → AVLMapIndexed V [ k ] u (i ⊕ hr)}
    → P (k , v)
    → All P lt
    → All P (proj₂ rt⁺)
    → (bal : hl ~ hr ⊔ h)
    → All P (proj₂ (joinʳ⁺ (k , v) lt rt⁺ bal))
  alljoinᴿ {rt⁺ = (0# , rt)} p allL allR bal = node p allL allR
  alljoinᴿ {rt⁺ = (1# , rt)} p allL allR ~0 = node p allL allR
  alljoinᴿ {rt⁺ = (1# , rt)} p allL allR ~- = node p allL allR
  alljoinᴿ {rt⁺ = (1# , (node _ _ _ ~+))} p allL (node a aL aR) ~+ = node a (node p allL aL) aR
  alljoinᴿ {rt⁺ = (1# , (node _ _ _ ~0))} p allL (node a aL aR) ~+ = node a (node p allL aL) aR
  alljoinᴿ {rt⁺ = (1# , (node _ (node _ _ _ _) _ ~-))} p allL (node a (node aᴸ aLᴸ aRᴸ) aR) ~+ =
    node aᴸ (node p allL aLᴸ) (node a aRᴸ aR)
\end{code}

\newcommand{\allInsert}{
\begin{code}
  allInsert : {l u : Key⁺} {h : ℕ} {(k , v) : Key × V}
              {P : Pred (Key × V) ℓₐ}
              {{@erased l<u : l <⁺ [ k ]}} {{@erased p<u : [ k ] <⁺ u}}
              {m : AVLMapIndexed V l u h}
              → P (k , v)
              → All P m
              → All P (proj₂ $ insert (k , v) m)
  allInsert p leaf = node p leaf leaf
  allInsert {h = _} {k , v} p (node {h = _} {(k' , v')} {lt} {rt} {bal = bal} a allL allR) with compare k k'
  ... | le k<k' = alljoinᴸ {lt⁺ = m } a (allInsert ⦃ p<u = [ k<k' ]ᴿ ⦄ p allL) allR bal
    where
      m = insert (k , v) ⦃ p≤u = [ k<k' ]ᴿ ⦄ lt
  ... | eq refl = node p allL allR
  ... | ge k'<k = alljoinᴿ {rt⁺ = m} a allL (allInsert ⦃ [ k'<k ]ᴿ ⦄ p allR) bal
    where
      m = insert (k , v) ⦃ [ k'<k ]ᴿ ⦄ rt
\end{code}
}

\newcommand{\RecordSplitUnion}{
\begin{code}
  record Split (x : Key) (@0 l u : Key⁺) (h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor split
    field
      value : Maybe V
      leftH : ℕ
      @0 leftP : leftH ≤ h
      leftT : AVLMapIndexed V l [ x ] leftH
      rightH : ℕ
      @0 rightP : rightH ≤ h
      rightT : AVLMapIndexed V [ x ] u rightH

  record UnionReturn {@0 l u : Key⁺} {h1 h2 : ℕ}
    (@0 t₁ : AVLMapIndexed V l u h1) (@0 t₂ : AVLMapIndexed V l u h2)
    : Set (k ⊔ v ⊔ ℓ₁) where
    constructor retval
    field
      hof : ℕ
      tree : AVLMapIndexed V l u hof
      @0 prf : hof ≤ (h1 + h2)
\end{code}
}

\begin{code}[hide]
  n+0 : ∀ n → n + 0 ≡ n
  n+0 zero = refl
  n+0 (suc n) rewrite n+0 n = refl

  eqto≤ : ∀ n → n ≤ n → n ≤ n + 0
  eqto≤ n p rewrite n+0 n = ≤-refl
\end{code}

\newcommand{\JoinType}{
\begin{code}[hide]
  module _ where
  postulate
\end{code}
\begin{code}
    gJoin : {hl hr : ℕ} {@0 l u : Key⁺}
      → ((k , v) : Key × V)
      → AVLMapIndexed V l [ k ] hl
      → AVLMapIndexed V [ k ] u hr
      → ∃ λ i → AVLMapIndexed V l u (i ⊕ max hl hr)
\end{code}
}
