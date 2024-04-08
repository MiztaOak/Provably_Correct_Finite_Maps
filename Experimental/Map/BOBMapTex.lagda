\begin{code}[hide]
{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMapTex {k ℓ₁} (order : OrdSet k ℓ₁) where

Order : StrictTotalOrder k k ℓ₁
Order = toStrictTotalOrder order

open import Prelude
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _<_)
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
    ℓ ℓ' ℓₚ : Level
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

\newcommand{\BOBMapDef}{
\begin{code}
data BOBMap (V : Set v) (l u : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ₁) where
  leaf : {{@erased l<u : l <⁺ u}} → BOBMap V l u 0
  node : ∀ {hl hr h}
         → ((k , v) : Key × V)
         → (lm : BOBMap V l [ k ] hl)
         → (rm : BOBMap V [ k ] u hr)
         → (bal : hl ~ hr ⊔ h)
         → BOBMap V l u (suc h)
\end{code}
}


\begin{code}[hide]
module _ {v} {V : Set v} where

  record Cons (l u : Key⁺) (h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor cons
    field
      head : Key × V
      @erased l<u : l <⁺ [ proj₁ head ]
      tail : ∃ λ i → BOBMap V [ proj₁ head ] u (i ⊕ h)

  reduce : ∀ {l y u h}
          → {{@erased l≤y : l <⁺ y}}
          → BOBMap V y u h
          → BOBMap V l u h
  reduce {l} {y} {u} {{a}} (leaf {{b}}) = leaf {{trans⁺ l a b}}
  reduce {{a}} (node p l r bal) = node p (reduce {{a}} l) r bal

  raise : ∀ {l y u h}
          → {{@erased y≤u : y <⁺ u}}
          → BOBMap V l y h
          → BOBMap V l u h
  raise {x} {y} {z} {{a}} (leaf {{b}}) = leaf {{trans⁺ x b a}}
  raise {{a}} (node p l r bal) = node p l (raise {{a}} r) bal

  @erased mklim : ∀ {l u h}
          → BOBMap V l u h
          → l <⁺ u
  mklim (leaf {{p}}) = p
  mklim {l} {u} (node p lt rt bal) = trans⁺ l (mklim lt) (mklim rt)

-- * JOINS STARTS HERE -----------------------------------------------------
  joinˡ⁺ : ∀ {l u : Key⁺} {h} {hl} {hr}
    → (p : Key × V)
    → ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl))
    → BOBMap V [ proj₁ p ] u hr
    → hl ~ hr ⊔ h
    → ∃ (λ i → BOBMap V l u (i ⊕ suc h))
  joinˡ⁺ p (0# , lt) rt bal = 0# , node p lt rt bal
  joinˡ⁺ p (1# , lt) rt ~+  = 0# , node p lt rt ~0
  joinˡ⁺ p (1# , lt) rt ~0  = 1# , node p lt rt ~-
  joinˡ⁺ p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- = 1# , node pᴸ ltᴸ (node p rtᴸ rt ~-) ~+
  joinˡ⁺ p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- = 0# , (node pᴸ ltᴸ (node p rtᴸ rt ~0) ~0)
  joinˡ⁺ p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+) rt ~- =
    0# , (node pᴿ (node pᴸ ltᴸ ltᴿ (max~ b)) (node p rtᴿ rt (~max b)) ~0)

  joinʳ⁺ : ∀ {l u : Key⁺} {h} {hl} {hr}
    → (p : Key × V)
    → BOBMap V l [ proj₁ p ] hl
    → ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr))
    → hl ~ hr ⊔ h
    → ∃ (λ i → BOBMap V l u (i ⊕ suc h))
  joinʳ⁺ p lt (0# , rt) bal = 0# , node p lt rt bal
  joinʳ⁺ p lt (1# , rt) ~0 = 1# , node p lt rt ~+
  joinʳ⁺ p lt (1# , rt) ~- = 0# , node p lt rt ~0
  joinʳ⁺ p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ = 0# , (node pᴿ (node p lt ltᴿ ~0) rtᴿ ~0)
  joinʳ⁺ p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ = 1# , node pᴿ (node p lt ltᴿ ~+) rtᴿ ~-
  joinʳ⁺ p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-) ~+ =
    0# , node pᴸ (node p lt ltᴸ (max~ b)) (node pᴿ rtᴸ rtᴿ (~max b)) ~0

  joinˡ⁻ : ∀ {l u} {hl hr h}
          → ((k , v) : Key × V)
          → ∃ (λ i → BOBMap V l [ k ] pred[ i ⊕ hl ])
          → BOBMap V [ k ] u hr
          → hl ~ hr ⊔ h
          → ∃ λ i → BOBMap V l u (i ⊕ h)
  joinˡ⁻ {hl = zero} kv (0# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = zero} kv (1# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~+ = joinʳ⁺ kv lt (1# , rt) ~+
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~0 = 1# , (node kv lt rt ~+)
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~- = 0# , (node kv lt rt ~0)
  joinˡ⁻ {hl = suc hl} kv (1# , lt) rt b = 1# , (node kv lt rt b)

  joinʳ⁻ : ∀ {l u} {hl hr h}
           → ((k , v) : Key × V)
           → BOBMap V l [ k ] hl
           → ∃ (λ i → BOBMap V [ k ] u pred[ i ⊕ hr ])
           → hl ~ hr ⊔ h
           → ∃ λ i → BOBMap V l u (i ⊕ h)
  joinʳ⁻ {hr = zero} kv lt (0# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = zero} kv lt (1# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~+ = 0# , node kv lt rt ~0
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~0 = 1# , node kv lt rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~- = joinˡ⁺ kv (1# , lt) rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (1# , rt) b = 1# , node kv lt rt b

  uncons : ∀ {l u h}
             → BOBMap V l u (suc h)
             → Cons l u h
  uncons (node p leaf rm ~+) = cons p (mklim leaf) (0# , rm)
  uncons (node p leaf rm ~0) = cons p (mklim leaf) (0# , rm)
  {-# CATCHALL #-}
  uncons (node {suc _} p lm rm bal) with uncons lm
  ... | cons head l<u tail = cons head l<u (joinˡ⁻ p tail rm bal)

  join : {l u : Key⁺} {k : Key} {hl hr h : ℕ}
         → BOBMap V l [ k ] hl
         → BOBMap V [ k ] u hr
         → hl ~ hr ⊔ h
         → ∃ λ i → BOBMap V l u (i ⊕ h)
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
               → BOBMap V l u h
               → ∃ λ i → BOBMap V l u (i ⊕ h)
  insertWith k f leaf = 1# , node (k , f nothing) leaf leaf ~0
  insertWith k f (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁺ p (insertWith k f {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = 0# , node (k , f (just (proj₂ p))) lt rt bal
  ... | tri> _ _ p<k = joinʳ⁺ p lt (insertWith k f {{[ p<k ]ᴿ}} rt) bal

  insert : {l u : Key⁺} {h : ℕ} (kv : Key × V)
           {{@erased l≤p : l <⁺ [ (proj₁ kv) ]}}
           {{@erased p≤u : [ (proj₁ kv) ] <⁺ u}}
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u (i ⊕ h)
  insert (k , v) m = insertWith k (λ _ → v) m
\end{code}
}

\newcommand{\lookup}{
\begin{code}
  lookup : ∀ {l u : Key⁺} {h : ℕ}
           → BOBMap V l u h
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
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁻ p (delete k {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = join lt rt bal
  ... | tri> _ _ p<k = joinʳ⁻ p lt (delete k {{[ p<k ]ᴿ}} rt) bal
\end{code}
}

\newcommand{\any}{
\begin{code}
  data Any (P : Pred V ℓₚ) {l u : Key⁺} (kₚ : Key) :
    ∀ {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ v ⊔ ℓₚ) where
    here : ∀ {h hl hr} {v : V}
           {{@erased l≤k : l <⁺ [ kₚ ]}} {{@erased k≤u : [ kₚ ] <⁺ u}}
           → P v
           → {lm : BOBMap V l [ kₚ ] hl}
           {rm : BOBMap V [ kₚ ] u hr}
           {bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (kₚ , v) lm rm bal)

    left : ∀ {h hl hr} {(k' , v) : Key × V}
           {lm : BOBMap V l [ k' ] hl}
           {{@erased k≺k' : [ kₚ ] <⁺ [ k' ]}}
           → Any P kₚ lm
           → {rm : BOBMap V [ k' ] u hr}
           {bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)

    right : ∀ {h hl hr} {(k' , v) : Key × V}
           {lm : BOBMap V l [ k' ] hl}
           {rm : BOBMap V [ k' ] u hr}
           {{@erased k'≤k : [ k' ] <⁺ [ kₚ ]}}
           → Any P kₚ rm
           → {bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)
\end{code}
}

\begin{code}[hide]
  foldr : ∀ {l u} {h : ℕ} {n : Level} {A : Set n}
          → (Key × V → A → A)
          → A
          → BOBMap V l u h
          → A
  foldr f g leaf = g
  foldr f g (node p l r bal) = foldr f (f p (foldr f g r)) l
\end{code}
