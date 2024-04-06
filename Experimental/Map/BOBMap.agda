{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMap {k ℓ₁} (order : OrdSet k ℓ₁) where

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

data BOBMap (V : Set v) (l u : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ₁) where
  leaf : {{@erased l<u : l <⁺ u}} → BOBMap V l u 0
  node : ∀ {hl hr h}
         → ((k , v) : Key × V)
         → (lm : BOBMap V l [ k ] hl)
         → (rm : BOBMap V [ k ] u hr)
         → (bal : hl ~ hr ⊔ h)
         → BOBMap V l u (suc h)

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

  lookup : ∀ {l u : Key⁺} {h : ℕ}
           → BOBMap V l u h
           → Key
           → Maybe V
  lookup leaf k = nothing
  lookup (node p lt rt bal) k with compare k (proj₁ p)
  ... | tri< k<p _ _ = lookup lt k
  ... | tri≈ _ refl _ = just (proj₂ p)
  ... | tri> _ _ p<k = lookup rt k

-- * UNION STARTS HERE -----------------------------------------------------


  heightBM : ∀ {h l u} → BOBMap V l u h → ℕ
  heightBM {h} _ = h

  ratio : ℕ
  ratio = 5 -- source?

  data CmpResult : Set where
    LT : CmpResult
    EQ : CmpResult
    GT : CmpResult

  cmp : ℕ → ℕ → CmpResult
  cmp zero    zero    = EQ
  cmp zero    _       = LT
  cmp _       zero    = GT
  cmp (suc n) (suc m) = cmp n m

  max : ℕ → ℕ → ℕ
  max zero n = n
  max (suc n) zero = suc n
  max (suc n) (suc m) = suc (max n m)

  lemma : ∀ {n m : ℕ} → max (suc (m + n)) m ≡ suc (m + n)
  lemma {n} {zero} = refl
  lemma {n} {suc m} rewrite lemma {n} {m} = refl

  {-# TERMINATING #-}
  concat3 : {h1 h2 : ℕ}
            → ((k , v) : Key × V)
            → {l u : Key⁺}
            → BOBMap V l [ k ] h1
            → BOBMap V [ k ] u h2
            → ∃ λ n → BOBMap V l u n
  concat3 p n (leaf {{pf}}) with insert p {{mklim n}} {{pf}} (raise {{pf}} n)
  ... | _ , t = _ , t
  concat3 p (leaf {{pf}}) m with insert p {{pf}} {{mklim m}} (reduce {{pf}} m)
  ... | _ , t = _ , t
  concat3 p@(k , v) n@(node p1 l1 r1 b1) m@(node p2 l2 r2 b2)
    with cmp (ratio * heightBM n) (heightBM m)
  ... | LT = let (i , cc) = concat3 p n l2
             in {!!} --balance p2 cc r2
  ... | EQ = {!!} , {!!}
  ... | GT = let (i , cc) = concat3 p r1 m
             in {!!} --balance p1 l1 cc

  splitLT : ∀ {l u h}
            → ((k , v) : Key × V)
            → {{@erased l≤k : l <⁺ [ k ]}}
            → BOBMap V l u h
            → ∃ λ n → BOBMap V l [ k ] n
  splitLT x (leaf {{l<u}}) = 0 , leaf
  splitLT (k , v) (node (k' , v') lt rt bal) with compare k k'
  ... | tri< k<p _ _ = splitLT (k , v) lt
  ... | tri≈ _ refl _ = _ , lt
  ... | tri> _ _ p<k = let (n , m) = splitLT (k , v) {{[ p<k ]ᴿ}} rt
                       in concat3 (k' , v') lt m

  splitGT : ∀ {l u h}
            → ((k , v) : Key × V)
            → {{@erased l≤u : [ k ] <⁺ u}}
            → BOBMap V l u h
            → ∃ λ n → BOBMap V [ k ] u n
  splitGT x (leaf {{l<u}})= 0 , leaf
  splitGT (k , v) (node (k' , v') lt rt bal) with compare k k'
  ... | tri< k<p _ _ = let (n , m) = splitGT (k , v) {{[ k<p ]ᴿ}} lt
                       in concat3 (k' , v') m rt
  ... | tri≈ _ refl _ = _ , rt
  ... | tri> _ _ p<k = splitGT (k , v) rt

  union : {h1 h2 : ℕ} → ∀ {l u}
          → (V → Maybe V → V)
          → BOBMap V l u h1
          → BOBMap V l u h2
          → ∃ λ n → BOBMap V l u (n ⊕ (max h1 h2))
  union f leaf (leaf ⦃ l≤u ⦄) = 0# , leaf ⦃ l≤u ⦄
  union f leaf (node p lm rm b) = 0# , node p lm rm b
  union f (node p lm rm b) leaf = 0# , node p lm rm b
  union {h1} {h2} f (node p1 lm1 rm1 b1) (node p2 lm2 rm2 b2) with
    splitLT p2 {{mklim lm2}} (node p1 lm1 rm1 b1)
  ... | lsh , ls with splitGT p2 {{mklim rm2}} (node p1 lm1 rm1 b1)
  ... | rsh , rs with union f ls lm2
  ... | llh , ll with union f rs rm2
  ... | rrh , rr = join {h = max h1 h2} ll rr {!!}

  -- * DELETE STARTS HERE ----------------------------------------------------


  delete : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
           {{@erased l≤p : l <⁺ [ k ]}} {{@erased p≤u : [ k ] <⁺ u}}
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁻ p (delete k {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = join lt rt bal
  ... | tri> _ _ p<k = joinʳ⁻ p lt (delete k {{[ p<k ]ᴿ}} rt) bal

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

  foldr : ∀ {l u} {h : ℕ} {n : Level} {A : Set n}
          → (Key × V → A → A)
          → A
          → BOBMap V l u h
          → A
  foldr f g leaf = g
  foldr f g (node p l r bal) = foldr f (f p (foldr f g r)) l

-- -}
-- -}
-- -}
-- -}
-- -}
