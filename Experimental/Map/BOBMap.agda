module Map.BOBMap where

open import Prelude hiding (Nat;_×_;_,_)
open import OrdSet
open import Level using (Level; _⊔_) 
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product

private
  variable
    ℓ ℓ' : Level

module _ {K : Set ℓ} (V : Set ℓ') (R : OSet K) where
  open OSet R
  open OSet (ext {ℓ} {K} {R}) renaming 
   (_≤_ to _≤Ex_;_≺_ to _≺Ex_; trans to transEx; compare to compareEx)

  ℕ₂ = Fin 2
  pattern 0# = fzero
  pattern 1# = fsuc fzero
  pattern ## = fsuc (fsuc ())

  infixl 6 _⊕_

  _⊕_ : ℕ₂ → ℕ → ℕ
  0# ⊕ n = n
  1# ⊕ n = 1 + n

  infix 4 _~_⊔_
  
  data _~_⊔_ : ℕ → ℕ → ℕ → Set where
    ~+ : ∀ {n} → n     ~ 1 + n ⊔ 1 + n
    ~0 : ∀ {n} → n     ~ n     ⊔ n
    ~- : ∀ {n} → 1 + n ~ n     ⊔ 1 + n 

  max~ : ∀ {i j m} → i ~ j ⊔ m → m ~ i ⊔ m
  max~ ~+ = ~-
  max~ ~0 = ~0
  max~ ~- = ~0

  ~max : ∀ {i j m} → i ~ j ⊔ m → j ~ m ⊔ m
  ~max ~+ = ~0
  ~max ~0 = ~0
  ~max ~- = ~+

  -- B(alanced)O(rdered)B(ST)Map
  data BOBMap (lu : Ext K × Ext K) : ℕ → Set (ℓ ⊔ ℓ') where
    leaf : {{l≤u : (proj₁ lu) ≺Ex (proj₂ lu)}} → BOBMap lu 0
    node : {h hl hr : ℕ}
           (p : K × V)
           (let (k , v) = p)
           (let (l , u) = lu)
           (lt : BOBMap (l , # k) hl)
           (rt : BOBMap (# k , u) hr)
           (bal : hl ~ hr ⊔ h)
           → BOBMap lu (suc h)

  rotR : ∀ {l u : Ext K} {hr : ℕ}
         (kv : K × V)
         → BOBMap (l , # (proj₁ kv)) (suc (suc hr))
         → BOBMap (# (proj₁ kv) , u) hr
         → ∃ λ i → BOBMap (l , u) (i ⊕ (suc (suc hr))) 
  rotR kv (node p llt lrt ~0) rt = 1# , (node p llt (node kv lrt rt ~-) ~+)
  rotR kv (node p llt lrt ~-) rt = 0# , (node p llt (node kv lrt rt ~0) ~0)
  rotR kv (node p llt (node p' lrlt lrrt bal) ~+) rt =
    0# , (node p' (node p llt lrlt (max~ bal)) (node kv lrrt rt (~max bal)) ~0)
  
  rotL : ∀ {l u : Ext K} {hl : ℕ}
         (kv : K × V)
         → BOBMap (l , # (proj₁ kv)) hl 
         → BOBMap (# (proj₁ kv) , u) (suc (suc hl))
         → ∃ λ i → BOBMap (l , u) (i ⊕ (suc (suc hl))) 
  rotL kv lt (node p rlt rrt ~+) = 0# , (node p (node kv lt rlt ~0) rrt ~0)
  rotL kv lt (node p rlt rrt ~0) = 1# , (node p (node kv lt rlt ~+) rrt ~-)
  rotL kv lt (node p (node p' rllt rlrt bal) rrt ~-) =
    0# , (node p' (node kv lt rllt (max~ bal)) (node p rlrt rrt (~max bal)) ~0)

  insert : ∀ {l u : Ext K} {h : ℕ} (kv : K × V) 
            {{l≤p : l ≺Ex  (# (proj₁ kv))}} {{p≤u :(# (proj₁ kv)) ≺Ex u}}
            → BOBMap (l , u) h → ∃ λ i → BOBMap (l , u) (i ⊕ h)
  insert kv leaf = (1# , node kv leaf leaf ~0)
  insert kv (node p lt rt bal) with compare (proj₁ kv) (proj₁ p)
  insert kv (node p lt rt bal)
    | le with insert kv lt
  ... | 0# , t = 0# , (node p t rt bal)
  ... | 1# , t with bal
  ... | ~+ = 0# , (node p t rt ~0)
  ... | ~0 = 1# , node p t rt ~-
  ... | ~- = rotR p t rt -- rotate
  insert kv (node p lt rt bal)
    | eq = 0# , (node kv lt rt bal)
  insert kv (node p lt rt bal)
    | ge with insert kv rt
  ... | 0# , t = 0# , node p lt t bal
  ... | 1# , t with bal
  ... | ~+ = rotL p lt t -- rotate
  ... | ~0 = 1# , (node p lt t ~+)
  ... | ~- = 0# , node p lt t ~0
