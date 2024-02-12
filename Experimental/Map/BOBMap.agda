{-# OPTIONS --allow-unsolved-metas #-}
module Map.BOBMap where

open import Prelude 
open import OrdSet
open import Level using (Level; _⊔_) 
open import Data.Nat.Base using (ℕ; zero; suc; _+_) 
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Maybe
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality hiding (trans)

private
  variable
    ℓ ℓ' ℓₚ : Level

module Map {K : Set ℓ} (V : Set ℓ') (R : OSet K) where
  open OSet R
  open OSet (ext {ℓ} {K} {R}) renaming 
   (_≺_ to _≺Ex_; trans to transEx; compare to compareEx)

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
            → BOBMap (l , u) h
            → ∃ λ i → BOBMap (l , u) (i ⊕ h)
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

  lookup : ∀ {l u : Ext K} {h : ℕ}
           → BOBMap (l , u) h
           → K
           → Maybe V
  lookup leaf k = nothing
  lookup (node p lt rt bal) k with compare k (proj₁ p)
  ... | le = lookup lt k
  ... | eq = just (proj₂ p)
  ... | ge = lookup rt k

  join : ∀ {l u : Ext K} {k : K} {hl hr h : ℕ}
         → BOBMap (l , # k) hl 
         → hl ~ hr ⊔ h
         → BOBMap (# k , u) hr
         → ∃ λ i → BOBMap (l , u) (i ⊕ h)
  join leaf ~+ rt = {!!}
  join leaf ~0 leaf = 0# , (leaf {{{!!}}})
  join (node p llt lrt bal) b rt = {!!}
  
  delete : ∀ {l u : Ext K} {h : ℕ} (k : K)
           {{l≤p : l ≺Ex  (# k)}} {{p≤u :(# k) ≺Ex u}}
           → BOBMap (l , u) h
           → ∃ λ i → BOBMap (l , u) pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  delete k (node p lt rt bal)
    | le with delete k lt
  ... | 0# , lt' = 1# , node p lt' rt {!!} 
  ... | 1# , lt' with bal
  ... | ~+ = {!!} 
  ... | ~0 = 1# , node p lt' rt {!!}
  ... | ~- = 1# , (node p lt' rt ~-)
  delete k (node p lt rt bal)
    | eq = {!!}
  delete k (node p lt rt bal)
    | ge with delete k rt
  ... | x , rt' = {!!} 

  data Any (P : Pred (K × V) ℓₚ) {l u : Ext K} :
    ∀ {h : ℕ} → BOBMap (l , u) h → Set (ℓ ⊔ ℓ' ⊔ ℓₚ) where
    here : ∀ {h hl hr} {kv : K × V}
           → P kv
           → {lm : BOBMap (l , # (proj₁ kv)) hl}
           {rm : BOBMap (# (proj₁ kv) , u) hr}
           {bal : hl ~ hr ⊔ h}
           → Any P (node kv lm rm bal)

    left : ∀ {h hl hr} {kv : K × V}
           {lm : BOBMap (l , # (proj₁ kv)) hl}
           → Any P lm 
           → {rm : BOBMap (# (proj₁ kv) , u) hr}
           {bal : hl ~ hr ⊔ h}
           → Any P (node kv lm rm bal)

    right : ∀ {h hl hr} {kv : K × V}
           {lm : BOBMap (l , # (proj₁ kv)) hl}
           {rm : BOBMap (# (proj₁ kv) , u) hr}
           → Any P rm 
           → {bal : hl ~ hr ⊔ h}
           → Any P (node kv lm rm bal)

    
