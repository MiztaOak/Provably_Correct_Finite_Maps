module Map.TPMap where

open import Prelude hiding (Rel; _≡_)
open import OrdSet
open import Level renaming (suc to s; zero to z)
open import Data.Maybe

private
  variable
    ℓ : Level

module _ {K : Set ℓ} (R : OSet K) (V : Set) where
  open OSet R
  open OSet (ext {ℓ} {K} {R}) renaming
    (_≤_ to _≤Ex_; _≺_ to _≺Ex_; trans to transEx; compare to compareEx)
  -----------------------------------------------------------------------
  -- Basic balanced ordered tree implementation
  -----------------------------------------------------------------------
  data Tree (lu : Ext K × Ext K) : Nat → Set ℓ where
    leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → Tree lu 0 
    node : (k : K)
           (let (l , u) = lu)
           {n : Nat}
           (lt : Tree (l , # k) n)
           (rt : Tree (# k , u) n)
           → Tree lu (suc n)

  -----------------------------------------------------------------------
  -- Map implementation with keyset in type using tree for keyset
  -----------------------------------------------------------------------
  data TPMap {lu : Ext K × Ext K} : (n : Nat) → Tree lu n → Set ℓ where
    leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → TPMap 0 leaf 
    node : (p : K × V)
           (let (k , v) = p)
           (let (l , u) = lu)
           {n : Nat}
           {ls : Tree (l , # k) n} 
           → (lm : TPMap n ls)
           {rs : Tree (# k , u) n}
           → (rm : TPMap n rs)
           → TPMap (suc n) (node k ls rs)
