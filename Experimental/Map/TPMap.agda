{-# OPTIONS --erasure #-}
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
  data Tree (lu : Ext K × Ext K) : Set ℓ where
    leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → Tree lu 
    node : (k : K)
           (let (l , u) = lu)
           (lt : Tree (l , # k))
           (rt : Tree (# k , u))
           → Tree lu

  insertT : ∀ {l u : Ext K} (k : K)
            {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
            → Tree (l , u) → Tree (l , u)
  insertT k leaf = node k leaf leaf
  insertT k (node k' lt rt) with compare k k'
  ... | le = node k' (insertT k lt) rt
  ... | eq = node k lt rt
  ... | ge = node k' lt (insertT k rt)

  -----------------------------------------------------------------------
  -- Map implementation with keyset in type using tree for keyset
  -----------------------------------------------------------------------
  data TPMap {lu : Ext K × Ext K} : Tree lu → Set ℓ where
    leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → TPMap leaf 
    node : (p : K × V)
           (let (k , v) = p)
           (let (l , u) = lu)
           {@0 ls : Tree (l , # k)} 
           → (lm : TPMap ls)
           {@0 rs : Tree (# k , u)}
           → (rm : TPMap rs)
           → TPMap (node k ls rs)

  data _∈_ : K → {lu : Ext K × Ext K} {ks : Tree lu} → TPMap ks → Set ℓ where
   here : ∀ {v : V} (k : K)
          → {l u : Ext K}
          {@0 ls : Tree (l , # k)}
          {lt : TPMap ls}
          {@0 rs : Tree (# k , u)}
          {rt : TPMap rs}
          → k ∈ (node (k , v) lt rt)

   left : ∀ {v : V} {k k' : K}
          → {l u : Ext K}
          {@0 ls : Tree (l , # k')}
          {lt : TPMap ls}
          → k ∈ lt
          → {@0 rs : Tree (# k' , u)}
          {rt : TPMap rs}
          → k ∈ (node (k' , v) lt rt)

   right : ∀ {v : V} {k k' : K}
         → {l u : Ext K} 
         {@0 ls : Tree (l , # k')}
         {lt : TPMap ls}
         {@0 rs : Tree (# k' , u)}
         {rt : TPMap rs}
         → k ∈ rt
         → k ∈ (node (k' , v) lt rt)

  insert : ∀ {l u : Ext K} (p : K × V)
            (let (k , v) = p)
            {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
            {ks : Tree (l , u)}
            → TPMap ks → TPMap (insertT k ks) 
  insert p leaf = node p leaf leaf
  insert (k , v) (node (k' , v') lt rt) with compare k k'
  ... | le = node (k' , v') (insert (k , v) lt) rt
  ... | eq = node (k , v) lt rt
  ... | ge = node (k' , v') lt (insert (k , v) rt)

  lookup : ∀ {l u : Ext K} {ks : Tree (l , u)} → TPMap ks → K → Maybe V 
  lookup leaf q = nothing
  lookup (node (k , v) lt rt) q with compare q k
  ... | le = lookup lt q
  ... | eq = just v
  ... | ge = lookup rt q
  
  lookup∈ : ∀ {l u : Ext K} {ks : Tree (l , u)} → (t : TPMap ks) → {k : K} → k ∈ t → V
  lookup∈ leaf ()
  lookup∈ (node .(_ , v) _ _) (here {v} _) = v
  lookup∈ (node .(_ , _) lt _) (left p)    = lookup∈ lt p
  lookup∈ (node .(_ , _) _ rt) (right p)   = lookup∈ rt p
 
  insert∈ : ∀ {l u : Ext K} {t : Tree (l , u)} {m : TPMap t} {k : K} {v : V}
            {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
            → k ∈ (insert (k , v) m)
  insert∈ {m = leaf} {k} = here k
  insert∈ {m = node p lt rt} {k} with compare k (fst p)
  ... | le = left (insert∈ {m = lt}) 
  ... | eq = here k
  ... | ge = right (insert∈ {m = rt})
