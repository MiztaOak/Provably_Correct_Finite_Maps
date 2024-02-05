module Map.LPMap where

open import Prelude hiding (Rel; _≡_) 
open import OrdSet
open import Relation.Unary using (Pred) 
open import Relation.Nullary 
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

private
  variable 
    ℓ : Level

module _ {K : Set ℓ} (R : OSet K) (V : Set) where
 open OSet R
 open OSet (ext {ℓ} {K} {R}) renaming 
   (_≤_ to _≤Ex_; _≺_ to _≺Ex_; trans to transEx; compare to compareEx)

 Distinct : {A : Set ℓ} → Rel A ℓ
 Distinct x y = ¬ (x ≡ y)
   
 data OList (lu : Ext K × Ext K) : Set ℓ where
   []  : {{l≤u : (fst lu) ≺Ex (snd lu)}} → OList lu
   _∷_ : (p : K)
         (let (l , u) = lu)
         {{l≤p : (l ≺Ex # p)}}
         (ps : OList (# p , u))
         → OList lu

 _++_ : ∀ {l m u}
          (xs : OList (l , m))
          (ys : ∀{k} {{k≤m : (k ≺Ex m)}} → OList (k , u))
          → OList (l , u)
 (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
 []       ++ ys = ys

 infixr 1 _++_

 -- Binary ordered tree with the keys in the type signature
 -- this approach has one huge problem: How does it deal with rotations?
 data LPMap {lu : Ext K × Ext K} : (ks : OList lu) → Set ℓ where
   leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → LPMap []
   node : (p : K × V)
          (let (k , v) = p)
          (let (l , u) = lu)
          {ls : OList (l , # k)}
          {rs : OList (# k , u)}
          (lt : LPMap ls)
          (rt : LPMap rs)
          → LPMap (ls ++ (k ∷ rs)) 

 data _∈_ : K → {lu : Ext K × Ext K} {ks : OList lu} → LPMap ks → Set ℓ where
   here : ∀ {v : V} (k : K)
          → {l u : Ext K}
          {ls : OList (l , # k)}
          {lt : LPMap ls}
          {rs : OList (# k , u)}
          {rt : LPMap rs}
          → k ∈ (node (k , v) lt rt)

   left : ∀ {v : V} {k k' : K}
          → {l u : Ext K}
          {ls : OList (l , # k')}
          {lt : LPMap ls}
          → k ∈ lt
          → {rs : OList (# k' , u)}
          {rt : LPMap rs}
          → k ∈ (node (k' , v) lt rt)

   right : ∀ {v : V} {k k' : K}
         → {l u : Ext K} 
         {ls : OList (l , # k')}
         {lt : LPMap ls}
         {rs : OList (# k' , u)}
         {rt : LPMap rs}
         → k ∈ rt
         → k ∈ (node (k' , v) lt rt)
 
 insertK : ∀ {l u : Ext K} {ks : OList (l , u)}
           → LPMap ks → (k : K) 
           → {{l≤p : l ≺Ex (# k)}} {{p≤u : (# k ≺Ex u)}}
           → OList (l , u)
 insertK leaf k = k ∷ []
 insertK (node p {ls} {rs} lt rt) k with compare k (fst p)
 ... | le = insertK lt k ++ ((fst p) ∷ rs)
 ... | eq = ls ++ (k ∷ rs)
 ... | ge = ls ++ ((fst p) ∷ (insertK rt k))

 insert : ∀ {l u : Ext K} (kv : K × V) {ks : OList (l , u)}
            {{l≤p : l ≺Ex (# (fst kv))}} {{p≤u : (# (fst kv) ≺Ex u)}}
            → (t : LPMap ks) → LPMap (insertK t (fst kv)) 
 insert kv leaf = node kv leaf leaf 
 insert kv (node p lt rt) with compare (fst kv) (fst p)
 ... | le = node p (insert kv lt) rt
 ... | eq = node kv lt rt
 ... | ge = node p lt (insert kv rt)

 lookup : ∀ {l u : Ext K} {ks : OList (l , u)} → LPMap ks → K → Maybe V 
 lookup leaf q = nothing
 lookup (node (k , v) lt rt) q with compare q k
 ... | le = lookup lt q
 ... | eq = just v
 ... | ge = lookup rt q

 lookup∈ : ∀ {l u : Ext K} {ks : OList (l , u)} → (t : LPMap ks) → {k : K} → k ∈ t → V
 lookup∈ leaf ()
 lookup∈ (node .(_ , v) _ _) (here {v} _) = v
 lookup∈ (node .(_ , _) lt _) (left p)    = lookup∈ lt p
 lookup∈ (node .(_ , _) _ rt) (right p)   = lookup∈ rt p

 delete : ∀ {l u : Ext K} {ks : OList (l , u)} → LPMap ks
          → K → LPMap ks
 delete leaf _                 = leaf
 delete (node (k , v) lt rt) q with compare q k
 ... | le = node (k , v) (delete lt q) rt
 ... | eq = {!!}
 ... | ge = node (k , v) lt (delete rt q)
