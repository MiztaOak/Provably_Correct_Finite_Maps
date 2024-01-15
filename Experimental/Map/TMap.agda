module Map.TMap where

open import Prelude 
open import OrdSet
open import Relation.Unary using (Pred)
open import Relation.Nullary.Negation -- using (¬_)

{-private
  Disitinct : {A : Set ℓ} → Rel A ℓ
  Disitinct x y = ¬ (x ≈ y) -} 

module _ {K : Set} (R : OSet K) (V : Set) where
 open OSet R
 open OSet (ext {K} {R}) renaming 
   (_≤_ to _≤Ex_; trans to transEx; compare to compareEx)

 data OList (lu : Ext K × Ext K) : Set where
   []  : {{l≤u : (fst lu) ≤Ex (snd lu)}} → OList lu
   _∷_ : (p : K)
         (let (l , u) = lu)
         {{l≤p : (l ≤Ex # p)}}
         (ps : OList (# p , u))
         → OList lu

 _++_ : ∀ {l m u}
          (xs : OList (l , m))
          (ys : ∀{k} {{k≤m : (k ≤Ex m)}} → OList (k , u))
          → OList (l , u)
 (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
 []       ++ ys = ys

 infixr 1 _++_

 -- Function that insert a element at the correct position in the list
 -- "replacing" the element if it is already in the list
 ⟦_+_⟧ : {l u : Ext K} → (k : K)
         {{l≤k : l ≤Ex # k}} {{k≤u : # k ≤Ex u}}
         → (xs : OList (l , u)) → OList (l , u)
 ⟦ k + [] ⟧ = k ∷ []
 ⟦_+_⟧ k ⦃ l≤k ⦄ ⦃ k≤u ⦄ (x ∷ xs) with compare k x
 ... | le = k ∷ (x ∷ xs)
 ... | eq = _∷_ k {{l≤k}} xs -- this might be the line that fucks it up 
 ... | ge = x ∷ ⟦ k + xs ⟧   -- since it removes an element which is not expected by olist

 ⟦_-_⟧ : {l u : Ext K} → (k : K)
         {{l≤k : l ≤Ex # k}} {{k≤u : # k ≤Ex u}}
         → (xs : OList (l , u)) → OList (l , u)
 ⟦ k - [] ⟧ = []
 ⟦ k - p ∷ xs ⟧ with compare k p
 ... | le = p ∷ xs
 ... | eq = {!xs!}
 ... | ge = p ∷ ⟦ k - xs ⟧

 -- Binary ordered tree with the keys in the type signature
 data TMap {lu : Ext K × Ext K} : (ks : OList lu) → Set where
   leaf : {{l≤u : (fst lu) ≤Ex (snd lu)}} → TMap []
   node : (p : K × V)
          (let (k , v) = p)
          (let (l , u) = lu)
          {ls : OList (l , # k)}
          {rs : OList (# k , u)}
          (lt : TMap ls)
          (rt : TMap rs) → TMap (ls ++ (k ∷ rs)) 
 
 insert : ∀ {l u : Ext K} (kv : K × V) {ks : OList (l , u)}
            {{l≤p : l ≤Ex (# (fst kv))}} {{p≤u : (# (fst kv) ≤Ex u)}}
            → TMap ks → TMap ⟦ fst kv + ks ⟧ 
 insert kv leaf = node kv leaf leaf 
 insert kv (node p lt rt) with compare (fst kv) (fst p)
 ... | le = {!node p (insert kv lt) rt!}
 ... | eq = {!node kv lt rt!}
 ... | ge = {!node p lt (insert kv rt)!}
