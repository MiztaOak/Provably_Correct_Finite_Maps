module Map.BSTMap where

open import Prelude
open import OrdSet
open import Level

data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just : A → Maybe A

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {K : Set ℓ} (V : Set ℓ') (R : OSet K) where
  open OSet R
  open OSet (ext {ℓ} {K} {R}) renaming 
   (_≤_ to _≤Ex_;_≺_ to _≺Ex_; trans to transEx; compare to compareEx)

  -- BST based map implementation
  data BSTMap (lu : Ext K × Ext K) : Set (ℓ ⊔ ℓ') where
    leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → BSTMap lu
    node : (p : K × V)
           (let (k , v) = p)
           (let (l , u) = lu)
           (lt : BSTMap (l , # k))
           (rt : BSTMap (# k , u)) → BSTMap lu

  data _∈_ {lu : Ext K × Ext K} : K → BSTMap lu → Set (ℓ ⊔ ℓ') where
    here : ∀ {v : V} (k : K)
           → (let (l , u) = lu)
           {lt : BSTMap (l , # k)}
           {rt : BSTMap (# k , u)}
           → k ∈ (node (k , v) lt rt)
    left : ∀ {v : V} {k k' : K}
           → (let (l , u) = lu)
           {lt : BSTMap (l , # k')}
           → k ∈ lt
           → {rt : BSTMap (# k' , u)}
           → k ∈ (node (k' , v) lt rt)
    right : ∀ {v : V} {k k' : K}
           → (let (l , u) = lu)
           {lt : BSTMap (l , # k')}
           {rt : BSTMap (# k' , u)}
           → k ∈ rt
           → k ∈ (node (k' , v) lt rt)

  data Env {lu : Ext K × Ext K} (f : V → Set ℓ'') : BSTMap lu → Set (ℓ ⊔ (ℓ' ⊔ ℓ'')) where
    leaf : {{l≤u : (fst lu) ≺Ex (snd lu)}} → Env f leaf
    node : {p : K × V}
           (let (k , v) = p)
           (let (l , u) = lu)
           → f v
           → {lt : BSTMap (l , # k)}
           → Env f lt
           → {rt : BSTMap (# k , u)} 
           → Env f rt
           → Env f (node p lt rt)
{-
  mapOrd : ∀ {l u : Ext K} → BSTMap (l , u) → l ≤Ex u
  mapOrd {l} {u} (leaf ⦃ l≤u ⦄) = l≤u
  mapOrd {l} {u} (node p lt rt) = transEx {x = l} {z = u} (mapOrd lt) (mapOrd rt)
-}
  insert : (V × V → V) → ∀{l u : Ext K} (kv : K × V) 
            {{l≤p : l ≺Ex  (# (fst kv))}} {{p≤u :(# (fst kv)) ≺Ex u}}
            → (t : BSTMap (l , u)) → BSTMap (l , u)
  insert f kv leaf = node kv leaf leaf 
  insert f kv (node p lt rt) with compare (fst kv) (fst p)
  ... | le = node p (insert f kv lt ) rt
  ... | eq = node (fst kv , f (snd kv , snd p)) lt rt
  ... | ge = node p lt (insert f kv rt) 

  insert∈ : ∀ {l u : Ext K} {m : BSTMap (l , u)} {k : K} {v : V}
            {f : V × V → V}
            {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
            → k ∈ (insert f (k , v) m)
  insert∈ {m = leaf} {k} = here k
  insert∈ {m = node p lt rt} {k} with compare k (fst p)
  ... | le = left (insert∈ {m = lt}) 
  ... | eq = here k
  ... | ge = right (insert∈ {m = rt})

  lookup : ∀ {l u : Ext K} → BSTMap (l , u) → K → Maybe V
  lookup leaf k = nothing
  lookup (node (k' , v) lt rt) k with compare k k'
  ... | le = lookup lt k
  ... | ge = lookup rt k
  ... | eq = just v

  lookup∈ : ∀ {l u : Ext K} → (t : BSTMap (l , u)) → {k : K} → k ∈ t → V
  lookup∈ leaf ()
  lookup∈ (node .(_ , v) lt rt) (here {v} _) = v
  lookup∈ (node .(_ , _) lt rt) (left p) = lookup∈ lt p
  lookup∈ (node .(_ , _) lt rt) (right p) = lookup∈ rt p
{-
  merge : ∀ {l u k : Ext K} → BSTMap (l , k) → BSTMap (k , u) → BSTMap (l , u)
  merge {l} {u} {k} (leaf ⦃ x ⦄) (leaf ⦃ y ⦄) = leaf {{transEx {l} {k} {u} x y}}
  merge (node p lt rt) leaf = node p lt (merge rt leaf)
  merge leaf (node p lt rt) = node p (merge leaf lt) rt
  merge {l} {u} {k} (node p₁ lt₁ rt₁) (node p₂ lt₂ rt₂) = t'
    where
      p : l ≤Ex # (fst p₂)
      p = transEx {l} {k} {# (fst p₂)} (transEx {l} {z = k} (mapOrd lt₁) (mapOrd rt₁)) (mapOrd lt₂)
      t' : BSTMap (l , u)
      t' = insert fst p₂ {{p}} {{mapOrd rt₂}} (merge (merge (node p₁ lt₁ rt₁) lt₂) rt₂)

  delete : ∀ {l u : Ext K} → BSTMap (l , u) → K → BSTMap (l , u)
  delete leaf k = leaf
  delete (node (k' , v) lt rt) k with compare k k'
  ... | le = node (k' , v) (delete lt k) rt
  ... | ge = node (k' , v) lt (delete rt k)
  ... | eq = merge lt rt 
-}

  -- Ordered lists

  data OList (lu : Ext K × Ext K) : Set (ℓ ⊔ ℓ') where
    []  : {{l≤u : (fst lu) ≺Ex (snd lu)}} → OList lu
    _∷_ : (p : K × V)
          (let (l , u) = lu)
          {{l≤p : (l ≺Ex # (fst p))}}
          (ps : OList (# (fst p) , u)) → OList lu

  -- Flattening a BST

  _++_ : ∀{l m u}
          (xs : OList (l , m))
          (ys : ∀{k} {{k≤m : (k ≺Ex m)}} → OList (k , u)) → OList (l , u)
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
  []       ++ ys = ys

  infixr 1 _++_
{-
  flatten : ∀{lu} (t : BSTMap lu) → OList lu
  flatten leaf     = []
  flatten (node p lt rt) = flatten lt ++ (p ∷ flatten rt)

  tree : (xs : List (K × V)) → BSTMap (⊥ , ⊤)
  tree nil = leaf {{record {}}}
  tree (cons x xs) = insert fst x {{record {}}} {{record {}}} (tree xs)

  -- Sorting is flatten ∘ tree

  sort : (xs : List (K × V)) → OList (⊥ , ⊤)
  sort xs = flatten (tree xs)

xs : List (Nat × Nat)
xs = cons (5 , 4) (cons (0 , 10) (cons (5 , 11) (cons (2 , 4) nil)))
     
sorted = sort Nat OSetℕ xs 

module _ {K : Set ℓ} {R : OSet K} where
  map : ∀ {l u : Ext K} {A : Set ℓ} {B : Set ℓ'} → (A → B)→ BSTMap A R (l , u) → BSTMap B R (l , u)
  map f leaf = leaf
  map f (node (k , v) lt rt) = node (k , f v) (map f lt) (map f rt)
  -}
