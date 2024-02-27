{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Map.BOBMap where

open import Prelude
open import OrdSet
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _<_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Maybe
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Function using (_∘_; _$_; const)

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
    leaf : {{@erased l≤u : (proj₁ lu) ≺Ex (proj₂ lu)}} → BOBMap lu 0
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

  insertWith : ∀ {l u : Ext K} {h : ℕ} (k : K) (f : Maybe V → V)
               {{@erased l≤p : l ≺Ex  (# k)}} {{@erased p≤u :(# k) ≺Ex u}}
               → BOBMap (l , u) h
               → ∃ λ i → BOBMap (l , u) (i ⊕ h)
  insertWith k f leaf = 1# , node (k , f nothing) leaf leaf ~0
  insertWith k f (node p lt rt bal) with compare k (proj₁ p)
  insertWith k f (node p lt rt bal)
    | le with insertWith k f lt
  ... | 0# , t = 0# , (node p t rt bal)
  ... | 1# , t with bal
  ... | ~+ = 0# , (node p t rt ~0)
  ... | ~0 = 1# , (node p t rt ~-)
  ... | ~- = rotR p t rt
  insertWith k f (node p lt rt bal)
    | eq = 0# , (node (k , f (just (proj₂ p))) lt rt bal)
  insertWith k f (node p lt rt bal)
    | ge with insertWith k f rt
  ... | 0# , t = 0# , (node p lt t bal)
  ... | 1# , t with bal
  ... | ~+ = rotL p lt t
  ... | ~0 = 1# , (node p lt t ~+)
  ... | ~- = 0# , (node p lt t ~0)

  insert : ∀ {l u : Ext K} {h : ℕ} (kv : K × V)
            {{l≤p : l ≺Ex  (# (proj₁ kv))}} {{p≤u :(# (proj₁ kv)) ≺Ex u}}
            → BOBMap (l , u) h
            → ∃ λ i → BOBMap (l , u) (i ⊕ h)
  insert (k , v) m = insertWith k (λ _ → v) m

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

  -- * UNION STARTS HERE -----------------------------------------------------

  reduce : ∀ {l y u h}
          → @erased l ≺Ex y
          → BOBMap (y , u) h
          → BOBMap (l , u) h
  reduce {x} {y} {z} a (leaf {{b}}) = leaf {{transEx {x} {y} {z} a b}}
  reduce a (node p l r bal) = node p (reduce a l) r bal

  raise : ∀ {l y u h}
          → @erased y ≺Ex u
          → BOBMap (l , y) h
          → BOBMap (l , u) h
  raise {x} {y} {z} a (leaf {{b}}) = leaf {{transEx {x} {y} {z} b a}}
  raise a (node p l r bal) = node p l (raise a r) bal

  -- O(n) operation, not good!
  @erased mklim : ∀ {l u h}
          → BOBMap (l , u) h
          → l ≺Ex u
  mklim (leaf {{p}}) = p
  mklim {l} {u} (node p lt rt bal) = transEx {l} {_} {u} (mklim lt) (mklim rt)

  height : ∀ {h l u} → BOBMap (l , u) h → ℕ
  height {h} _ = h

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

  balance : ∀ {l u h} → BOBMap (l , u) h → ∃ λ n → BOBMap (l , u) n
  balance = {!!}

  {-# TERMINATING #-} -- does it though?
  concat3 : {h1 h2 : ℕ} → {l u : Ext K}
            → ((k , v) : K × V)
            -- → {{l≤k : l ≺Ex (# k)}} → {{k≤u : (# k) ≺Ex u}}
            → BOBMap (l , # k) h1
            → BOBMap (# k , u) h2
            → ∃ λ n → BOBMap (l , u) n
  concat3 = {!!}
{-
  concat3 {h} {_} {l} {u} (k , v) {{p1}} {{p2}} n leaf
    with insertWith {l} {u} k (const v) {{p1}} {{p2}} (raise p2 n)
  ... | fst , snd = (fst ⊕ h) , snd
  concat3 {_} {h} {l} {u} (k , v) {{p1}} {{p2}} leaf m
    with insertWith {l} {u} k (const v) {{p1}} {{p2}} (reduce p1 m)
  ... | fst , snd = (fst ⊕ h) , snd
  concat3 {h1} {h2} {l} {u} (k , v)
          {{p1}} {{p2}}
          n@(node kv1 l1 r1 b1) m@(node kv2 l2 r2 bal2)
    with cmp (ratio * h1) h2
  ... | LT = let (i , cc) = concat3 (k , v) {{p1}} {{mklim l2}} n l2
             in balance (node kv2 cc r2 {!!})
  ... | EQ = {!!} , node (k , v) n m {!!}
  ... | GT = let (i , cc) = concat3 (k , v) {{mklim r1}} {{p2}} r1 m
             in balance (node kv1 l1 cc {!!})
-}
  splitLT : ∀ {l u h}
            → ((k , v) : K × V)
            → {{@erased l≤k : l ≺Ex  (# k)}} -- {{@erased k≤u :(# k) ≺Ex u}}
            → BOBMap (l , u) h
            → ∃ λ n → BOBMap (l , # k) n
  splitLT x (leaf {{l<u}}) = 0 , leaf

  splitLT (k , v) (node (k' , v') lt rt bal) with compare k k'
  ... | le = splitLT (k , v) lt
  ... | ge = let (n , m) = splitLT (k , v) rt
             in concat3 (k' , v') lt m
  ... | eq = _ , lt

  splitGT : ∀ {l u h}
            → ((k , v) : K × V)
            -- → {{@erased l≤p : l ≺Ex # k}}
            → {{@erased p≤u : # k ≺Ex u}}
            → BOBMap (l , u) h
            → ∃ λ n → BOBMap (# k , u) n
  splitGT = {!!}

{-
  splitGT : ∀ {l u h}
            → ((p , v) : K × V)
            → BOBMap (l , u) h
            → ∃ λ n → BOBMap (# p , u) n
  splitGT x leaf = 0 , leaf
  splitGT (x , y) (node (k , v) lt rt bal) with compare k x
  ... | le = let (n , m) = splitGT (x , y) lt
             in n , raise (mklim rt) m
  ... | eq = height rt , reduce (mklim lt) rt
  ... | ge = let (i1 , t1) = splitGT (x , y) lt
             in concat3 (k , v) {- {{mklim t1}} {{mklim rt}} -} t1 rt

  least : Ext K → Ext K → Ext K
  least ⊥ n = ⊥
  least n ⊥ = ⊥
  least ⊤ n = n
  least n ⊤ = n
  least (# a) (# b) with compare a b
  ... | le = # a
  ... | eq = # a
  ... | ge = # b

  great : Ext K → Ext K → Ext K
  great ⊥ n = n
  great n ⊥ = n
  great ⊤ n = ⊤
  great n ⊤ = ⊤
  great (# a) (# b) with compare a b
  ... | le = # b
  ... | eq = # a
  ... | ge = # a
-- -}

  union : {h1 h2 : ℕ} → ∀ {l u}
          → (V → Maybe V → V)
          → BOBMap (l , u) h1
          → BOBMap (l , u) h2
          → ∃ λ h → BOBMap (l , u) h
  union f leaf m = _ , m
  union f n leaf = _ , n
  union f n (node p lt rt bal)
    = let (_ , ls) = splitLT p {{mklim lt}} n
          (_ , rs) = splitGT p {{mklim rt}} n
          (_ , ll) = union f ls lt
          (_ , rr) = union f rs rt
      in concat3 p ll rr

  -- * DELETE STARTS HERE ----------------------------------------------------

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

  foldr : ∀ {l u} {h : ℕ} {n : Level} {A : Set n}
          → (K × V → A → A)
          → A
          → BOBMap (l , u) h
          → A
  foldr f g leaf = g
  foldr f g (node p l r bal) = foldr f (f p (foldr f g r)) l

{-

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

  link : ∀ {h1 h2}
         → (k : K)
         → ∀ {l u x y}
         → {{l≤p : l ≺Ex  (# k)}} → {{p≤u :(# k) ≺Ex u}}
         → (Maybe V → V)
         → {{l≤y : l ≺Ex y}} → {{x≤u : x ≺Ex u}}
         → BOBMap (l , x) h1
         → BOBMap (y , u) h2
         → ∃ λ n → BOBMap (l , u) n
  link {h1} {h2} k {l} {u} {x} {y} {{p4}} {{p5}} f {{p1}} {{p2}} (leaf {{p3}}) m
    with insertWith {l} {u} k f {{p4}} {{p5}} (reduce p1 m)
  ... | fst , snd = (fst ⊕ h2) , snd
  link {h1} {h2} k {l} {u} {x} {y} {{p4}} {{p5}} f {{p1}} {{p2}} n (leaf {{p3}})
    with insertWith {l} {u} k f {{p4}} {{p5}} (raise p2 n)
  ... | fst , snd = (fst ⊕ h1) , snd
  link {h1} {h2} k f n@(node (k1 , _) l1 r1 bal1) m@(node (k2 , _) l2 r2 bal2)
    with cmp (ratio * h1) h2
  ... | LT = let (i1 , t1) = link k f n {!!}
             in {!!}
  ... | EQ = {!!}
  ... | GT = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
