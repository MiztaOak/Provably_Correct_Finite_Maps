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
open import Function using (_∘_; _$_; const; case_of_)

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

  insertWith : {l u : Ext K} {h : ℕ} (k : K) (f : Maybe V → V)
               {{@erased l≤p : l ≺Ex  # k}} {{@erased p≤u : # k ≺Ex u}}
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

  insert : {l u : Ext K} {h : ℕ} (kv : K × V)
           {{@erased l≤p : l ≺Ex  (# (proj₁ kv))}}
           {{@erased p≤u :(# (proj₁ kv)) ≺Ex u}}
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

  record Cons (p : K × V) (l u : Ext K) (h : ℕ) : Set (ℓ ⊔ ℓ') where
    constructor cons
    field
      head : K × V
      @erased l<u : l ≺Ex # (proj₁ head)
      tail : ∃ λ i → BOBMap (# (proj₁ head) , u) (i ⊕ h)

  uncons : ∀ {l u h h1 h2}
           → ((k , v) : K × V)
           → h1 ~ h2 ⊔ h
           → BOBMap (l , # k) h1
           → BOBMap (# k , u) h2
           → Cons (k , v) l u h
  uncons p b (leaf {{l<u}}) r = cons p l<u (case b of
    λ { ~+ → 0# , r
      ; ~0 → 0# , r })
  uncons p b (node p' l c bl) r with uncons p' bl l c
  ... | cons head l<u tail = cons head l<u (case tail of
    λ { (1# , t) → 1# , node p t r b
      ; (0# , t) → case b of
        λ { ~- → 0# , node p t r ~0
          ; ~0 → 1# , node p t r ~+
          ; ~+ → rotL p t r } })

  reduce : ∀ {l y u h}
          → {{@erased l≤y : l ≺Ex y}}
          → BOBMap (y , u) h
          → BOBMap (l , u) h
  reduce {l} {y} {u} {{a}} (leaf {{b}}) = leaf {{transEx {l} {y} {u} a b}}
  reduce {{a}} (node p l r bal) = node p (reduce {{a}} l) r bal

  raise : ∀ {l y u h}
          → {{@erased y≤u : y ≺Ex u}}
          → BOBMap (l , y) h
          → BOBMap (l , u) h
  raise {x} {y} {z} {{a}} (leaf {{b}}) = leaf {{transEx {x} {y} {z} b a}}
  raise {{a}} (node p l r bal) = node p l (raise {{a}} r) bal

  join : {l u : Ext K} {k : K} {hl hr h : ℕ}
         → BOBMap (# k , u) hr
         → hl ~ hr ⊔ h
         → BOBMap (l , # k) hl
         → ∃ λ i → BOBMap (l , u) (i ⊕ h)
  join leaf ~- lt = 0# , (raise lt)
  join {l} {u} {k} (leaf {{k<u}}) ~0 (leaf {{l<k}}) =
    0# , (leaf {{transEx {l} {# k} {u} l<k k<u}})
  join (node p rlt rrt br) b tl with uncons p br rlt rrt
  ... | cons head l<u (1# , tr') = 1# , node head (raise {{l<u}} tl) tr' b
  ... | cons head l<u (0# , tr') with b
  ... | ~- = rotR head (raise {{l<u}} tl) tr'
  ... | ~0 = 1# , node head (raise {{l<u}} tl) tr' ~-
  ... | ~+ = 0# , node head (raise {{l<u}} tl) tr' ~0

-- * UNION STARTS HERE -----------------------------------------------------

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

  max : ℕ → ℕ → ℕ
  max n zero = n
  max zero n = n
  max (suc n) (suc m) = max n m

  {-# TERMINATING #-}
  concat3 : {h1 h2 : ℕ}
            → ((k , v) : K × V)
            → {l u : Ext K}
            → BOBMap (l , # k) h1
            → BOBMap (# k , u) h2
            → ∃ λ n → BOBMap (l , u) n
  concat3 p n (leaf {{pf}}) with insert p {{mklim n}} {{pf}} (raise {{pf}} n)
  ... | _ , t = _ , t
  concat3 p (leaf {{pf}}) m with insert p {{pf}} {{mklim m}} (reduce {{pf}} m)
  ... | _ , t = _ , t
  concat3 p@(k , v) n@(node p1 l1 r1 b1) m@(node p2 l2 r2 b2)
    with cmp (ratio * height n) (height m)
  ... | LT = let (i , cc) = concat3 p n l2
             in {!!} --balance p2 cc r2
  ... | EQ = {!!} , ?
  ... | GT = let (i , cc) = concat3 p r1 m
             in {!!} --balance p1 l1 cc

  splitLT : ∀ {l u h}
            → ((k , v) : K × V)
            → {{@erased l≤k : l ≺Ex  (# k)}}
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
            → {{@erased l≤u : # k ≺Ex u}}
            → BOBMap (l , u) h
            → ∃ λ n → BOBMap (# k , u) n
  splitGT x (leaf {{l<u}})= 0 , leaf
  splitGT (k , v) (node (k' , v') lt rt bal) with compare k k'
  ... | le = let (n , m) = splitGT (k , v) lt
             in concat3 (k' , v') m rt
  ... | eq = _ , rt
  ... | ge = splitGT (k , v) rt

  union : {h1 h2 : ℕ} → ∀ {l u}
          → (V → Maybe V → V)
          → BOBMap (l , u) h1
          → BOBMap (l , u) h2
          -- real height is i ⊕ max h1 h2
          -- but this caused issues in the n leaf case
          → ∃ λ n → BOBMap (l , u) (n ⊕ (max h1 h2))
  union f leaf (leaf ⦃ l≤u ⦄) = 0# , leaf ⦃ l≤u ⦄
  union f leaf (node p lm rm b) = 0# , node p lm rm b
  union f (node p lm rm b) leaf = 0# , node p lm rm b
  union {h1} {h2} f (node p1 lm1 rm1 b1) (node p2 lm2 rm2 b2) with
    splitLT p2 {{mklim lm2}} (node p1 lm1 rm1 b1)
  ... | lsh , ls with splitGT p2 {{mklim rm2}} (node p1 lm1 rm1 b1)
  ... | rsh , rs with union f ls lm2
  ... | llh , ll with union f rs rm2
  ... | rrh , rr = join {h = max h1 h2} rr {!!} ll

  -- * DELETE STARTS HERE ----------------------------------------------------

  delete : ∀ {l u : Ext K} {h : ℕ} (k : K)
           {{l≤p : l ≺Ex  (# k)}} {{p≤u :(# k) ≺Ex u}}
           → BOBMap (l , u) h
           → ∃ λ i → BOBMap (l , u) pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  delete k (node p lt rt bal)
    | le with lt
  ... | leaf = 1# , (node p leaf rt bal)
  ... | node pL ltL rtL balL with delete k (node pL ltL rtL balL)
  ... | 0# , lt' with bal
  ... | ~+ = rotL p lt' rt
  ... | ~0 = 1# , (node p lt' rt ~+)
  ... | ~- = 0# , (node p lt' rt ~0)
  delete k (node p lt rt bal)
    | le | node pL ltL rtL balL | 1# , lt' with bal
  ... | ~+ = 1# , (node p lt' rt ~+)
  ... | ~0 = 1# , node p lt' rt ~0
  ... | ~- = 1# , (node p lt' rt ~-)
  delete k (node p lt rt bal)
    | eq = join rt bal lt
  delete k (node p lt rt bal)
    | ge with rt
  ... | leaf = _ , (node p lt leaf bal )
  ... | node pR ltR rtR balR with delete k (node pR ltR rtR balR)
  ... | 0# , rt' with bal
  ... | ~+ = 0# , (node p lt rt' ~0)
  ... | ~0 = 1# , (node p lt rt' ~-)
  ... | ~- = rotR p lt rt'
  delete k (node p lt rt bal)
    | get | node pR ltR rtR balR | 1# , rt' with bal
  ... | ~+ = 1# , node p lt rt' ~+
  ... | ~0 = 1# , node p lt rt' ~0
  ... | ~- = 1# , node p lt rt' ~-

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
