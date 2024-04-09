{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMap {k ℓ₁} (order : OrdSet k ℓ₁) where

Order : StrictTotalOrder k k ℓ₁
Order = toStrictTotalOrder order

open import Prelude
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Nat.Base
  using (ℕ; zero; suc; pred; _+_; _*_; _<_; _≤_; z<s; s<s; z≤n; s≤s; s≤s⁻¹)
  renaming (_⊔_ to max; compare to compareℕ; Ordering to Ordℕ)
open import Data.Nat.Properties
  using (n<1+n; ≤-refl; <⇒≤; m≤n⇒m≤1+n; ≤-trans; +-identityʳ; m≤n⇒m⊔n≡n; ⊔-comm; _≤?_; n≤0⇒n≡0; suc-injective)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Core using (Rel)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Function using (_∘_; _$_; const; case_of_)
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (yes; no)

open StrictTotalOrder Order using (compare) renaming (Carrier to Key)
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

  _∈_ : Key → {l u : Key⁺} {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ v)
  k ∈ m = Any {ℓₚ = 0ℓ} (λ _ → True) k m

  _∈?_ : ∀ {l u h} (x : Key)
         → (a : BOBMap V l u h)
         → Maybe (x ∈ a)
  _∈?_ x leaf = nothing
  _∈?_ x (node p lt rt bal) with compare x (proj₁ p)
  ... | tri< prf _ _ = _∈?_ x lt >>= λ α → just (left {{[ prf ]ᴿ}} α)
  ... | tri≈ _ refl _ = just $ here {{mklim lt}} {{mklim rt}} tt
  ... | tri> _ _ prf = (_∈?_ x rt) >>= λ α → just (right {{[ prf ]ᴿ}} α)

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

  -- * GENERAL JOIN STARTS HERE ----------------------------------------------

  -- TODO: Look over these lemmas
  lemR : {n m : ℕ} → max (suc (m + n)) m ≡ suc (m + n)
  lemR {n} {zero} = refl
  lemR {n} {suc m} rewrite lemR {n} {m} = refl

  lemRR+n : {n m : ℕ} → max (suc (suc (m + n))) m ≡ suc (suc (m + n))
  lemRR+n {n} {zero} = refl
  lemRR+n {n} {suc m} rewrite lemRR+n {n} {m} = refl

  lemRR : {m : ℕ} → max (suc (suc m)) m ≡ suc (suc m)
  lemRR {zero} = refl
  lemRR {suc m} rewrite lemRR {m} = refl

  lemL : {n m : ℕ} → max m (suc (m + n)) ≡ suc (m + n)
  lemL {n} {zero} = refl
  lemL {n} {suc m} rewrite lemL {n} {m} = refl

  lemLL+n : {n m : ℕ} → max m (suc (suc (m + n))) ≡ suc (suc (m + n))
  lemLL+n {n} {zero} = refl
  lemLL+n {n} {suc m} rewrite lemLL+n {n} {m} = refl

  lemC : {m : ℕ} → max m m ≡ m
  lemC {zero} = refl
  lemC {suc m} rewrite lemC {m} = refl

  lem4L : ∀ {a} → max (suc a) a ≡ suc a
  lem4L {zero} = refl
  lem4L {suc a} rewrite lem4L {a} = refl

  lem4Ln : ∀ {a n} → max (suc (a + n)) (a + n) ≡ suc (a + n)
  lem4Ln {zero} {n} rewrite lem4L {n} = refl
  lem4Ln {suc a} {n} rewrite lem4Ln {a} {n} = refl

  lem4R : ∀ {a} → max a (suc a) ≡ suc a
  lem4R {zero} = refl
  lem4R {suc a} rewrite lem4R {a} = refl
  -- END OF TODO

  data Balancing : Rel ℕ 0ℓ where
    left : ∀ hr k → Balancing (suc (suc (hr + k))) hr
    1-offL : ∀ h → Balancing (suc h) h
    balanced : ∀ h → Balancing h h
    1-offR : ∀ h → Balancing h (suc h)
    right : ∀ hl k → Balancing hl (suc (suc (hl + k)))

  compareBalance : ∀ hl hr → Balancing hl hr
  compareBalance zero zero = balanced zero
  compareBalance zero (suc zero) = 1-offR zero
  compareBalance zero (suc (suc b)) = right zero b
  compareBalance (suc zero) zero = 1-offL zero
  compareBalance (suc (suc a)) zero = left zero a
  {-# CATCHALL #-}
  compareBalance (suc a) (suc b) with compareBalance a b
  ... | left .b k = left (suc b) k
  ... | 1-offL .b = 1-offL (suc b)
  ... | balanced .a = balanced (suc a)
  ... | 1-offR .a = 1-offR (suc a)
  ... | right .a k = right (suc a) k

  postulate
    illegal~⊔2L : ∀ {a b c} → a ~ b ⊔ suc (suc a + c) → ⊥
    illegal~⊔2R : ∀ {a b c} → a ~ b ⊔ suc (suc b + c) → ⊥
    illegal~⊔3L : ∀ {a b c d} → a ~ b ⊔ suc (suc (suc a + c + d)) → ⊥
    illegal~⊔3R : ∀ {a b c d} → a ~ b ⊔ suc (suc (suc b + c + d)) → ⊥

  gJoinRight : {hr x : ℕ} {l u : Key⁺}
                → ((k , v) : Key × V)
                → BOBMap V l [ k ] (suc (suc (hr + x)))
                → BOBMap V [ k ] u hr
                → ∃ λ i → BOBMap V l u (i ⊕ suc (suc (hr + x)))
  gJoinRight {hr} {x} {ₗ} {ᵘ} p (node {hl = hl} {hr = hc} p2 l c b) r
    with compareBalance hc hr
  ... | left .hr k = joinʳ⁺ p2 l T' b
    where
      T' : ∃ λ i → BOBMap V [ proj₁ p2 ] ᵘ (i ⊕ hc)
      T' = gJoinRight p c r

  ... | 1-offL .hr = joinʳ⁺ p2 l T' b
    where
      T' : ∃ λ i → BOBMap V [ proj₁ p2 ] ᵘ (i ⊕ hc)
      T' = 1# , node p c r ~-

  ... | balanced .hr = joinʳ⁺ p2 l T' b
    where
      T' : ∃ λ i → BOBMap V [ proj₁ p2 ] ᵘ (i ⊕ hc)
      T' = 1# , node p c r ~0

  ... | right .hc k = ⊥-elim (illegal~⊔3R b )
  ... | 1-offR .hc = ⊥-elim (illegal~⊔2R b)

  gJoinLeft : {hl x : ℕ} {l u : Key⁺}
               → ((k , v) : Key × V)
               → BOBMap V l [ k ] hl
               → BOBMap V [ k ] u (suc (suc (hl + x)))
               → ∃ λ i → BOBMap V l u (i ⊕ suc (suc (hl + x)))
  gJoinLeft {hl} {x} {ₗ} {ᵘ} p l (node {hl = hc} {hr = hr} p2 c r b)
    with compareBalance hc hl
  ... | left     .hl k = joinˡ⁺ p2 T' r b
    where
      T' : ∃ λ i → BOBMap V ₗ [ proj₁ p2 ] (i ⊕ hc)
      T' = gJoinLeft p l c

  ... | 1-offL   .hl   = joinˡ⁺ p2 T' r b
    where
      T' : ∃ λ i → BOBMap V ₗ [ proj₁ p2 ] (i ⊕ hc)
      T' = 1# , node p l c ~+

  ... | balanced .hl   = joinˡ⁺ p2 T' r b
    where
      T' : ∃ λ i → BOBMap V ₗ [ proj₁ p2 ] (i ⊕ hc)
      T' = 1# , node p l c ~0

  ... | 1-offR .hc = ⊥-elim (illegal~⊔2L b)
  ... | right .hc k = ⊥-elim (illegal~⊔3L b)

  gJoin : {hl hr : ℕ} {l u : Key⁺}
          → ((k , v) : Key × V)
          → BOBMap V l [ k ] hl
          → BOBMap V [ k ] u hr
          → ∃ λ i → BOBMap V l u (i ⊕ max hl hr)
  gJoin {hl} {hr} p l r
    with compareBalance hl hr
  ... | left     .hr k rewrite lemRR+n {k} {hr} = gJoinRight p l r
  ... | 1-offL   .hr   rewrite lem4L {hr} = 1# , node p l r ~-
  ... | balanced .hl   rewrite lemC {hl}  = 1# , node p l r ~0
  ... | 1-offR   .hl   rewrite lem4R {hl} = 1# , node p l r ~+
  ... | right    .hl k rewrite lemLL+n {k} {hl} = gJoinLeft p l r

  -- * SPLIT STARTS HERE -----------------------------------------------------

  n≤n : ∀ {n} → n ≤ n
  n≤n {n} = ≤-refl

  n≤sn : ∀ {n} → n ≤ suc n
  n≤sn {n} = <⇒≤ (n<1+n n)

  record Split (x : Key) (l u : Key⁺) (h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor split
    field
      value : Maybe V
      leftT : ∃ λ hl → hl ≤ h × BOBMap V l [ x ] hl
      rightT : ∃ λ hr → hr ≤ h × BOBMap V [ x ] u hr

  bigbal : ∀ {a b c}
          → a ~ b ⊔ c
          → (a ≡ c × b ≡ a)
            ⊎ (a ≡ c × a ≡ suc b)
            ⊎ (b ≡ c × b ≡ suc a)
  bigbal ~+ = inr (inr (refl , refl))
  bigbal ~0 = inl (refl , refl)
  bigbal ~- = inr (inl (refl , refl))

  -- TODO: Talk about this
  lembal : ∀ {a b c}
           → a ~ b ⊔ c
           → (a < c × b ≤ c)
             ⊎ (a ≤ c × b < c)
             ⊎ (a ≤ c × b ≤ c)
  lembal {a} {b} {c} bal with bigbal bal
  -- LOL!! LOL!! LOL!!
  ... | inl (refl , refl) = inr (inr (n≤n , n≤n))
  ... | inr (inl (refl , refl)) = inr (inl (n≤n , n≤n))
  ... | inr (inr (refl , refl)) = inl (n≤n , n≤n)

  postulate
    lem≤max : ∀ {a b c} → a ≤ c → b ≤ c → max a b ≤ c

  lemin : ∀ {l u h}
          → {x : Key}
          → {m : BOBMap V l u h}
          → x ∈ m
          → ∃ λ n → suc n ≡ h
  lemin {h = h} {x = x} {m = leaf} ()
  lemin {h = suc h} {m = node (x , _) l r b} _ = h , refl

  -- what the hell??
  sa≤b⇒a≤sb : ∀ {a b} → suc a ≤ b → a ≤ suc b
  sa≤b⇒a≤sb {a} {b} prf = s≤s⁻¹ (m≤n⇒m≤1+n (m≤n⇒m≤1+n prf))

  splitAt : ∀ {l u h}
             → (k : Key)
             → {{@erased l<k : l <⁺ [ k ]}} → {{@erased k<u : [ k ] <⁺ u}}
             → (m : BOBMap V l u h)
             → Split k l u h
  splitAt {ₗ} {ᵘ} {zero} k leaf
    = split nothing (0 , z≤n , lt) (0 , z≤n , rt)
    where
      -- sinful stuff
      lt : BOBMap V ₗ [ k ] 0
      lt = leaf

      rt : BOBMap V [ k ] ᵘ 0
      rt = leaf

  splitAt {h = suc h} k (node (k' , v') l r b) with compare k k'
  splitAt {ₗ} {ᵘ} {h} k {{l<k = l<k}} (node {hl = hl} {hr = hr} (k' , v') l r b)
    | tri< x _ _ = split (Split.value leftS) lt rt
    where
      sh : ℕ
      sh = h

      leftS : Split k ₗ [ k' ] hl
      leftS = splitAt k {{l<k}} {{[ x ]ᴿ}} l

      lt : ∃ λ hl' → hl' ≤ sh × BOBMap V ₗ [ k ] hl'
      lt with lembal b
      lt | inr (inr (o , _)) with Split.leftT leftS
      lt | inr (inr (o , _)) | ht , ht<hl , t = ht , ≤-trans ht<hl (m≤n⇒m≤1+n o) , t
      lt | inr (inl (o , _)) with Split.leftT leftS
      lt | inr (inl (o , _)) | ht , ht<hl , t = ht , ≤-trans ht<hl (m≤n⇒m≤1+n o) , t
      lt | inl (o , _) with Split.leftT leftS
      lt | inl (o , _) | ht , ht<hl , t = ht , ≤-trans ht<hl (sa≤b⇒a≤sb o) , t

      -- a bit (very) convoluted, surely there are better ways to do this
      -- also uses a few lemmas which are not proven yet
      rt : ∃ λ hr' → hr' ≤ sh × BOBMap V [ k ] ᵘ hr'
      rt with Split.rightT leftS
      rt | ht , ht<hl , t with gJoin (k' , v') t r
      rt | ht , ht<hl , t | 0# , β with lembal b
      ... | inl (hl<h , hr≤h)
        = max ht hr , lem≤max (≤-trans ht<hl (sa≤b⇒a≤sb hl<h)) (m≤n⇒m≤1+n hr≤h) , β
      -- max ht hr , lem≤max (≤-trans ht<hl (m≤n⇒m≤1+n hl<h)) (m≤n⇒m≤1+n hr<h) , β
      ... | inr (inl (hl≤h , hr<h))
        = max ht hr , lem≤max (≤-trans ht<hl (m≤n⇒m≤1+n hl≤h)) (sa≤b⇒a≤sb hr<h) , β
      ... | inr (inr (hl≤h , hr≤h))
        = max ht hr , lem≤max (≤-trans ht<hl (m≤n⇒m≤1+n hl≤h)) (m≤n⇒m≤1+n hr≤h) , β
      rt | ht , ht<hl , t | 1# , β with lembal b
      ... | inl (hl<h , hr≤h)
        = suc (max ht hr)
        , s≤s (lem≤max (≤-trans ht<hl (s≤s⁻¹ (m≤n⇒m≤1+n hl<h))) hr≤h)
        , β
      ... | inr (inl (hl≤h , hr<h))
        = suc (max ht hr)
        , s≤s (lem≤max (≤-trans ht<hl hl≤h) (s≤s⁻¹ (m≤n⇒m≤1+n hr<h)))
        , β
      ... | inr (inr (hl≤h , hr≤h))
        = suc (max ht hr)
        , s≤s (lem≤max (≤-trans ht<hl hl≤h) hr≤h)
        , β

  splitAt {ₗ} {ᵘ} {h} k (node {hl = hl} {hr = hr} (.k , v') l r b)
    | tri≈ _ refl _ = split (just v') (hl , lt) (hr , rt)
    where
      sh : ℕ
      sh = h

      lt : hl ≤ sh × BOBMap V ₗ [ k ] hl
      lt with lembal b
      ... | inl (o , u) = sa≤b⇒a≤sb o , l
      ... | inr (inl (o , _)) = (m≤n⇒m≤1+n o) , l
      ... | inr (inr (o , _)) = (m≤n⇒m≤1+n o) , l

      rt : hr ≤ sh × BOBMap V [ k ] ᵘ hr
      rt with lembal b
      ... | inl (_ , p) = m≤n⇒m≤1+n p , r
      ... | inr (inl (o , u)) = m≤n⇒m≤1+n (<⇒≤ u) , r
      ... | inr (inr (o , u)) = m≤n⇒m≤1+n u , r

  splitAt {ₗ} {ᵘ} {h} k {{k<u = k<u}} (node {hl = hl} {hr = hr} (k' , v') l r b)
    | tri> _ _ x = split (Split.value rightS) lt rt
    where
      sh : ℕ
      sh = h

      rightS : Split k [ k' ] ᵘ hr
      rightS = splitAt k {{[ x ]ᴿ}} r

      rt : ∃ λ hr' → hr' ≤ sh × BOBMap V [ k ] ᵘ hr'
      rt with lembal b
      rt | inl (_ , o) with Split.rightT rightS
      ... | ht , ht<hr , t = ht , ≤-trans ht<hr (m≤n⇒m≤1+n o) , t
      rt | inr (inl (o , u)) with Split.rightT rightS
      ... | ht , ht<hr , t = ht , ≤-trans ht<hr (sa≤b⇒a≤sb u) , t
      rt | inr (inr (o , u)) with Split.rightT rightS
      ... | ht , ht<hr , t = ht , ≤-trans ht<hr (m≤n⇒m≤1+n u) , t

      lt : ∃ λ hl' → hl' ≤ sh × BOBMap V ₗ [ k ] hl'
      lt with Split.leftT rightS
      lt | ht , ht<hr , t with gJoin (k' , v') l t
      lt | ht , ht<hr , t | 0# , β with lembal b
      ... | inl (hl<h , hr≤h) =
          max hl ht
        , lem≤max (sa≤b⇒a≤sb hl<h) (≤-trans ht<hr (m≤n⇒m≤1+n hr≤h))
        , β
      ... | inr (inl (hl≤h , hr<h)) =
          max hl ht
        , lem≤max (m≤n⇒m≤1+n hl≤h) (≤-trans ht<hr (sa≤b⇒a≤sb hr<h))
        , β
      ... | inr (inr (hl≤h , hr≤h)) =
          max hl ht
        , lem≤max (m≤n⇒m≤1+n hl≤h) (≤-trans ht<hr (m≤n⇒m≤1+n hr≤h))
        , β
      lt | ht , ht<hr , t | 1# , β with lembal b
      ... | inl (hl<h , hr≤h) =
          suc (max hl ht)
        , s≤s (lem≤max (s≤s⁻¹ (m≤n⇒m≤1+n hl<h)) (≤-trans ht<hr hr≤h))
        , β
      ... | inr (inl (hl≤h , hr<h)) =
          suc (max hl ht)
        , s≤s (lem≤max hl≤h (≤-trans ht<hr (s≤s⁻¹ (m≤n⇒m≤1+n hr<h))))
        , β
      ... | inr (inr (hl≤h , hr≤h)) =
          suc (max hl ht)
        , s≤s (lem≤max hl≤h (≤-trans ht<hr hr≤h))
        , β

  -- * UNION STARTS HERE -----------------------------------------------------

  -- UNION DECLARATIONS ------------------------------------------------------
  unionRight : {hl n : ℕ} → {l u : Key⁺}
               → (V → Maybe V → V)
               → BOBMap V l u hl
               → BOBMap V l u (suc (hl + n))
               → ∃ λ i → BOBMap V l u (i ⊕ suc (hl + n))
  unionWith : {h1 h2 : ℕ} → ∀ {l u}
              → (V → Maybe V → V)
              → BOBMap V l u h1
              → BOBMap V l u h2
              → ∃ λ n → BOBMap V l u (n ⊕ max h1 h2)

  -- UNION IMPLEMENTATIONS ---------------------------------------------------

  unionWith {h1} {h2} f n m with compareℕ h1 h2
  ... | Ordℕ.less    .h1 k rewrite lemL {k} {h1} = {!!}
  ... | Ordℕ.equal   .h1   rewrite lemC {h1}     = {!!}
  ... | Ordℕ.greater .h2 k rewrite lemR {k} {h2} = unionRight f m n

  n+0 : ∀ {n} → n + 0 ≡ n
  n+0 {n} = +-identityʳ n

  sa+n : ∀ {a n} → suc (a + n) ≡ a + suc n
  sa+n {zero} {zero} = refl
  sa+n {zero} {suc n} = refl
  sa+n {suc a} {n} rewrite sa+n {a} {n} = refl

  ≤+n : ∀ {a b n} → a ≤ b → a ≤ b + n
  ≤+n {zero} {b} {n} p = z≤n
  {-# CATCHALL #-}
  ≤+n {a} {b} {zero} p rewrite n+0 {b} = p
  {-# CATCHALL #-}
  ≤+n {a} {b} {suc n} p with m≤n⇒m≤1+n (≤+n {a} {b} {n} p)
  ... | x rewrite sa+n {b} {n} = x

  lemgt : ∀ {a b c n} → b ≤ c → a ≡ c + n → max a b ≡ c + n
  lemgt {a} {b} {c} {n} p1 p2 with ≤+n {n = n} p1
  ... | x rewrite p2 with m≤n⇒m⊔n≡n x
  ... | y rewrite ⊔-comm b (c + n) = y

  postulate
    n⊔n≡n : ∀ n → max n n ≡ n
    mab≡mba : ∀ {a b} → max a b ≡ max b a

  n≡n⇒sn≡sn : ∀ {n} → n ≡ n → suc n ≡ suc n
  n≡n⇒sn≡sn {n} refl = refl

  sn≡sn⇒n≡n : ∀ {n} → suc n ≡ suc n → n ≡ n
  sn≡sn⇒n≡n {n} refl = refl

  lemm : ∀ {a b} → b ≤ a → max a b ≡ a
  lemm {zero} {zero} p1 = refl
  lemm {suc a} {zero} p1 = refl
  lemm {suc a} {suc b} p1 with b ≤? a
  ... | yes x rewrite lemm {a} {b} x = refl
  ... | no  x = contradiction (s≤s⁻¹ p1) x

  ⊔-0 : ∀ {n} → max n zero ≡ n
  ⊔-0 {zero} = refl
  ⊔-0 {suc n} = refl

  lemm+n : ∀ {a b n} → b ≤ a → max (a + n) b ≡ a + n
  lemm+n {zero} {zero} {n} p1 = ⊔-0 {n}
  lemm+n {suc a} {zero} {n} p1 = refl
  lemm+n {suc a} {suc b} {n} p1 with b ≤? a
  ... | yes x rewrite lemm+n {a} {b} {n} x = refl
  ... | no  x = contradiction (s≤s⁻¹ p1) x

  n≢sn : ∀ {n} → ¬ n ≡ suc n
  n≢sn {n} ()

  sa≰sb⇒a≰b : ∀ {a b} → ¬ (suc a) ≤ (suc b) → ¬ a ≤ b
  sa≰sb⇒a≰b {a} {b} sa≰sb a≤b = contradiction (s≤s a≤b) sa≰sb

  a≰b∧a≤sb⇒a=sb : ∀ {a b} → ¬ a ≤ b → a ≤ suc b → a ≡ suc b
  a≰b∧a≤sb⇒a=sb {zero} {b} p1 p2 = ⊥-elim (p1 z≤n)
  a≰b∧a≤sb⇒a=sb {suc a} {zero} p1 p2
    rewrite n≤0⇒n≡0 (s≤s⁻¹ p2) = refl
  a≰b∧a≤sb⇒a=sb {suc a} {suc b} p1 p2
    rewrite a≰b∧a≤sb⇒a=sb {a} {b} (sa≰sb⇒a≰b p1) (s≤s⁻¹ p2) = refl

  postulate
    a+sb≡sc⇒a+b≡c : ∀ {a b c} → a + suc b ≡ suc c → c ≡ a + b

  lemA : ∀ {hlʳ hrʳ hl n hL hR}
         → hlʳ ~ hrʳ ⊔ hl + n
         → hL ≤ hl
         → hR ≤ hl
         → max hlʳ hL ~ max hrʳ hR ⊔ hl + n
  lemA {hlʳ} {hrʳ} {hl} {zero} {hL} {hR} b hl<hl hr<hl
    rewrite n+0 {hl} with bigbal b
  ... | inl (refl , refl)
    rewrite lemm hl<hl rewrite lemm hr<hl = b
  ... | inr (inl (refl , refl))
    rewrite lemm hl<hl rewrite lemm hr<hl = fun
    where
      fun : suc hrʳ ~ max hrʳ hR ⊔ suc hrʳ
      fun with hR ≤? hrʳ
      ... | yes x rewrite lemm x = ~-
      ... | no  x rewrite a≰b∧a≤sb⇒a=sb x hr<hl rewrite lem4R {hrʳ} = ~0
  ... | inr (inr (refl , refl))
    rewrite lemm hl<hl rewrite lemm hr<hl = fun
    where
      fun : max hlʳ hL ~ suc hlʳ ⊔ suc hlʳ
      fun with hL ≤? hlʳ
      ... | yes x rewrite lemm x = b
      ... | no  x rewrite a≰b∧a≤sb⇒a=sb x hl<hl rewrite lem4R {hlʳ} = ~0
  lemA {hlʳ} {hrʳ} {hl} {suc n} {hL} {hR} b hl<hl hr<hl
    with bigbal b
  ... | inl (refl , refl)
    rewrite lemm+n {n = suc n} hl<hl rewrite lemm+n {n = suc n} hr<hl = b
  ... | inr (inl (refl , t))
    rewrite lemm+n {n = suc n} hl<hl
    rewrite a+sb≡sc⇒a+b≡c t
    rewrite lemm+n {n = n} hr<hl = b
  ... | inr (inr (refl , t))
    rewrite lemm+n {n = suc n} hr<hl
    rewrite a+sb≡sc⇒a+b≡c t
    rewrite lemm+n {n = n} hl<hl = b

  postulate
    tttt : ∀ {a b n} → a + suc n ≡ suc b → a + n ≡ b
    pppp : ∀ {a b c n} → c + n ≡ a → b ≤ c → max a b ≡ a

  ssss : ∀ {a b c n}
         → c + n ≡ suc a
         → b ≤ c
         → suc (max a b) ≡ c + n ⊎ suc (max a b) ≡ suc c + n
  ssss {a} {b} {c} {zero} c0=sa b<c
    rewrite n+0 {c}
    rewrite c0=sa
    with b ≤? a
  ... | yes x
    rewrite lemm x = inl refl
  ... | no  x
    rewrite a≰b∧a≤sb⇒a=sb x b<c
    rewrite lem4R {a}
    = inr refl
  ssss {a} {b} {c} {suc n} c0=sa b<c
    rewrite c0=sa
    with b ≤? a
  ... | yes x
    rewrite lemm x = inl refl
  ... | no  x
    rewrite pppp (tttt c0=sa) b<c
    = inl refl

  sss2 : ∀ {a b c n}
         → c + n ≡ suc a
         → b ≤ c
         → max (suc a) (max a b) ≡ suc a
  sss2 {a} {b} {c} c0=sa b<c with ssss c0=sa b<c
  ... | inr x
    rewrite n+0 {c}
    rewrite suc-injective x
    rewrite c0=sa
    rewrite n⊔n≡n a
    = refl
  ... | inl x
    rewrite n+0 {c}
    rewrite c0=sa
    rewrite suc-injective x
    rewrite lem4L {a}
    = refl

  sss2L : ∀ {a b c n}
          → c + n ≡ suc a
          → b ≤ c
          → max (max a b) (suc a) ≡ suc a
  sss2L {a} {b} {c} p1 p2 with sss2 p1 p2
  ... | x rewrite mab≡mba {max a b} {suc a} = x

  -- Optimization
  -- unionRight f leaf (node p l r b) = 0# , (node p l r b)
  -- {-# CATCHALL #-}
  unionRight {hl} f m (node p l r b)
    with splitAt (proj₁ p) {{mklim l}} {{mklim r}} m
  unionRight {hl} f m (node p l r b)
    | split value (hL , prfL , treeL) (hR , prfR , treeR)
    with unionWith f l treeL
  unionRight {hl} {n} {ₗ} {ᵘ} f m (node {hlʳ} {hrʳ} (k , v) l r b)
    | split value (hL , prfL , treeL) (hR , prfR , treeR)
    | 0# , t1 = joinʳ⁺ (k , f v value) t1 (unionWith f r treeR) (lemA b prfL prfR)
  unionRight {hl} {n} {ₗ} {ᵘ} f m (node {hlʳ} {hrʳ} (k , v) l r b)
    | split value (hL , prfL , treeL) (hR , prfR , treeR)
    | 1# , t1 with unionWith f r treeR
  ... | j , t2 =  lem (gJoin (k , f v value) t1 t2)
    where
      lem : ∃ (λ i → BOBMap V ₗ ᵘ (i ⊕ max (suc (max hlʳ hL)) (j ⊕ max hrʳ hR)))
          → ∃ (λ i → BOBMap V ₗ ᵘ (i ⊕ suc (hl + n)))
      lem (i , t) = i , {!!}
{-
      joiner : ∃ λ i → BOBMap V ₗ ᵘ (i ⊕ suc (hl + zero))
      joiner with bigbal b
      joiner | inl (refl , refl) with gJoin (k , f v value) t1 t2
      ... | i , t -- why is this needed?
        rewrite lemm+n {n = zero} prfR
        rewrite lemm+n {n = zero} prfL
        rewrite lem4L {hl + zero}
        = i , t
      joiner | inr (inl (refl , t)) with ssss t prfR , gJoin (k , f v value) t1 t2
      ... | inr x , i , res
        rewrite lemm+n {n = zero} prfL
        rewrite n+0 {hl}
        rewrite suc-injective x
        rewrite lem4L {hl}
        = i , res
      ... | inl x , i , res
        rewrite lemm+n {n = zero} prfL
        rewrite n+0 {hl}
        rewrite sym x
        rewrite lemRR {max hrʳ hR}
        = i , res
      joiner | inr (inr (refl , t)) with ssss t prfL
      ... | inl x
        rewrite lemm+n {n = zero} prfR
        rewrite n+0 {hl}
        rewrite x
        = joinʳ⁺ (k , f v value) t1 (0# , t2) ~0
      ... | inr x
        rewrite lemm+n {n = zero} prfR
        rewrite n+0 {hl}
        rewrite x
        with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite lem4L {hl}= i , res
  ... | 1# , t2 = joiner --{!gJoin (k , f v value) t1 t2!}
    where
      joiner : ∃ λ i → BOBMap V ₗ ᵘ (i ⊕ suc (hl + zero))
      joiner
        with bigbal b
      joiner | inl (refl , refl) with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite n+0 {hl}
        rewrite lemm prfL
        rewrite lemm prfR
        rewrite n⊔n≡n hl
        = i , res
      joiner | inr (inl (refl , t)) with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite lemm+n {n = zero} prfL
        rewrite t
        rewrite sss2 t prfR
        = i , res
      joiner | inr (inr (refl , t)) with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite lemm+n {n = zero} prfR
        rewrite t
        rewrite sss2L t prfL
        = i , res


  unionRight {hl} {suc n} {ₗ} {ᵘ} f m (node {hlʳ} {hrʳ} (k , v) l r b)
    | split value (hL , prfL , treeL) (hR , prfR , treeR)
    | 1# , t1 with unionWith f r treeR
  ... | 0# , t2 = joiner
    where
      N : ℕ
      N = suc n

      joiner : ∃ λ i → BOBMap V ₗ ᵘ (i ⊕ suc (hl + N))
      joiner with bigbal b
      joiner | inl (refl , refl) with gJoin (k , f v value) t1 t2
      ... | i , t -- why is this needed?
        rewrite lemm+n {n = N} prfR
        rewrite lemm+n {n = N} prfL
        rewrite lem4L {hl + N}
        = i , t
      joiner | inr (inl (refl , t))
        with gJoin (k , f v value) t1 t2
      ... | i , x -- again
        rewrite lemm+n {n = N} prfL
        rewrite t
        rewrite pppp {hrʳ} {hR} {hl} {n} (tttt t) prfR
        rewrite lemRR {hrʳ}
        = i , x
      joiner | inr (inr (refl , t)) with pppp {hlʳ} {hL} {hl} {n} (tttt t) prfL
      ... | x
        rewrite x
        rewrite lemm+n {n = N} prfR
        rewrite t
        = joinʳ⁺ (k , f v value) t1 (0# , t2) ~0
  ... | 1# , t2 = joiner
    where
      N : ℕ
      N = suc n

      joiner : ∃ λ i → BOBMap V ₗ ᵘ (i ⊕ suc (hl + N))
      joiner
        with bigbal b
      joiner | inl (refl , refl) with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite lemm+n {n = N} prfL
        rewrite lemm+n {n = N} prfR
        rewrite n⊔n≡n (hl + N)
        = i , res
      joiner | inr (inl (refl , t)) with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite lemm+n {n = N} prfL
        rewrite t
        rewrite sss2 t prfR
        = i , res
      joiner | inr (inr (refl , t)) with gJoin (k , f v value) t1 t2
      ... | i , res
        rewrite lemm+n {n = N} prfR
        rewrite t
        rewrite sss2L t prfL
        = i , res
{-

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

-- -}
-- -}
-- -}
-- -}
-- -}
