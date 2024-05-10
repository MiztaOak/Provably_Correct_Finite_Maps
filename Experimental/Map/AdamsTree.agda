{-# OPTIONS --erasure #-}

module Map.AdamsTree where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Nat.Base renaming (Ordering to Ordℕ)
open import Data.Nat.Properties
open import Data.Product
open import Function using (_∘_; _$_; const; case_of_)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Definitions

open import Map.UnionLemmas

variable
  ω : ℕ

data Value : Set where

postulate
  [_] : ℕ → ℕ

data balance (c : ℕ) : ℕ → ℕ → Set where
  bal : ∀ {a b} → ∣ a - b ∣ ≤ c → balance c a b

data ATree (l u : ℕ) : @erased ℕ → Set where
  leaf : {{l < u}} → ATree l u 0
  node : {sl sr : ℕ}
    → (v : ℕ)
    → (lt : ATree l v sl)
    → (rt : ATree v u sr)
    -- this causes issues with matching on sl and sr for some reason
--    → {{ b : ∣ sl - sr ∣ ≤ ω }}
    → ATree l u (suc (sl + sr))

mklim : ∀ {l u s}
  → ATree l u s
  → l < u
mklim (leaf ⦃ l<u ⦄) = l<u
mklim (node v lt rt) = <-trans (mklim lt) (mklim rt)

join : ∀ {sl sr l u}
  → (v : ℕ)
  → ATree l v sl
  → ATree v u sr
  → ATree l u (1 + sl + sr)
join = {!!}

ℕ₂ = Fin 2
pattern 0# = fzero
pattern 1# = fsuc fzero
pattern ## = fsuc (fsuc ())

infixl 6 _⊕_

_⊕_ : ℕ₂ → ℕ → ℕ
0# ⊕ n = n
1# ⊕ n = 1 + n

data Split {l u s : ℕ} (v : ℕ) (m : ATree l u (suc s)) : Set where
  split : ∀ {sl sr}
    → Maybe ℕ
    → ATree l v sl
    → ATree v u sr
    → (∃ λ i → i ⊕ s ≡ sl + sr)
    → Split v m

postulate
  compv : Trichotomous _≡_ _<_

splitAt : ∀ {s l u}
  → (v : ℕ)
  → {{l < v}} → {{v < u}}
  → (m : ATree l u (suc s))
  → Split v m
splitAt {s} {l} {u} v t@(node w lt rt) with compv v w
splitAt {s} {l} {u} v {{p1}} t@(node w leaf rt) | tri< a ¬b ¬c = ans
  where
    ans : Split v t
    ans = split nothing (leaf {{p1}}) (join w (leaf {{a}}) rt) (1# , refl)

splitAt {s} {l} {u} v {{p1}} t@(node w lt@(node {sl} {sr} _ _ _) rt)
  | tri< a ¬b ¬c with splitAt v {{p1}} {{a}} lt
... | split value ll rr prf
  = split value ll (join w rr rt) (ans {sl} {sr} prf)
  where
    -- mirror for right
    ans : ∀ {sl sr sl₁ sr₁ sr₂}
      → (∃ λ j → j ⊕ (sl + sr) ≡ sl₁ + sr₂)
      → (∃ λ i → i ⊕ suc (sl + sr + sr₁) ≡ sl₁ + suc (sr₂ + sr₁))
    ans {sl} {sr} {sl₁} {sr₁} {sr₂} (0# , prf)
      rewrite c+sb≡sc+b sl₁ (sr₂ + sr₁) rewrite abc≡abc sl₁ sr₂ sr₁
      = 0# , n≡n⇒sn≡sn (m≡n⇒m+c≡n+c (sl + sr) (sl₁ + sr₂) sr₁ prf)
    ans {sl} {sr} {sl₁} {sr₁} {sr₂} (1# , prf)
      rewrite c+sb≡sc+b sl₁ (sr₂ + sr₁) rewrite abc≡abc sl₁ sr₂ sr₁
      = 1# , n≡n⇒sn≡sn (m≡n⇒m+c≡n+c (suc (sl + sr)) (sl₁ + sr₂) sr₁ prf)

splitAt {s} {l} {u} v t@(node w lt rt) | tri≈ ¬a refl ¬c
  = split (just w) lt rt (0# , refl)
splitAt {s} {l} {u} v {{_}} {{p2}} t@(node {sl} w lt leaf) | tri> ¬a ¬b c
  = ans
  where
    ans : Split v t
    ans = split nothing (join w lt (leaf {{c}})) (leaf {{p2}})
                (1# , n≡n⇒sn≡sn (sym (n+0 (sl + 0))))

splitAt {s} {l} {u} v {{_}} {{p2}} t@(node w lt rt@(node {sl} {sr} _ _ _))
 | tri> ¬a ¬b c with splitAt v {{c}} {{p2}} rt
... | split value ll rr prf
  = split value (join w lt ll) rr (ans {sl} {sr} prf)
  where
    ans : ∀ {sl sr sl₁ sr₁ sl₂}
      → (∃ λ j → j ⊕ (sl + sr) ≡ sl₂ + sr₁)
      → (∃ λ i → i ⊕ (sl₁ + suc (sl + sr)) ≡ suc (sl₁ + sl₂ + sr₁))
    ans {sl} {sr} {sl₁} {sr₁} {sl₂} (0# , prf)
      rewrite c+sb≡sc+b sl₁ (sl + sr)
      with n≡n⇒sn≡sn (m≡n⇒c+m≡c+n (sl + sr) (sl₂ + sr₁) sl₁ prf)
    ... | xx rewrite abc≡abc sl₁ sl₂ sr₁ = 0# , xx
    ans {sl} {sr} {sl₁} {sr₁} {sl₂} (1# , prf)
      rewrite prf rewrite abc≡abc sl₁ sl₂ sr₁
      = 1# , refl

sss≤ssss : ∀ {sL sR sl sr sl₁ sr₁ sl₂ sr₂}
  → (∃ λ i → i ⊕ (sl₁ + sr₁) ≡ sl + sr)
  → sL ≤ sl + sl₂
  → sR ≤ sr + sr₂
  → sL + sR ≤ sl₁ + sr₁ + suc (sl₂ + sr₂)
  -- we can either take from i or arbitrarily increase
sss≤ssss {sL} {sR} {sl} {sr} {sl₁} {sr₁} {sl₂} {sr₂} (0# , p1) p2 p3
  with a≤b+c≤d⇒a+c≤b+d sL (sl + sl₂) sR (sr + sr₂) p2 p3
... | xx
  -- beautiful
  rewrite c+sb≡sc+b (sl₁ + sr₁) (sl₂ + sr₂)
  rewrite abcd≡acbd sl sl₂ sr sr₂
  rewrite p1
  rewrite abc≡abc (sl + sr) sl₂ sr₂ = m≤n⇒m≤1+n xx
sss≤ssss {sL} {sR} {sl} {sr} {sl₁} {sr₁} {sl₂} {sr₂} (1# , p1) p2 p3
  with a≤b+c≤d⇒a+c≤b+d sL (sl + sl₂) sR (sr + sr₂) p2 p3
... | xx
  -- beautiful
  rewrite c+sb≡sc+b (sl₁ + sr₁) (sl₂ + sr₂)
  rewrite abcd≡acbd sl sl₂ sr sr₂
  rewrite abc≡abc (sl₁ + sr₁) sl₂ sr₂
  rewrite sym p1 = xx

ss⊔ss≤sss : ∀ {sL sR sl sr sl₁ sr₁ sl₂ sr₂}
  → (∃ λ i → i ⊕ (sl₁ + sr₁) ≡ sl + sr)
  → sl ⊔ sl₂ ≤ sL
  → sr ⊔ sr₂ ≤ sR
  → (sl₁ + sr₁) ⊔ (sl₂ + sr₂) ≤ (sL + sR)
ss⊔ss≤sss {sL} {sR} {sl} {sr} {sl₁} {sr₁} {sl₂} {sr₂} (i , s=p) slsl srsr
  with a⊔b≤c⇒a≤c∧b≤c {sl} {sl₂} {sL} slsl
... | (slsl1 , slsl2) with a⊔b≤c⇒a≤c∧b≤c {sr} {sr₂} {sR} srsr
... | (srsr1 , srsr2) with i
... | 0# rewrite s=p =
  ⊔-lub (a≤b+c≤d⇒a+c≤b+d sl sL sr sR slsl1 srsr1)
        (a≤b+c≤d⇒a+c≤b+d sl₂ sL sr₂ sR slsl2 srsr2)
... | 1# =
  ⊔-lub fst
        (a≤b+c≤d⇒a+c≤b+d sl₂ sL sr₂ sR slsl2 srsr2)
  where
    fst : sl₁ + sr₁ ≤ sL + sR
    fst with a≤b+c≤d⇒a+c≤b+d sl sL sr sR slsl1 srsr1
    ... | xx rewrite sym s=p = s≤s⁻¹ (m≤n⇒m≤1+n xx)

n⊔n : ∀ n → n ⊔ n ≡ n
n⊔n zero = refl
n⊔n (suc n) rewrite n⊔n n = refl

n⊓n : ∀ n → n ⊓ n ≡ n
n⊓n zero = refl
n⊓n (suc n) rewrite n⊓n n = refl

n≤n : ∀ n → n ≤ n
n≤n zero = z≤n
n≤n (suc n) = s≤s (n≤n n)

n⊔0 : ∀ n → n ⊔ 0 ≡ n
n⊔0 zero = refl
n⊔0 (suc n) = refl

unionᵒᵏ : ∀ {s₁ s₂ l u}
  → ATree l u s₁
  → ATree l u s₂
  → ∃ λ (s : ℕ)
    → ATree l u s × s ≤ (s₁ + s₂) × (s₁ ⊔ s₂) ≤ s
unionᵒᵏ {_} {s} leaf t = _ , t , n≤n s , n≤n s
unionᵒᵏ {s} t leaf rewrite n+0 s rewrite n⊔0 s = _ , t , n≤n s , n≤n s
unionᵒᵏ {s₁} {s₂} t₁@(node {sl₁} {sr₁} v₁ l₁ r₁) t₂@(node v₂ l₂ r₂)
  with splitAt v₂ {{mklim l₂}} {{mklim r₂}} t₁
... | split {sl} {sr} w lv rv hp with unionᵒᵏ lv l₂
... | sL , tL , p+L , p⊔L with unionᵒᵏ rv r₂
... | sR , tR , p+R , p⊔R
  = suc (sL + sR)
  , join v₂ tL tR
  , s≤s (sss≤ssss {sL} {sR} {sl} {sr} {sl₁} {sr₁} hp p+L p+R)
  , s≤s (ss⊔ss≤sss {sL} {sR} {sl} {sr} {sl₁} {sr₁} hp p⊔L p⊔R)

union : ∀ {s₁ s₂ l u}
  → ATree l u s₁
  → ATree l u s₂
  → ∃ λ (s : ℕ) → ATree l u s
union t leaf = _ , leaf
union leaf t = _ , leaf
union {suc s₁} {suc s₂} t₁ t₂ with unionᵒᵏ t₁ t₂
... | s , t , _ , _ = s , t
