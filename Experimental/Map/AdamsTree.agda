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

variable
  ω : ℕ

data Value : Set where

postulate
  [_] : ℕ → ℕ

data balance (a b c : ℕ) : Set where
  balanced : ∣ a - b ∣ ≤ c → balance a b c

data ATree (l u : ℕ) : ℕ → Set where
  leaf : {{l < u}} → ATree l u 0
  node : {sl sr : ℕ}
    → (v : ℕ)
    → (lt : ATree l v sl)
    → (rt : ATree v u sr)
    -- this causes issues with matching on sl and sr for some reason
--    → {{ balance sl sr ω }}
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

n+0 : ∀ n → n + 0 ≡ n
n+0 zero = refl
n+0 (suc n) rewrite n+0 n = refl

c+1 : ∀ c → c + 1 ≡ suc c
c+1 zero = refl
c+1 (suc c) rewrite c+1 c = refl

c+sb≡sc+b : ∀ c b → c + suc b ≡ suc (c + b)
c+sb≡sc+b zero zero = refl
c+sb≡sc+b zero (suc b) = refl
c+sb≡sc+b (suc c) zero rewrite c+1 c rewrite n+0 c = refl
c+sb≡sc+b (suc c) (suc b) rewrite c+sb≡sc+b c b = cong suc h
  where
    h2 : c + suc b ≡ suc (c + b)
    h2 = c+sb≡sc+b c b

    h : c + 2+ b ≡ suc (suc (c + b))
    h rewrite c+sb≡sc+b c (suc b) = cong suc h2

s+a≤b+c : ∀ a b c → a ≤ c + b → suc a ≤ c + suc b
s+a≤b+c _ _ zero p = s≤s p
s+a≤b+c zero _ (suc c) p = s≤s z≤n
s+a≤b+c (suc a) zero (suc c) p rewrite c+1 c rewrite n+0 c = s≤s p
s+a≤b+c (suc a) (suc b) (suc c) p = s≤s (s+a≤b+c a (suc b) c (s≤s⁻¹ p))

s-a≤b+c : ∀ a b c → suc a ≤ c + suc b → a ≤ c + b
s-a≤b+c a b zero p = s≤s⁻¹ p
s-a≤b+c a b (suc c) p rewrite c+sb≡sc+b c b = s≤s⁻¹ p

a≤b+c : ∀ a b c → a ≤ b → a ≤ c + b
a≤b+c zero zero c p = z≤n
a≤b+c zero (suc b) c p = z≤n
a≤b+c (suc a) (suc b) c p = s+a≤b+c a b c (a≤b+c a b c (s≤s⁻¹ p))

⊔-sym : ∀ a b → a ⊔ b ≡ b ⊔ a
⊔-sym zero zero = refl
⊔-sym zero (suc b) = refl
⊔-sym (suc a) zero = refl
⊔-sym (suc a) (suc b) rewrite ⊔-sym a b = refl

a+sb≡b+sa : ∀ a b → a + suc b ≡ b + suc a
a+sb≡b+sa zero zero = refl
a+sb≡b+sa zero (suc b) rewrite c+1 b = refl
a+sb≡b+sa (suc a) zero rewrite c+1 a = refl
a+sb≡b+sa (suc a) (suc b) rewrite a+sb≡b+sa a b = cong suc h
  where
    h1 : b + suc a ≡ a + suc b
    h1 = a+sb≡b+sa b a -- how is this ok

    h : a + 2+ b ≡ b + 2+ a
    h rewrite a+sb≡b+sa a (suc b) rewrite a+sb≡b+sa b (suc a) = cong suc h1

a⊔b≤c⇒a≤c∧b≤c : ∀ {a b c} → a ⊔ b ≤ c → a ≤ c × b ≤ c
a⊔b≤c⇒a≤c∧b≤c {zero} {zero} p = p , p
a⊔b≤c⇒a≤c∧b≤c {zero} {suc b} {suc c} p = z≤n , p
a⊔b≤c⇒a≤c∧b≤c {suc a} {zero} {suc c} p = p , z≤n
a⊔b≤c⇒a≤c∧b≤c {suc a} {suc b} {suc c} p with a⊔b≤c⇒a≤c∧b≤c {a} {b} {c} (s≤s⁻¹ p)
... | pa , pb = s≤s pa , s≤s pb

a≤b+c≤d⇒a+c≤b+d : ∀ a b c d → a ≤ b → c ≤ d → a + c ≤ b + d
a≤b+c≤d⇒a+c≤b+d zero zero c d p1 p2 = p2
a≤b+c≤d⇒a+c≤b+d zero b c d p1 p2 = a≤b+c c d b p2
a≤b+c≤d⇒a+c≤b+d (suc a) (suc b) c d p1 p2 = s≤s $ a≤b+c≤d⇒a+c≤b+d a b c d (s≤s⁻¹ p1) p2

data Split {l u s : ℕ} (v : ℕ) (m : ATree l u (suc s)) : Set where
  split : ∀ {sl sr}
    → Maybe ℕ
    → ATree l v sl
    → ATree v u sr
    → (∃ λ i → i ⊕ s ≡ sl + sr)
    → Split v m

n≡n⇒sn≡sn : ∀ {n m} → n ≡ m → suc n ≡ suc m
n≡n⇒sn≡sn {n} refl = refl

sn≡sn⇒n≡n : ∀ {n m} → suc n ≡ suc m → n ≡ m
sn≡sn⇒n≡n {n} refl = refl

m≡n⇒m+c≡n+c : ∀ m n c → m ≡ n → m + c ≡ n + c
m≡n⇒m+c≡n+c zero zero c p = refl
m≡n⇒m+c≡n+c (suc m) (suc n) c p rewrite m≡n⇒m+c≡n+c m n c (sn≡sn⇒n≡n p) = refl

abc≡abc : ∀ a b c → a + (b + c) ≡ a + b + c
abc≡abc zero zero zero = refl
abc≡abc zero zero (suc c) = refl
abc≡abc zero (suc b) zero = refl
abc≡abc zero (suc b) (suc c) = refl
abc≡abc (suc a) zero zero rewrite n+0 a rewrite n+0 a = refl
abc≡abc (suc a) zero (suc c) rewrite n+0 a = refl
abc≡abc (suc a) (suc b) zero rewrite n+0 b rewrite n+0 (a + suc b) = refl
abc≡abc (suc a) (suc b) (suc c) rewrite abc≡abc a (suc b) (suc c) = refl

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
splitAt {s} {l} {u} v t@(node w lt rt) | tri> ¬a ¬b c = {!!}

abcd≡acbd : ∀ a b c d → a + b + (c + d) ≡ a + c + b + d
abcd≡acbd a b c d
  -- very funny
  rewrite abc≡abc (a + b) c d
  rewrite +-comm (a + b) c
  rewrite abc≡abc c a b
  rewrite +-comm c a
  = refl

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
