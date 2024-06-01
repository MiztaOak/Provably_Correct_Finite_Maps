module Map.UnionLemmas where

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

n⊔n≡n : ∀ n → n ⊔ n ≡ n
n⊔n≡n zero = refl
n⊔n≡n (suc n) rewrite n⊔n≡n n = refl

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
    h rewrite a+sb≡b+sa a (suc b)
      rewrite a+sb≡b+sa b (suc a)
      = cong suc h1

a⊔b≤c⇒a≤c∧b≤c : ∀ {a b c} → a ⊔ b ≤ c → a ≤ c × b ≤ c
a⊔b≤c⇒a≤c∧b≤c {zero} {zero} p = p , p
a⊔b≤c⇒a≤c∧b≤c {zero} {suc b} {suc c} p = z≤n , p
a⊔b≤c⇒a≤c∧b≤c {suc a} {zero} {suc c} p = p , z≤n
a⊔b≤c⇒a≤c∧b≤c {suc a} {suc b} {suc c} p
  with a⊔b≤c⇒a≤c∧b≤c {a} {b} {c} (s≤s⁻¹ p)
... | pa , pb = s≤s pa , s≤s pb

a≤b+c≤d⇒a+c≤b+d : ∀ a b c d → a ≤ b → c ≤ d → a + c ≤ b + d
a≤b+c≤d⇒a+c≤b+d zero zero c d p1 p2 = p2
a≤b+c≤d⇒a+c≤b+d zero b c d p1 p2 = a≤b+c c d b p2
a≤b+c≤d⇒a+c≤b+d (suc a) (suc b) c d p1 p2
  = s≤s $ a≤b+c≤d⇒a+c≤b+d a b c d (s≤s⁻¹ p1) p2

n≡n⇒sn≡sn : ∀ {n m} → n ≡ m → suc n ≡ suc m
n≡n⇒sn≡sn {n} refl = refl

sn≡sn⇒n≡n : ∀ {n m} → suc n ≡ suc m → n ≡ m
sn≡sn⇒n≡n {n} refl = refl

m≡n⇒m+c≡n+c : ∀ m n c → m ≡ n → m + c ≡ n + c
m≡n⇒m+c≡n+c zero zero c p = refl
m≡n⇒m+c≡n+c (suc m) (suc n) c p rewrite m≡n⇒m+c≡n+c m n c (sn≡sn⇒n≡n p) = refl

n+c≡c+n : ∀ n c → n + c ≡ c + n
n+c≡c+n zero c rewrite n+0 c = refl
n+c≡c+n (suc n) c rewrite c+sb≡sc+b c n rewrite n+c≡c+n n c = refl

m≡n⇒c+m≡c+n : ∀ m n c → m ≡ n → c + m ≡ c + n
m≡n⇒c+m≡c+n zero zero c p = refl
m≡n⇒c+m≡c+n (suc m) (suc n) c p rewrite c+sb≡sc+b c m rewrite c+sb≡sc+b c n
  = n≡n⇒sn≡sn (m≡n⇒c+m≡c+n m n c (sn≡sn⇒n≡n p))

abc≡abc : ∀ a b c → a + (b + c) ≡ a + b + c
abc≡abc zero zero zero = refl
abc≡abc zero zero (suc c) = refl
abc≡abc zero (suc b) zero = refl
abc≡abc zero (suc b) (suc c) = refl
abc≡abc (suc a) zero zero rewrite n+0 a rewrite n+0 a = refl
abc≡abc (suc a) zero (suc c) rewrite n+0 a = refl
abc≡abc (suc a) (suc b) zero rewrite n+0 b rewrite n+0 (a + suc b) = refl
abc≡abc (suc a) (suc b) (suc c) rewrite abc≡abc a (suc b) (suc c) = refl

abcd≡acbd : ∀ a b c d → a + b + (c + d) ≡ a + c + b + d
abcd≡acbd a b c d
  -- very funny
  rewrite abc≡abc (a + b) c d
  rewrite +-comm (a + b) c
  rewrite abc≡abc c a b
  rewrite +-comm c a
  = refl

-- rename
testo : ∀ a b c d → (a ⊔ c) ⊔ (b ⊔ d) ≡ (a ⊔ b) ⊔ (c ⊔ d)
testo a b c d
  rewrite sym (⊔-assoc (a ⊔ c) b d)
  rewrite ⊔-assoc a c b
  rewrite ⊔-comm c b
  rewrite sym (⊔-assoc a b c)
  = ⊔-assoc (a ⊔ b) c d

-- rename
testo2 : ∀ a b c d → a ≤ b → c ≤ d → a ⊔ c ≤ b ⊔ d
testo2 zero b zero d p1 p2 = z≤n
testo2 zero b (suc c) d p1 p2 = m≤n⇒m≤o⊔n b p2
testo2 (suc a) b zero d p1 p2 = m≤n⇒m≤n⊔o d p1
testo2 (suc a) (suc b) (suc c) (suc d) p1 p2 = s≤s (testo2 a b c d (s≤s⁻¹ p1) (s≤s⁻¹ p2))

n⊔0 : ∀ n → n ⊔ 0 ≡ n
n⊔0 zero = refl
n⊔0 (suc n) = refl

n⊔sn≡sn : ∀ n → n ⊔ (suc n) ≡ suc n
n⊔sn≡sn zero = refl
n⊔sn≡sn (suc n) rewrite n⊔sn≡sn n = refl

a≤b⇒a+c≤b+c : ∀ {a b} → a ≤ b → (c : ℕ) → a + c ≤ b + c
a≤b⇒a+c≤b+c {a} {b} p zero rewrite n+0 a rewrite n+0 b = p
a≤b⇒a+c≤b+c {a} {b} p (suc c)
  rewrite c+sb≡sc+b a c rewrite c+sb≡sc+b b c
  = s≤s (a≤b⇒a+c≤b+c p c)
