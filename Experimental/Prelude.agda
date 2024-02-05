open import Level renaming (suc to s; zero to z)
module Prelude where

private
  variable
    ℓ l : Level

-- Natural numbers as our first example of
-- an inductive data type.

data Nat : Set where
  zero : Nat 
  suc  : (n : Nat) → Nat 

-- To use decimal notation for numerals, like
-- 2 instead of (suc (suc zero)), connect it
-- to the built-in natural numbers.

{-# BUILTIN NATURAL Nat #-}

-- Lists are a parameterized inductive data type.

data List (A : Set ℓ) : Set ℓ where
  nil  : List A
  cons : (x : A) (xs : List A) → List A

-- Disjoint sum type.

data _⊎_ (S : Set l) (T : Set ℓ) : Set (s (l ⊔ ℓ)) where
  inl : S → S ⊎ T
  inr : T → S ⊎ T
infixr 4 _⊎_

-- The empty sum is the type with 0 alternatives,
-- which is the empty type.
-- By the Curry-Howard-Isomorphism,
-- which views a proposition as the set/type of its proofs,
-- it is also the absurd proposition.

data False : Set where

-- Tuple types

-- The generic record type with two fields
-- where the type of the second depends on the value of the first
-- is called Sigma-type (or dependent sum), in analogy to
--
--   Σ ℕ A =  Σ   A(n) = A(0) + A(1) + ...
--           n ∈ ℕ

record Σ (S : Set l) (T : S → Set ℓ) : Set (l ⊔ ℓ) where
  constructor _,_
  field fst : S
        snd : T fst
open Σ public

infixr 5 _,_

-- The non-dependent version is the ordinary Cartesian product.

_×_ : (S : Set l) (T : Set ℓ) → Set (l ⊔ ℓ)
S × T = Σ S λ _ → T

infixr 5 _×_

-- The record type with no fields has exactly one inhabitant
-- namely the empty tuple record{}
-- By Curry-Howard, it corresponds to Truth, as
-- no evidence is needed to construct this proposition.

record True : Set ℓ where
  constructor tt

-- Relations

-- Type-theoretically, the type of relations 𝓟(A×A) is
--
--   A × A → Prop
--
-- which is
--
--   A × A → Set
--
-- by the Curry-Howard-Isomorphism.

Rel : Set → Set₁
Rel A = A → A → Set

-- Less-or-equal on natural numbers

LEℕ : Rel Nat 
LEℕ zero  y     = True
LEℕ (suc x) zero  = False
LEℕ (suc x) (suc y) = LEℕ x y 

≺ℕ : Rel Nat
≺ℕ zero zero = False
≺ℕ zero (suc y) = True 
≺ℕ (suc x) zero = False
≺ℕ (suc x) (suc y) = ≺ℕ x y

data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

-- C-c C-l load
-- C-c C-c case split
-- C-c C-, show goal and assumptions
-- C-c C-. show goal and assumptions and current term
-- C-c C-SPC give

record ⌜_⌝ (P : Set ℓ) : Set ℓ where
  constructor !
  field {{prf}} : P

-- Extension by a least and a greatest element

data Ext (A : Set ℓ) : Set ℓ where
  ⊤ : Ext A
  # : A → Ext A
  ⊥ : Ext A
