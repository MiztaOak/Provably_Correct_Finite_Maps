open import Level renaming (suc to s; zero to z)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
module Prelude where

private
  variable
    ℓ l : Level

-- The empty sum is the type with 0 alternatives,
-- which is the empty type.
-- By the Curry-Howard-Isomorphism,
-- which views a proposition as the set/type of its proofs,
-- it is also the absurd proposition.

data False : Set where

-- The record type with no fields has exactly one inhabitant
-- namely the empty tuple record{}
-- By Curry-Howard, it corresponds to Truth, as
-- no evidence is needed to construct this proposition.

record True : Set ℓ where
  instance constructor tt

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

pattern le = inj₁ !
pattern ge = inj₂ (inj₂ !)
pattern eq = inj₂ (inj₁ refl)
