{-# OPTIONS --erasure #-}

open import Prelude
open import Level using (Level) renaming (zero to 0ℓ)
open import Data.Nat.Base using (ℕ; _+_; suc; zero)
open import NatOrder
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality

open import Map.BasicMap using (BMap)
open import Map.CorrectAll using (CorrectAll)

module Lambda where

data Unit : Set where
  unit : Unit

Var : Set
Var = ℕ

data Type : Set where
  nat : Type
  unit : Type
  _=>_ : Type → Type → Type

[[_]] : Type → Set
[[ nat ]] = ℕ
[[ unit ]] = Unit
[[ τ => τ' ]] = [[ τ ]] → [[ τ' ]]

private
 variable
   Ctx : Set

module Interpreter (bMap : BMap {K = ℕ} {Type} Ctx) (cAll : CorrectAll {ℓₐ = 0ℓ} {ℕ} {Type} Ctx bMap) where
  open Map.BasicMap.BMap bMap public
  open Map.CorrectAll.CorrectAll cAll public

  Env : Ctx → Set
  Env c = All (λ (_ , τ) → [[ τ ]]) c

  data _⊢_ : Ctx → Type → Set where
    T-Int  : ∀ {Γ : Ctx}
             → ℕ
           ------------
             → Γ ⊢ nat

    T-Add  : ∀ {Γ : Ctx}
             → Γ ⊢ nat
             → Γ ⊢ nat
           ------------
             → Γ ⊢ nat

    T-Unit : ∀ {Γ : Ctx}
           -------------
             → Γ ⊢ unit

    T-Var  : ∀ {Γ : Ctx} {τ : Type} {x : Var}
             → x ↦ τ ∈ Γ
           --------------------------
             → Γ ⊢ τ

    T-Abs  : ∀ {Γ : Ctx} {x : Var} {τ₁ τ₂ : Type}
             → (insert x τ₁ Γ) ⊢ τ₂
           ------------------------------------
             → Γ ⊢ (τ₁ => τ₂)

    T-App  : ∀ {Γ : Ctx} {τ₁ τ₂ : Type}
             → Γ ⊢ (τ₁ => τ₂)
             → Γ ⊢ τ₁
           --------------------------
             → Γ ⊢ τ₂

  translate : ∀ {Γ : Ctx} {τ : Type} → Env Γ → Γ ⊢ τ → [[ τ ]]
  translate _ (T-Int n) = n
  translate env (T-Add e₁ e₂) = translate env e₁ + translate env e₂
  translate env T-Unit = unit
  translate env (T-Var {x = x'} prf) = allLookup {k = x'} prf env
  translate env (T-Abs {x = x} e) e' = translate (allInsert {k = x} e' env) e
  translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)
{-
--sucL : ℕ → ℕ
--sucL n = translate {[]} []Env (T-App (T-Abs (T-Add (T-Var (insert∈ 0 nat [])) (T-Int 1))) (T-Int n))
-- -}
-- -}
-- -}
-- -}
