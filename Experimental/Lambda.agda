open import Prelude  
open import Level using (Level; Lift; lower)
open import Map.BSTMap
open import OrdSet

module Lambda where

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)

data Unit : Set where
  unit : Unit

Var : Set
Var = Nat 

data Type : Set where
  int : Type
  unit : Type
  _=>_ : Type → Type → Type

[[_]] : Type → Set₁
[[ int ]] = Lift (Level.suc Level.zero) Nat 
[[ unit ]] = Lift (Level.suc Level.zero) Unit
[[ τ => τ' ]] = [[ τ ]] → [[ τ' ]]

--data Env : Set where
--  tst : Env
Ctx : Set
Ctx = BSTMap Type OSetℕ (⊥ , ⊤)

Env : Ctx → Set
Env = {!!}

data _⊢_ : Ctx → Type → Set where
  T-Int  : ∀ {Γ : Ctx}
             → Nat
           ------------
             → Γ ⊢ int
             
  T-Add  : ∀ {Γ : Ctx}
             → Γ ⊢ int
             → Γ ⊢ int
           ------------
             → Γ ⊢ int
             
  T-Unit : ∀ {Γ : Ctx}
           -------------
             → Γ ⊢ unit
             
  T-Var  : ∀ {Γ : Ctx} {τ : Type} {x : Var}
           -- add proof of Γ(x) = τ
             → lookup Type OSetℕ Γ x ≡ just τ 
             -- → Var
           --------------------------
             → Γ ⊢ τ -- fromJust $ lookup Γ x
  
  T-Abs  : ∀ {Γ : Ctx} {x : Var} {τ₁ τ₂ : Type}
             → (insert Type OSetℕ fst (x , τ₁) {{record {}}} {{record {}}} Γ) ⊢ τ₂
           -- needs to add Γ,x:τ₁ to argument
           ------------------------------------
             → Γ ⊢ (τ₁ => τ₂)
  
  T-App  : ∀ {Γ : Ctx} {τ₁ τ₂ : Type}
             → Γ ⊢ (τ₁ => τ₂)
             → Γ ⊢ τ₁
           --------------------------
             → Γ ⊢ τ₂

translate : ∀ {Γ : Ctx} {τ : Type} → Env Γ → Γ ⊢ τ → [[ τ ]]
translate _ (T-Int n) = Level.lift n
translate env (T-Add e₁ e₂) = Level.lift (lower (translate env e₁) + lower (translate env e₂))
translate env T-Unit = Level.lift unit
translate env (T-Var {x = x'} prf) = {!!} 
translate env (T-Abs e) e' = translate {!!} e 
translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)
