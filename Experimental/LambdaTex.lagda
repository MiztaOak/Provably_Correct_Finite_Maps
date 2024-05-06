\begin{code}[hide]
{-# OPTIONS --erasure #-}

open import Prelude
open import Level using (Level; Lift; lower)
open import Data.Nat.Base using (ℕ; _+_; suc; zero)
open import NatOrder
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Map.BasicMap
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality

open import Map.BOBMapImp ℕOrder

module LambdaTex where

\end{code}

\begin{code}[hide]
data Unit : Set where
  unit : Unit
\end{code}

\newcommand{\VarDef}{
\begin{code}
Var : Set
Var = ℕ
\end{code}
}

\newcommand{\LambdaType}{
\begin{code}
data Type : Set where
  int : Type
  unit : Type
  _=>_ : Type → Type → Type
\end{code}
}

\begin{code}[hide]
open BMapAVLInstance Type
\end{code}

\newcommand{\TypeTrans}{
\begin{code}
[[_]] : Type → Set
[[ int ]] = ℕ
[[ unit ]] = Unit
[[ τ => τ' ]] = [[ τ ]] → [[ τ' ]]
\end{code}
}

\newcommand{\CtxEnvDef}{
\begin{code}
Ctx : Set
Ctx = AVLMap Type

Env : Ctx → Set
Env c = AllM (λ x → [[ proj₂ x ]]) c
\end{code}
}

\newcommand{\LambdaExp}{
\begin{code}
data _⊢_ : Ctx → Type → Set where
  T-Int  : ∀ {Γ : Ctx}
             → ℕ
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
\end{code}
}

\newcommand{\LambdaTrans}{
\begin{code}
translate : ∀ {Γ : Ctx} {τ : Type} → Env Γ → Γ ⊢ τ → [[ τ ]]
translate _ (T-Int n) = n
translate env (T-Add e₁ e₂) = translate env e₁ + translate env e₂
translate env T-Unit = unit
translate env (T-Var {x = x'} prf) = allMLookup prf env
translate env (T-Abs {x = x} e) e' = translate (allMInsert e' env) e
translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)
\end{code}
}
