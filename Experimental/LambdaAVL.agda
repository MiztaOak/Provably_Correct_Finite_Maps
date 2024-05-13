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
open import Lambda
open import Map.BOBMapImp ℕOrder

module LambdaAVL where

open BMapAVLInstance Type

private
  module LambdaImp = Lambda.Interpreter basicMap correctAll

open LambdaImp public

[]Env : Env ∅
[]Env = all∅ (λ x → [[ proj₂ x ]])

sucL : ℕ → ℕ
sucL n = translate []Env (T-App (T-Abs (T-Add (T-Var (insert∈ 0 nat ∅)) (T-Int 1))) (T-Int n))

open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Criterion.Main

main : IO ⊤
main = defaultMain (bench "translate" (whnf sucL 100) ∷ [])

-- -}
-- -}
-- -}
-- -}
