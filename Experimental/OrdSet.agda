module OrdSet where

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.Structures using (IsStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.Core
open import Level
open import Relation.Binary.PropositionalEquality hiding (trans)

record OrdSet c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _<_
  field
    Carrier            : Set c
    _<_                : Rel Carrier ℓ
    isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_

toStrictTotalOrder : {c ℓ : Level} → OrdSet c ℓ → StrictTotalOrder c c ℓ
StrictTotalOrder.Carrier (toStrictTotalOrder ord) = Carrier
  where open OrdSet ord
StrictTotalOrder._≈_ (toStrictTotalOrder ord) = _≡_
StrictTotalOrder._<_ (toStrictTotalOrder ord) = _<_
  where open OrdSet ord
StrictTotalOrder.isStrictTotalOrder (toStrictTotalOrder ord) = isStrictTotalOrder
  where open OrdSet ord
