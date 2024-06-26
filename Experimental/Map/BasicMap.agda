module Map.BasicMap where

open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Prelude
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

private
  variable
    ℓ ℓ' : Level

module _ {ℓ₁ : Level} {K : Set ℓ} {V : Set ℓ'} where

  record BMap (Map : Set (ℓ ⊔ ℓ' ⊔ ℓ₁)) : Set (lsuc (ℓ ⊔ ℓ' ⊔ ℓ₁)) where
    constructor mkMap
    field
      ∅      : Map                 -- Empty
      singleton : K → V → Map
      _∈_   : K → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
      _↦_∈_ : K → V → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁) -- Domain
      lookup : Map → K → Maybe V   -- Apply should this be removed?
      lookup∈ : ∀ {k m} → k ∈ m → V
      insertWith : K → (Maybe V → V) → Map → Map

    infix  7 lookup
    infix  5 _↦_∈_
    infix  5 _∈_

    insert : K → V → Map → Map
    insert k v m = insertWith k (λ _ → v) m

    _↦_∉_ : K → V → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    k ↦ v ∉ m = ¬ (k ↦ v ∈ m)

    _∉_ : K → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    k ∉ m = ¬ (k ∈ m)

    _⊆_ : Map → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

    _≐_ : Map → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    n ≐ m = (n ⊆ m) × (m ⊆ n)

    field
      refl⊆ : Reflexive _⊆_
      trans⊆ : Transitive _⊆_
      isequivalence : IsEquivalence _≐_

    field
      ↦∈To∈ : ∀ {k v m} → k ↦ v ∈ m → k ∈ m
      ∈To↦∈ : ∀ {k m} → k ∈ m → ∃ (λ v → k ↦ v ∈ m)

      ∈↦-∅ : ∀ k v → k ↦ v ∉ ∅
      ∈-∅ : ∀ k → k ∉ ∅

      ∈-singleton : ∀ k k' v v' → k ↦ v ∈ singleton k' v' → k ≡ k' × v ≡ v'

      -- induction principle (stronger)
      {-
      ⊢ ∀ P .
          P ∅ ∧
          (∀ f . P f ⊃ (∀ x . ¬(x ∈ f) ⊃ ∀ y . P (insert f (x , y))))
            ⊃
          ∀ f . P f
      -}
      ips : (P : Map → Set (ℓ ⊔ ℓ'))
            → P ∅ × (∀ m → P m → ∀ k v → k ∉ m
                       → P (insertWith k (λ _ → v) m))
            → (∀ m → P m)

      ---------------------------------------------------------------------------------
      -- Insertion and lookup properties
      ---------------------------------------------------------------------------------
      lookup-∅ : ∀ k → lookup ∅ k ≡ nothing

      ∈⇒lookup : ∀ m k {v} → lookup m k ≡ just v → k ↦ v ∈ m
      lookup⇒∈ : ∀ m k v → k ↦ v ∈ m → lookup m k ≡ just v

      ∉⇒nothing : ∀ m k → k ∉ m → lookup m k ≡ nothing
      nothing⇒∉ : ∀ m k → lookup m k ≡ nothing → k ∉ m

      lookup≡lookup∈ : ∀ k m → (k∈m : k ∈ m) → just (lookup∈ k∈m) ≡ lookup m k

      -- would this be usefull?
      mapsTo : ∀ {m k} → (k∈m : k ∈ m) → k ↦ lookup∈ k∈m ∈ m

      {-
      ⊢ ∀ f a b . lookup (insert f (a , b)) a = b
      -}
      lookup-insert : ∀ k m f
                       → lookup (insertWith k f m) k ≡ just (f (lookup m k))

      {-
      ⊢ ∀ a c . (a ≠ c) ⊃
          ∀ f b d .
            insert (insert f (a , b)) (c , d)
              = insert (insert f (c , d)) (a , b)
      -}
      ins-comm : ∀ k k' v v' m
                → k ≢ k'
                → insert k v (insert k' v' m)
                  ≐ insert k' v' (insert k v m)

      {-
      ⊢ ∀ f a b x . x ∈ (insert f (a , b)) → (x = a) ∨ x ∈ f
      -}
      ∈-ins : ∀ m k x v f
              → x ↦ v ∈ (insertWith k f m)
              → (x ≡ k) ⊎ x ↦ v ∈ m

      insert∈ : ∀ k v m → k ↦ v ∈ (insert k v m)

      ∈insert : ∀ k {v} {v'} m → k ↦ v ∈ (insert k v' m) → v ≡ v'

      insert-safe : ∀ {k k' v v' m} → k ↦ v ∈ m → k ≢ k' → k ↦ v ∈ (insert k' v' m)

      ---------------------------------------------------------------------------------
      -- Insertion and Deletion properties
      ---------------------------------------------------------------------------------


    ip : (P : Map → Set (ℓ ⊔ ℓ'))
          → P ∅ × (∀ m → P m → ∀ k v → P (insertWith k (λ _ → v) m))
          → (∀ m → P m)
    ip P (b , s) mp = ips P (b , λ m x k v _ → s m x k v ) mp

  open BMap ⦃...⦄ public
