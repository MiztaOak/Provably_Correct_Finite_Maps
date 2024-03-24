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

private
  variable
    ℓ ℓ' : Level

module _ {ℓ₁ : Level} {K : Set ℓ} {V : Set ℓ'} where

  record BMap : Set (lsuc (ℓ ⊔ ℓ' ⊔ ℓ₁)) where
    constructor mkMap
    field
      Map    : Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
      ∅      : Map                 -- Empty
      _∈_   : K → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
      _↦_∈_ : K → V → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁) -- Domain
      unionWith : (V → Maybe V → V) → Map → Map → Map
      lookup : Map → K → Maybe V   -- Apply
      lookup∈ : ∀ {k m} → k ∈ m → V
      insertWith : K → (Maybe V → V) → Map → Map
      delete : K → Map → Map

    syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

    infix  7 lookup
    infix  5 _↦_∈_
    infix  5 _∈_

    insert : K → V → Map → Map
    insert k v m = insertWith k (λ _ → v) m

    [_↦_]_ : K → V → Map → Set ℓ'
    [ k ↦ v ] m = lookup m k ≡ just v

    _↦_∉_ : K → V → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    k ↦ v ∉ m = ¬ (k ↦ v ∈ m)

    _∉_ : K → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    k ∉ m = ¬ (k ∈ m)

    _⊆_ : Map → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

    _≐_ : Map → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁)
    n ≐ m = (n ⊆ m) × (m ⊆ n)

    field
      refl≐ : Reflexive _≐_
      sym≐  : Symmetric _≐_
      trans≐ : Transitive _≐_

    field
      ↦∈To∈ : ∀ {k v m} → k ↦ v ∈ m → k ∈ m

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
      ∈↦-∅ : ∀ k v → ¬ (k ↦ v ∈ ∅)
      ∈-∅ : ∀ k → k ∉ ∅

      ∈⇒lookup : ∀ m k {v} → [ k ↦ v ] m → k ↦ v ∈ m
      lookup⇒∈ : ∀ m k v → k ↦ v ∈ m → [ k ↦ v ] m

      {-
      ⊢ ∀ f a b . lookup (insert f (a , b)) a = b
      -}
      lookup-insert : ∀ k m f
                       → [ k ↦ f (lookup m k) ] (insertWith k f m)

      {-
      ⊢ ∀ a c . (a ≠ c) ⊃
          ∀ f b d .
            insert (insert f (a , b)) (c , d)
              = insert (insert f (c , d)) (a , b)
      -}
      ins-comm : ∀ k k' f f' m
                → k ≢ k'
                → insertWith k f (insertWith k' f' m)
                  ≐ insertWith k' f' (insertWith k f m)

      {-
      ⊢ ∀ f a b x . x ∈ (insert f (a , b)) → (x = a) ∨ x ∈ f
      -}
      ∈-ins : ∀ m k x f
              → x ∈ (insertWith k f m)
              → (x ≡ k) ⊎ x ∈ m

      insert∈ : ∀ k v m → k ↦ v ∈ (insert k v m)

      insert-safe : ∀ {k k' v v' m} → k ↦ v ∈ m → k ≢ k' → k ↦ v ∈ (insert k' v' m)

      ---------------------------------------------------------------------------------
      -- Union Properties
      ---------------------------------------------------------------------------------
      -- is this possible? Issue with L/R bias in implementation
      ∪-∅ᴸ : ∀ m f → unionWith f m ∅ ≐ m
      ∪-∅ᴿ : ∀ m f → unionWith f ∅ m ≐ m
      ∪-∅ : ∀ m f → unionWith f m ∅ ≐ unionWith f ∅ m

      ∪-∈ : ∀ m1 m2 f k
            → k ∈ unionWith f m1 m2
            → k ∈ m1 ⊎ k ∈ m2

      -- safety prop of above?
      ∪-∈' : ∀ m1 m2 f k
            → k ∈ m1 ⊎ k ∈ m2
            → k ∈ unionWith f m1 m2
      -- eq
      {-
      ⊢ ∀ f g x . (x ∈ f ∧ x ∈ g) ∧ (lookup x f ≡ lookup x g) → f ≡ g
      -}
      -- should be covered by refl, sym and trans?
      --eq? : (f g : Map) → (∀ k v → k ↦ v ∈ f × k ↦ v ∈ g) → f ≐ g


      ---------------------------------------------------------------------------------
      -- Deletion properties
      ---------------------------------------------------------------------------------
      del-∉ : ∀ {k m} → k ∉ m → delete k m ≐ m
      del-∈ : ∀ {k m} → k ∈ m → k ∉ delete k m
      del-safe : ∀ {k k' v m} → k' ↦ v ∈ m → k ≢ k' → k' ↦ v ∈ delete k m

    ip : (P : Map → Set (ℓ ⊔ ℓ'))
          → P ∅ × (∀ m → P m → ∀ k v → P (insertWith k (λ _ → v) m))
          → (∀ m → P m)
    ip P (b , s) mp = ips P (b , λ m x k v _ → s m x k v ) mp
