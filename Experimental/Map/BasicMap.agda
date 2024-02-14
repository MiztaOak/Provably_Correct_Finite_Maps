module Map.BasicMap where

open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Prelude renaming (⊥ to bot; ⊤ to top)
open import Relation.Binary.PropositionalEquality
open import Data.Sum

private
  variable
    ℓ ℓ' : Level

module _ {K : Set ℓ} {V : Set ℓ'} where

  record BMap : Set (lsuc (ℓ ⊔ ℓ')) where
    constructor mkMap
    field
      Map    : Set (ℓ ⊔ ℓ')
      ∅      : Map                 -- Empty
      _∈_   : K → Map → Set (ℓ ⊔ ℓ')
      _↦_∈_ : K → V → Map → Set (ℓ ⊔ ℓ') -- Domain
      unionWith : (V → Maybe V → V) → Map → Map → Map
      lookup : Map → K → Maybe V   -- Apply
      insertWith : K → (Maybe V → V) → Map → Map

    syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

    infix  7 lookup
    infix  5 _↦_∈_
    infix  5 _∈_

    [_↦_]_ : K → V → Map → Set ℓ'
    [ k ↦ v ] m = lookup m k ≡ just v

    _↦_∉_ : K → V → Map → Set (ℓ ⊔ ℓ')
    k ↦ v ∉ m = ¬ (k ↦ v ∈ m)

    _∉_ : K → Map → Set (ℓ ⊔ ℓ')
    k ∉ m = ¬ (k ∈ m)

    _⊆_ : Map → Map → Set (ℓ ⊔ ℓ')
    n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

    _≐_ : Map → Map → Set (ℓ ⊔ ℓ')
    n ≐ m = (n ⊆ m) × (m ⊆ n)

    field
      -- induction principle (weak)
      {-
      ⊢ ∀ P . P ∅ ∧ (∀ f . P f ⊃ (∀ x y . P (insert f (x , y))))
          ⊃
        ∀ f . P f
      -}
      ip : (P : Map → Set)
           → P ∅ × (∀ m → P m → ∀ k v → P (insertWith k (λ _ → v) m))
           → (∀ m → P m)

      -- induction principle (stronger)
      {-
      ⊢ ∀ P .
          P ∅ ∧
          (∀ f . P f ⊃ (∀ x . ¬(x ∈ f) ⊃ ∀ y . P (insert f (x , y))))
            ⊃
          ∀ f . P f
      -}
      ips : (P : Map → Set (ℓ ⊔ ℓ'))
            → P ∅ × (∀ m → P m → ∀ k v → k ↦ v ∉ m → ∀ v
              → P (insertWith k (λ _ → v) m))
            → (∀ m → P m)

      lookup-∅ : ∀ k → lookup ∅ k ≡ nothing
      ∈↦-∅ : ∀ k v → ¬ (k ↦ v ∈ ∅)
      ∈-∅ : ∀ k → k ∉ ∅

      ∈⇒lookup : ∀ m k v → [ k ↦ v ] m → k ↦ v ∈ m
      lookup⇒∈ : ∀ m k v → k ↦ v ∈ m → [ k ↦ v ] m

      {-
      ⊢ ∀ f a b . lookup (insert f (a , b)) a = b
      -}
      lookup-insert∈ : ∀ k m f
                       → k ∈ m
                       → [ k ↦ f (lookup m k) ] (insertWith k f m)

      lookup-insert∉ : ∀ k m f
                       → k ∉ m
                       → [ k ↦ f nothing ] (insertWith k f m)

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

      {- TODO: Irrelevant given insertWith?
      ⊢ ∀ f a b c . insert (insert f (a , b)) (a , c) = insert f (a , c)
      ins-same : ∀ m k v w f
                 → insertWith k (λ _ → v) (insertWith k (λ _ → v') m)
                   ≐ insertWith k (λ _ → v) m
      -}

      {-
      ⊢ ∀ f a b x . x ∈ (insert f (a , b)) → (x = a) ∨ x ∈ f
      -}
      ∈-ins : ∀ m k x f
              → x ∈ (insertWith k f m)
              → (x ≡ k) ⊎ x ∈ m

      -- is this actually the case?
      ∪-assoc : ∀ m1 m2 m3 f
                → unionWith f m1 (unionWith f m2 m3)
                  ≐ unionWith f (unionWith f m1 m2) m3

      ∪-∅ : ∀ m f → unionWith f m ∅ ≐ unionWith f ∅ m

      ∪-∈ : ∀ m1 m2 f k
            → k ∈ unionWith f m1 m2
            → k ∈ m1 ⊎ k ∈ m2

      -- eq
      {-
      ⊢ ∀ f g x . (x ∈ f ∧ x ∈ g) ∧ (lookup x f ≡ lookup x g) → f ≡ g
      -}
      -- consider whether these are equivalent
      eq? : (f g : Map) → ∀ k v → k ↦ v ∈ f × k ↦ v ∈ g → f ≐ g

      {-
      ⊢ ∀ f g x . (x ∈ f ∧ x ∈ g) ∧ (x ∈ f → lookup x f ≡ lookup x g) → f ≡ g
      -}
      eq∈ : ∀ f g x → (x ∈ f × x ∈ g) × (x ∈ f → lookup f x ≡ lookup g x) → f ≐ g

    ip' : (P : Map → Set (ℓ ⊔ ℓ'))
          → P ∅ × (∀ m → P m → ∀ k v → P (insertWith k (λ _ → v) m))
          → (∀ m → P m)
    ip' P (b , s) mp = ips P (b , λ m x k _ _ v → s m x k v ) mp
