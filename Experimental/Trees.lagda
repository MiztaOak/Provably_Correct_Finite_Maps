\begin{code}[hide]
module Trees where

open import Level using (Level; _⊔_)
open import Data.Nat hiding (_⊔_)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

record ⊤ : Set where
  instance constructor tt

data ⊥ : Set where

data _⊎_ (S T : Set) : Set where
  inl : S → S ⊎ T
  inr : T → S ⊎ T
infixr 4 _⊎_

record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field fst : S
        snd : T fst

open Σ public
infixr 5 _,_

_×_ : (S T : Set) → Set
S × T = Σ S λ _ → T
infixr 5 _×_
\end{code}

\newcommand{\Tree1}{
\begin{code}
module one (Key : Set) (Val : Set) where

  data Tree : Set where
    leaf : Tree
\end{code}
}

\newcommand{\Tree2}{
\begin{code}
module two (Key : Set) (Val : Set) where

  data Tree : Set where
    leaf : Tree
    node : Key → (l : Tree) → (r : Tree) → Tree
\end{code}
}

\newcommand{\Tree3}{
\begin{code}
module three (Key : Set) (Val : Set) where

  data Tree : ℕ → Set where
    leaf : Tree 0
    node : ∀ {hl hr} → Key
      → (l : Tree hl) → (r : Tree hr)
      → Tree (1 + hl + hr)
\end{code}
}

\newcommand{\Tree4}{
\begin{code}
data _~_⊔_ : ℕ → ℕ → ℕ → Set where
  ~- : ∀ {n} → suc n ~ n ⊔ suc n
  ~0 : ∀ {n} → n ~ n ⊔ n
  ~+ : ∀ {n} → n ~ suc n ⊔ suc n

module four (Key : Set) (Val : Set) where

  data Tree : ℕ → Set where
    leaf : Tree 0
    node : ∀ {hl hr h} → Key
      → (l : Tree hl) → (r : Tree hr)
      → {{bal : hl ~ hr ⊔ h}}
      → Tree (1 + h)
\end{code}
}

\newcommand{\Tree5}{
\begin{code}
Rel : Set → Set₁
Rel A = A × A → Set

data Order (A : Set) : Set where
  top : Order A
  [_] : A → Order A
  bot : Order A

ext : ∀ {A} → Rel A → Rel (Order A)
ext R (_ , top) = ⊤
ext R ([ x ] , [ y ]) = R (x , y)
ext R (bot , _) = ⊤
ext R _         = ⊥

module five {ℓ : Level} (Key : Set)
  (Val : Set) (R : Rel Key) where

  data Tree (l u : Order Key) : ℕ → Set ℓ where
    leaf : {{l<u : ext R (l , u)}} → Tree l u 0
    node : ∀ {hl hr h} → (k : Key)
      → (l : Tree l [ k ] hl) → (r : Tree [ k ] u hr)
      → {{bal : hl ~ hr ⊔ h}}
      → Tree l u (1 + h)
\end{code}
}
