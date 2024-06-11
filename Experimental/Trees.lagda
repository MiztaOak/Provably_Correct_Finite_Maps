\newcommand{\DataF}{
\begin{code}
{-# OPTIONS --erasure #-}
\end{code}
}

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

\newcommand{\TreeA}{
\begin{code}[hide]
module one where
\end{code}
\begin{code}
  data Tree : Set where
    leaf : Tree
\end{code}
}

\begin{code}[hide]
postulate
  v : Level
  Key⁺ : Set
  _<⁺_ : Set → Set → Set
  Key : Set
\end{code}

\newcommand{\TreeB}{
\begin{code}[hide]
module two (V : Set) where
\end{code}
\begin{code}
  data Tree (V : Set) : Set where
    leaf : Tree V
    node : (Key × V)
      → (l : Tree V)
      → (r : Tree V)
      → Tree V
\end{code}
}

\newcommand{\TreeC}{
\begin{code}[hide]
module three (V : Set) where
\end{code}
\begin{code}
  data Tree (V : Set) : ℕ → Set where
    leaf : Tree V 0
    node : ∀ {hl hr}
      → (Key × V)
      → (l : Tree V hl)
      → (r : Tree V hr)
      → Tree V (1 + hl ⊔ hr)
\end{code}
}

\newcommand{\McBrideOrdering}{
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
\end{code}
}

\newcommand{\TreeD}{
\begin{code}[hide]
module four {ℓ : Level} (KV : Set)
  (R : Rel KV) where
\end{code}
\begin{code}
  data Tree (V : Set) (l u : Order KV)
    : ℕ → Set where
    leaf : {{l<u : l <⁺ u}}
      → Tree V l u 0
    node : ∀ {hl hr} → (kv : KV)
      → (l : Tree V l [ kv ] hl)
      → (r : Tree V [ kv ] u hr)
      → Tree V l u (1 + hl ⊔ hr)
\end{code}
}

\newcommand{\DataE}{
\begin{code}
data _~_⊔_ : ℕ → ℕ → ℕ → Set where
  ~- : ∀ {n} → suc n ~ n ⊔ suc n
  ~0 : ∀ {n} → n ~ n ⊔ n
  ~+ : ∀ {n} → n ~ suc n ⊔ suc n
\end{code}
}

\newcommand{\TreeE}{
\begin{code}[hide]
module five {ℓ : Level} (KV : Set)
  (R : Rel KV) where
\end{code}
\begin{code}
  data Tree (V : Set) (l u : Order KV)
    : ℕ → Set where
    leaf : {{l<u : l <⁺ u}}
      → Tree V l u 0
    node : ∀ {hl hr h} → (kv : KV)
      → (l : Tree V l [ kv ] hl)
      → (r : Tree V [ kv ] u hr)
      → {{bal : hl ~ hr ⊔ h}}
      → Tree V l u (1 + h)
\end{code}
}
