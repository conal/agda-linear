{-# OPTIONS --rewriting #-}
{-# OPTIONS --irrelevant-projections #-}

-- Functions as a category

module Fun where

open import Level

open import Category (suc 0ℓ)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning

open import Data.Product renaming
      (swap to swap×; _×_ to _×→_; curry to curry→; uncurry to uncurry→)
open import Data.Sum renaming (swap to swap⊎; _⊎_ to _⊎→_)
open import Data.Sum.Properties using (swap-involutive)
open import Function renaming (_∘_ to _∘→_; id to id→)

private
  variable
    A B : Set

-- Agda doesn't like "_→_".
_↦_ : Set → Set → Set
A ↦ B = A → B

-- Extensional equality for use in Category _↦_.
-- Used by swap⊎-involutive.
infix 4 _≡→_
_≡→_ : (A → B) → (A → B) → Set
f ≡→ g = ∀ x → f x ≡ g x

refl→ : {f : A → B} → f ≡→ f
refl→ _ = refl

-- TODO: use _≗_ from Relation.Binary.PropositionalEquality?

instance
  →-Category : Category _↦_
  →-Category = record
    { _≈_ =  _≡→_
    ; id = id→
    ; _∘_ = _∘′_
    ; idˡ = refl→
    ; idʳ = refl→
    ; assoc = refl→ }

instance
  →-Monoidal× : Monoidal _↦_ (_×→_)
  →-Monoidal× = record {_⊙_ = λ { f g (a , b) → (f a , g b) } }

instance
  →-Monoidal⊎ : Monoidal _↦_ (_⊎→_)
  →-Monoidal⊎ = record {
    _⊙_ = λ { f g → (λ { (inj₁ a) → inj₁ (f a) ; (inj₂ b) → inj₂ (g b) }) }
    }

instance
  →-Cartesian : Cartesian _↦_ _×→_
  →-Cartesian = record
    { exl = proj₁
    ; exr = proj₂
    ; dup = λ a → (a , a)
    }

instance
  →-Cocartesian : Cocartesian _↦_ _⊎→_
  →-Cocartesian = record
    { inl = inj₁
    ; inr = inj₂
    ; jam = λ { (inj₁ a) → a ; (inj₂ a) → a }
    }

instance
  →-Associative× : Associative _↦_ _×→_
  →-Associative× = AssocViaCart

instance
  →-Associative⊎ : Associative _↦_ _⊎→_
  →-Associative⊎ = AssocViaCocart

instance
  →-Braided× : Braided _↦_ _×→_
  -- →-Braided× = BraidedViaCart
  →-Braided× = record { swap = swap× }

instance
  →-Braided⊎ : Braided _↦_ _⊎→_
  -- →-Braided⊎ = BraidedViaCocart
  →-Braided⊎ = record { swap = swap⊎ }

instance
  →-Symmetric× : Symmetric _↦_ _×→_
  →-Symmetric× = record { swap∘swap = refl→ }

swap⊎-involutive : swap⊎ ∘ swap⊎ {A = A} {B = B} ≡→ id
swap⊎-involutive (inj₁ _) = refl
swap⊎-involutive (inj₂ _) = refl

instance
  →-Symmetric⊎ : Symmetric _↦_ _⊎→_
  →-Symmetric⊎ = record { swap∘swap = swap⊎-involutive }

instance
  →-Closed : Closed _↦_ _↦_
  →-Closed = record { _⇓_ = λ { f h g → h ∘ g ∘ f } }

instance
  →-CartesianClosed : CartesianClosed _↦_ _×→_ _↦_
  →-CartesianClosed = record
      { curry = curry→
      ; uncurry = uncurry→
      ; apply = λ { (f , x) → f x }
      -- ; apply = applyViaUncurry
      }


