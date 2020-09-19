{-# OPTIONS --type-in-type --rewriting #-}
{-# OPTIONS --irrelevant-projections #-}

-- Functions as a category

module Fun where

open import Level

open import Category

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning

open import Data.Product renaming
      (swap to swap×; _×_ to _×→_; curry to curry→; uncurry to uncurry→)
open import Data.Sum renaming (swap to swap⊎; _⊎_ to _⊎→_)
open import Function renaming (_∘_ to _∘→_; id to id→)

Fun : Set → Set → Set
Fun = λ (A B : Set) → A → B

instance
  →-Category : Category Fun
  →-Category = record {
    _≈_ = _≡_ ;
    id = id→ ;
    _∘_ = _∘′_ ;
    idˡ = refl ;
    idʳ = refl ;
    assoc = refl }

instance
  →-Monoidal× : Monoidal Fun (_×→_)
  →-Monoidal× = record {
    _⊙_ = λ { f g (a , b) → (f a , g b) } }

instance
  →-Monoidal⊎ : Monoidal Fun (_⊎→_)
  →-Monoidal⊎ = record {
    _⊙_ = λ { f g → (λ { (inj₁ a) → inj₁ (f a) ; (inj₂ b) → inj₂ (g b) }) } }

instance
  →-Cartesian : Cartesian Fun _×→_
  →-Cartesian = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }

instance
  →-Cocartesian : Cocartesian Fun _⊎→_
  →-Cocartesian = record {
    inl = inj₁ ;
    inr = inj₂ ;
    jam = λ { (inj₁ a) → a ; (inj₂ a) → a }
   }

instance
  →-Associative× : Associative Fun _×→_
  →-Associative× = AssocViaCart

instance
  →-Associative⊎ : Associative Fun _⊎→_
  →-Associative⊎ = AssocViaCocart

instance
  →-Braided× : Braided Fun _×→_
  →-Braided× = BraidedViaCart

instance
  →-Braided⊎ : Braided Fun _⊎→_
  →-Braided⊎ = BraidedViaCocart

instance
  →-Symmetric× : Symmetric Fun _×→_
  →-Symmetric× = record { swap∘swap = refl }

-- TODO:
-- 
-- instance
--   →-Symmetric⊎ : Symmetric Fun _⊎→_
--   →-Symmetric⊎ = {!!}

-- Use swap-involutive from the standard library from Data.Sum.Properties

instance
  →-Closed : Closed Fun Fun
  →-Closed = record { _⇓_ = λ { f h g → h ∘ g ∘ f } }

instance
  →-CartesianClosed : CartesianClosed Fun _×→_ Fun
  →-CartesianClosed = record {
      curry = curry→ ;
      uncurry = uncurry→ ;
      apply = λ { (f , x) → f x }
      -- apply = applyViaUncurry
      }
