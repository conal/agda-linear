{-# OPTIONS --type-in-type --rewriting #-}

module Category where

open import Data.Product renaming (swap to pswap)
open import Data.Sum renaming (swap to sswap)
open import Data.Unit
open import Function renaming (_∘_ to _∘→_; id to id→)
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

private
  variable
   u : Set
   A B C D U V Z : u
   _↝_ : u → u → Set

record Category (_↝_ : u → u → Set) : Set where
  infixr 5 _∘_
  field
    id   : A ↝ A
    _∘_  : (B ↝ C) → (A ↝ B) → (A ↝ C)
    .id-l  : ∀ {f : A ↝ B} → id ∘ f ≡ f
    .id-r  : ∀ {f : A ↝ B} → f ∘ id ≡ f
    .assoc : ∀ {h : C ↝ D} {g : B ↝ C} {f : A ↝ B} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
open Category ⦃ … ⦄ public

instance
  →-Category : Category (λ (A B : Set) → A → B)
  →-Category = record {
    id = id→ ;
    _∘_ = _∘′_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

-- record MonoidalP (_↝_ : u → u → Set) : Set where
--   field
--     ⦃ cat ⦄ : Category _↝_
--     _⊗_ : (A ↝ C) → (B ↝ D) → ((A × B) ↝ (C × D))
-- open MonoidalP ⦃ … ⦄ public

-- The _⊗_ type is a no go, because × is on Set.

-- instance
--   →-MonoidalP : MonoidalP (λ (A B : Set) → A → B)
--   →-MonoidalP = record {
--     _⊗_ = λ { f g (a , b) → (f a , g b) } }

-- record Cartesian _↝_ : Set where
--   field
--     ⦃ _↝_MonoidalP ⦄ : MonoidalP _↝_
--     exl : (A × B) ↝ A
--     exr : (A × B) ↝ B
--     dup : A ↝ (A × A)
-- open Cartesian ⦃ … ⦄ public

-- _△_ : ⦃ _ : Cartesian _↝_ ⦄ → (A ↝ C) → (A ↝ D) → (A ↝ (C × D))
-- f △ g = (f ⊗ g) ∘ dup

-- instance
--   →-Cartesian : Cartesian (λ (A B : Set) → A → B)
--   →-Cartesian = record {
--     exl = proj₁ ;
--     exr = proj₂ ;
--     dup = λ a → (a , a) }
