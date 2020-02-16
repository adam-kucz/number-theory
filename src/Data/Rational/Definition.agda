{-# OPTIONS --exact-split --prop #-}
module Data.Rational.Definition where

open import PropUniverses
open import Type.Sum hiding (_,_)
open import Type.Quotient
open import Proposition.Sum
open import Proposition.Identity hiding (refl)
open import Data.Int

Pair : 𝒰₀ ˙
Pair = ℤ × (Σₚ λ (z : ℤ) → z ≠ 0)

open import Relation.Binary

_≡_ : Rel 𝒰₀ Pair Pair
(nx Σ., (dx , _)) ≡ (ny Σ., (dy , _)) = nx * dy == ny * dx

instance
  Reflexive≡ : Reflexive _≡_
  Transitive≡ : Transitive _≡_
  Symmetric≡ : Symmetric _≡_

open import Proof

refl ⦃ Reflexive≡ ⦄ _ = refl ⦃ Reflexive== ⦄ _
sym ⦃ Symmetric≡ ⦄ = sym ⦃ Symmetric== ⦄
trans ⦃ Transitive≡ ⦄
  {nx Σ., (dx , _)}{ny Σ., (dy , _)}{nz Σ., (dz , _)} p q =
  proof nx * dz
    === nz * dx :by: {!!}
  qed


Rational : 𝒰₁ ˙
Rational = {!Quotient.Type (ℤ × (Σₚ λ (z : ℤ) → z ≠ 0))!}
