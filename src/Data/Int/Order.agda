{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Order where

open import Data.Int.Definition

open import PropUniverses
open import Data.Nat as ℕ using (m; n)

infix 35 _<_ _>_
data _<_ : (x y : ℤ) → 𝒰₀ ᵖ where
  neg<nneg : -[ n +1] < nneg m
  nneg<nneg : (p : n ℕ.< m) → nneg n < nneg m
  neg<neg : (p : m ℕ.< n) → -[ n +1] < -[ m +1]

_>_ : (x y : ℤ) → 𝒰₀ ᵖ
x > y = y < x

open import Proposition.Decidable

instance
  Decidable< : Decidable (x < y)

open import Relation.Binary

Decidable< {nneg n} {nneg n₁} with decide (n ℕ.< n₁)
Decidable< {nneg n} {nneg n₁} | true p =
  true (nneg<nneg p)
Decidable< {nneg n} {nneg n₁} | false ¬p =
  false λ { (nneg<nneg p) → ¬p p}
Decidable< {nneg n} { -[ n₁ +1]} = false λ ()
Decidable< { -[ n +1]} {nneg n₁} = true neg<nneg
Decidable< { -[ n +1]} { -[ n₁ +1]} with decide (n₁ ℕ.< n)
Decidable< { -[ n +1]} { -[ n₁ +1]} | true p =
  true (neg<neg p)
Decidable< { -[ n +1]} { -[ n₁ +1]} | false ¬p =
  false λ { (neg<neg p) → ¬p p}
