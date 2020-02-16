{-# OPTIONS --exact-split --prop #-}
module Data.Int.Arithmetic.Property where

open import Data.Int.Arithmetic.Definition
open import Data.Int.Definition
open import Data.Int.Syntax
import Data.Nat as N
open N.Pattern hiding (one)
open Pattern

open import Proposition.Identity hiding (refl)
open import Operation.Binary

private
  module Patterns where
    pattern zer = nneg 0
    pattern one = nneg 1
open Patterns

open import Function as Fun
  hiding (RightInverse; LeftInverse; _$_; _⁻¹; left-unit; right-unit)

instance
  suc-pred : Fun.RightInverse suc pred
  pred-suc : Fun.LeftInverse suc pred

open import Proof

right-inv ⦃ suc-pred ⦄ (nneg 0) = refl 0
right-inv ⦃ suc-pred ⦄ (nneg (n +1)) = refl (nneg (n +1))
right-inv ⦃ suc-pred ⦄ -[ n +1] = refl -[ n +1]

left-inv ⦃ pred-suc ⦄ (nneg n) = refl (nneg n)
left-inv ⦃ pred-suc ⦄ -[1] = refl -[1]
left-inv ⦃ pred-suc ⦄ -[ n +2] = refl -[ n +2]

instance
  Associative+ : Associative _+_
  0-+ : zer IsLeftUnitOf _+_
  +-0 : zer IsRightUnitOf _+_
  Commutative+ : Commutative _+_
  +neg : RightInverse neg _+_
  neg+ : LeftInverse neg _+_

suc-+ : ∀ x y → suc x + y == suc (x + y)
suc-+ (nneg n) y = ap suc $ refl (nneg n + y)
suc-+ -[1] y = sym $ right-inv y
suc-+ -[ n +2] y = sym $ right-inv (-[ n +1] + y)

pred-+ : ∀ x y → pred x + y == pred (x + y)
pred-+ (nneg 0) y = refl (pred y)
pred-+ (nneg (n +1)) y = sym $ left-inv (nneg n + y)
pred-+ -[ n +1] y = refl (pred (-[ n +1] + y))

assoc ⦃ Associative+ ⦄ zer y z = refl (y + z)
assoc ⦃ Associative+ ⦄ (nneg (n +1)) y z =
  proof suc (nneg n + (y + z))
    === suc (nneg n + y + z)
      :by: ap suc $ assoc (nneg n) y z
    === suc (nneg n + y) + z
      :by: sym $ suc-+ (nneg n + y) z
  qed
assoc ⦃ Associative+ ⦄ -[1] y z = sym $ pred-+ y z
assoc ⦃ Associative+ ⦄ -[ n +2] y z = 
  proof pred (-[ n +1] + (y + z))
    === pred (-[ n +1] + y + z)
      :by: ap pred $ assoc -[ n +1] y z
    === pred (-[ n +1] + y) + z
      :by: sym $ pred-+ (-[ n +1] + y) z
  qed

left-unit ⦃ 0-+ ⦄ = refl
right-unit ⦃ +-0 ⦄ (nneg 0) = refl 0
right-unit ⦃ +-0 ⦄ (nneg (n +1)) = ap suc $ right-unit (nneg n)
right-unit ⦃ +-0 ⦄ -[1] = refl -[1]
right-unit ⦃ +-0 ⦄ -[ n +2] = ap pred $ right-unit -[ n +1]

+-suc : ∀ x y → x + suc y == suc (x + y)
+-suc (nneg 0) y = refl (suc y)
+-suc (nneg (n +1)) y = ap suc $ +-suc (nneg n) y
+-suc -[1] y = proof pred (suc y)
                 === y            :by: left-inv y
                 === suc (pred y) :by: sym $ right-inv y
               qed
+-suc -[ n +2] y =
  proof pred (-[ n +1] + suc y)
    === pred (suc (-[ n +1] + y))
      :by: ap pred $ +-suc -[ n +1] y
    === -[ n +1] + y
      :by: left-inv (-[ n +1] + y)
    === suc (pred (-[ n +1] + y))
      :by: sym $ right-inv (-[ n +1] + y)
  qed

+-pred : ∀ x y → x + pred y == pred (x + y)
+-pred (nneg 0) y = refl (pred y)
+-pred (nneg (n +1)) y =
  proof suc (nneg n + pred y)
    === suc (pred (nneg n + y)) :by: ap suc $ +-pred (nneg n) y
    === nneg n + y              :by: right-inv (nneg n + y)
    === pred (suc (nneg n + y)) :by: sym $ left-inv (nneg n + y)
  qed
+-pred -[1] y = refl (pred (pred y))
+-pred -[ n +2] y = ap pred $ +-pred -[ n +1] y

comm ⦃ Commutative+ ⦄ (nneg 0) y = sym $ right-unit y
comm ⦃ Commutative+ ⦄ (nneg (n +1)) y =
  proof suc (nneg n + y)
    === suc (y + nneg n) :by: ap suc $ comm (nneg n) y
    === y + nneg (n +1)  :by: sym $ +-suc y (nneg n)
  qed
comm ⦃ Commutative+ ⦄ -[1] y =
  proof pred y
    === pred (y + 0) :by: ap pred $ sym $ right-unit y
    === y + -1       :by: sym $ +-pred y 0
  qed
comm ⦃ Commutative+ ⦄ -[ n +2] y =
  proof pred (-[ n +1] + y)
    === pred (y + -[ n +1]) :by: ap pred $ comm -[ n +1] y
    === y + -[ n +2]        :by: sym $ +-pred y -[ n +1]
  qed

right-inverse ⦃ +neg ⦄ (nneg 0) = refl 0
right-inverse ⦃ +neg ⦄ (nneg 1) = refl 0
right-inverse ⦃ +neg ⦄ (nneg (n +2)) =
  proof suc (suc (nneg n + -[ n +2]))
    === suc (nneg n + -[ n +1])
      :by: ap suc $ sym $ +-suc (nneg n) -[ n +2]
    === nneg (n +1) + -[ n +1]
      :by: suc-+ (nneg n) -[ n +1]
    === 0
      :by: right-inverse (nneg (n +1))
  qed
right-inverse ⦃ +neg ⦄ -[1] = refl 0
right-inverse ⦃ +neg ⦄ -[ n +2] =
  proof pred (-[ n +1] + nneg (n +2))
    === -[ n +1] + nneg (n +1) :by: sym $ +-pred -[ n +1] (nneg (n +2))
    === 0                      :by: right-inverse -[ n +1]
  qed

left-inverse ⦃ neg+ ⦄ x =
  proof neg x + x
    === x + neg x :by: comm (neg x) x
    === 0         :by: right-inverse x
  qed


open import Structure.Monoid
open import Structure.Hemiring hiding (_+_; _*_)

instance
  0-* : zer IsLeftZeroOf _*_
  *-0 : zer IsRightZeroOf _*_
  Commutativeℕ* : Commutative _*_
  Associative* : Associative _*_
  1-* : one IsLeftUnitOf _*_
  *-1 : one IsRightUnitOf _*_
  Hemiringℕ+* : FormHemiring _+_ _*_ zer

left-zero ⦃ 0-* ⦄ (nneg n) = refl 0
left-zero ⦃ 0-* ⦄ -[ n +1] = refl 0
right-zero ⦃ *-0 ⦄ (nneg n) = ap nneg $ right-zero n
right-zero ⦃ *-0 ⦄ -[ n +1] = ap (neg ∘ nneg) $ right-zero n
comm ⦃ Commutativeℕ* ⦄ (nneg n) (nneg n₁) = ap nneg $ comm n n₁
comm ⦃ Commutativeℕ* ⦄ (nneg n) -[ n₁ +1] = ap (neg ∘ nneg) $ comm n (n₁ +1)
comm ⦃ Commutativeℕ* ⦄ -[ n +1] (nneg n₁) = ap (neg ∘ nneg) $ comm (n +1) n₁
comm ⦃ Commutativeℕ* ⦄ -[ n +1] -[ n₁ +1] = ap nneg $ comm (n +1) (n₁ +1)

neg-neg : neg ∘ neg ~ id
neg-neg (nneg 0) = refl 0
neg-neg (nneg (n +1)) = refl (nneg (n +1))
neg-neg -[ n +1] = refl -[ n +1]

open mkInvolutive {f = neg} neg-neg public

*-neg : ∀ x y → x * neg y == neg (x * y)
*-neg (nneg n) (nneg 0) =
  proof nneg (n N.* 0)
    === 0                    :by: ap nneg $ right-zero n
    === neg (nneg (n N.* 0)) :by: ap (neg ∘ nneg) $ sym $ right-zero n
  qed
*-neg (nneg n) (nneg (n₁ +1)) = refl _
*-neg (nneg n) -[ n₁ +1] = sym $ left-inv (nneg (n N.* (n₁ +1)))
*-neg -[ n +1] (nneg 0) = ap neg (
  proof nneg (n N.* 0)
    === 0                    :by: ap nneg $ right-zero n
    === neg (nneg (n N.* 0)) :by: ap (neg ∘ nneg) $ sym $ right-zero n
  qed)
*-neg -[ n +1] (nneg (n₁ +1)) = refl _
*-neg -[ n +1] -[ n₁ +1] = refl _

neg-* : ∀ x y → neg x * y == neg (x * y)
neg-* x y =
  proof neg x * y
    === y * neg x   :by: comm (neg x) y
    === neg (y * x) :by: *-neg y x
    === neg (x * y) :by: ap neg $ comm y x
  qed

neg-*-neg : ∀ x y → neg x * neg y == x * y
neg-*-neg x y =
  proof neg x * neg y
    === neg (x * neg y)
      :by: neg-* x (neg y)
    === neg (neg (x * y))
      :by: ap neg $ *-neg x y
    === x * y
      :by: left-inv (x * y)
  qed

open import Logic

as-nneg : ∀ (x : ℤ) → ∃ λ m → x == nneg m ∨ x == neg (nneg m)
as-nneg (nneg n) = n , ∨left $ refl (nneg n)
as-nneg -[ n +1] = n +1 , ∨right $ refl -[ n +1]

assoc ⦃ Associative* ⦄ x y z with as-nneg x | as-nneg y | as-nneg z
assoc Associative* .(nneg m) .(nneg n) .(nneg k)
  | m , ∨left (Id.refl .(nneg m))
  | n , ∨left (Id.refl .(nneg n))
  | k , ∨left (Id.refl .(nneg k)) = ap nneg $ assoc m n k
assoc Associative* .(nneg m) .(nneg n) .(neg (nneg k))
  | m , ∨left (Id.refl .(nneg m))
  | n , ∨left (Id.refl .(nneg n))
  | k , ∨right (Id.refl .(neg (nneg k))) =
  proof nneg m * (nneg n * neg (nneg k))
    === nneg m * neg (nneg (n N.* k))
      :by: ap (nneg m *_) $ *-neg (nneg n) (nneg k)
    === neg (nneg (m N.* (n N.* k)))
      :by: *-neg (nneg m) (nneg (n N.* k))
    === neg (nneg (m N.* n N.* k))
      :by: ap (neg ∘ nneg) $ assoc m n k
    === nneg (m N.* n) * neg (nneg k)
      :by: sym $ *-neg (nneg (m N.* n)) (nneg k)
  qed
assoc Associative* .(nneg m) .(neg (nneg n)) .(nneg k)
  | m , ∨left (Id.refl .(nneg m))
  | n , ∨right (Id.refl .(neg (nneg n)))
  | k , ∨left (Id.refl .(nneg k)) =
  proof nneg m * (neg (nneg n) * nneg k)
    === nneg m * neg (nneg (n N.* k))
      :by: ap (nneg m *_) $ neg-* (nneg n) (nneg k)
    === neg (nneg (m N.* (n N.* k)))
      :by: *-neg (nneg m) (nneg (n N.* k))
    === neg (nneg (m N.* n N.* k))
      :by: ap (neg ∘ nneg) $ assoc m n k
    === neg (nneg m * nneg n) * nneg k
      :by: sym $ neg-* (nneg m * nneg n) (nneg k)
    === (nneg m * neg (nneg n)) * nneg k
      :by: ap (_* nneg k) $ sym $ *-neg (nneg m) (nneg n)
  qed
assoc Associative* .(nneg m) .(neg (nneg n)) .(neg (nneg k))
  | m , ∨left (Id.refl .(nneg m))
  | n , ∨right (Id.refl .(neg (nneg n)))
  | k , ∨right (Id.refl .(neg (nneg k))) =
  proof nneg m * (neg (nneg n) * neg (nneg k))
    === nneg (m N.* (n N.* k))
      :by: ap (nneg m *_) $ neg-*-neg (nneg n) (nneg k)
    === nneg (m N.* n) * nneg k
      :by: ap nneg $ assoc m n k
    === neg (nneg m * nneg n) * neg (nneg k)
      :by: sym $ neg-*-neg (nneg m * nneg n) (nneg k)
    === (nneg m * neg (nneg n)) * neg (nneg k)
      :by: ap (_* neg (nneg k)) $ sym $ *-neg (nneg m) (nneg n)
  qed
assoc Associative* .(neg (nneg m)) .(nneg n) .(nneg k)
  | m , ∨right (Id.refl .(neg (nneg m)))
  | n , ∨left (Id.refl .(nneg n))
  | k , ∨left (Id.refl .(nneg k)) =
  proof neg (nneg m) * (nneg n * nneg k)
    === neg (nneg m * (nneg n * nneg k))
      :by: neg-* (nneg m) (nneg n * nneg k)
    === neg (nneg (m N.* n N.* k))
      :by: ap (neg ∘ nneg) $ assoc m n k
    === neg (nneg m * nneg n) * nneg k
      :by: sym $ neg-* (nneg (m N.* n)) (nneg k)
    === (neg (nneg m) * nneg n) * nneg k
      :by: ap (_* nneg k) $ sym $ neg-* (nneg m) (nneg n)
  qed
assoc Associative* .(neg (nneg m)) .(nneg n) .(neg (nneg k))
  | m , ∨right (Id.refl .(neg (nneg m)))
  | n , ∨left (Id.refl .(nneg n))
  | k , ∨right (Id.refl .(neg (nneg k))) = 
  proof neg (nneg m) * (nneg n * neg (nneg k))
    === neg (nneg m) * neg (nneg n * nneg k)
      :by: ap (neg (nneg m) *_) $ *-neg (nneg n) (nneg k)
    === nneg m * (nneg n * nneg k)
      :by: neg-*-neg (nneg m) (nneg n * nneg k)
    === nneg m * nneg n * nneg k
      :by: ap nneg $ assoc m n k
    === neg (nneg m * nneg n) * neg (nneg k)
      :by: sym $ neg-*-neg (nneg m * nneg n) (nneg k)
    === neg (nneg m) * nneg n * neg (nneg k)
      :by: ap (_* neg (nneg k)) $ sym $ neg-* (nneg m) (nneg n)
  qed
assoc Associative* .(neg (nneg m)) .(neg (nneg n)) .(nneg k)
  | m , ∨right (Id.refl .(neg (nneg m)))
  | n , ∨right (Id.refl .(neg (nneg n)))
  | k , ∨left (Id.refl .(nneg k)) =
  proof neg (nneg m) * (neg (nneg n) * nneg k)
    === neg (nneg m) * neg (nneg n * nneg k)
      :by: ap (neg (nneg m) *_) $ neg-* (nneg n) (nneg k)
    === nneg m * (nneg n * nneg k)
      :by: neg-*-neg (nneg m) (nneg n * nneg k)
    === nneg m * nneg n * nneg k
      :by: ap nneg $ assoc m n k
    === neg (nneg m) * neg (nneg n) * nneg k
      :by: ap (_* nneg k) $ sym $ neg-*-neg (nneg m) (nneg n)
  qed
assoc Associative* .(neg (nneg m)) .(neg (nneg n)) .(neg (nneg k))
  | m , ∨right (Id.refl .(neg (nneg m)))
  | n , ∨right (Id.refl .(neg (nneg n)))
  | k , ∨right (Id.refl .(neg (nneg k))) =
  proof neg (nneg m) * (neg (nneg n) * neg (nneg k))
    === neg (nneg m) * (nneg n * nneg k)
      :by: ap (neg (nneg m) *_) $ neg-*-neg (nneg n) (nneg k)
    === neg (nneg m * (nneg n * nneg k))
      :by: neg-* (nneg m) (nneg n * nneg k)
    === neg (nneg m * nneg n * nneg k)
      :by: ap (neg ∘ nneg) $ assoc m n k
    === nneg m * nneg n * neg (nneg k)
      :by: sym $ *-neg (nneg m * nneg n) (nneg k)
    === neg (nneg m) * neg (nneg n) * neg (nneg k)
      :by: ap (_* neg (nneg k)) $ sym $ neg-*-neg (nneg m) (nneg n)
  qed

left-unit ⦃ 1-* ⦄ (nneg n) = ap nneg $ right-unit n
left-unit ⦃ 1-* ⦄ -[ n +1] = ap -[_+1] $ right-unit n

right-unit ⦃ *-1 ⦄ (nneg n) = ap nneg $ right-unit n
right-unit ⦃ *-1 ⦄ -[ n +1] = ap -[_+1] $ right-unit n

nneg+nneg : ∀ m k → nneg m + nneg k == nneg (m N.+ k)
nneg+nneg 0 n = refl (nneg n)
nneg+nneg (m +1) n = ap suc $ nneg+nneg m n

private
  *-+-distrib : (x y z : ℤ) → x * (y + z) == x * y + x * z
*-+-distrib (nneg n) (nneg n₁) (nneg n₂) =
  proof nneg n * (nneg n₁ + nneg n₂)
    === nneg n * nneg (n₁ N.+ n₂)
      :by: ap (nneg n *_) $ nneg+nneg n₁ n₂
    === nneg (n N.* n₁ N.+ n N.* n₂)
      :by: ap nneg $ *[+]==*+* n n₁ n₂
    === nneg (n N.* n₁) + nneg (n N.* n₂)
      :by: sym $ nneg+nneg (n N.* n₁) (n N.* n₂)
  qed
*-+-distrib (nneg n) (nneg n₁) -[ n₂ +1] = {!!}
*-+-distrib (nneg n) -[ n₁ +1] (nneg n₂) = {!!}
*-+-distrib (nneg n) -[ n₁ +1] -[ n₂ +1] = {!!}
*-+-distrib -[ n +1] (nneg n₁) (nneg n₂) = {!!}
*-+-distrib -[ n +1] (nneg n₁) -[ n₂ +1] = {!!}
*-+-distrib -[ n +1] -[ n₁ +1] (nneg n₂) = {!!}
*-+-distrib -[ n +1] -[ n₁ +1] -[ n₂ +1] = {!!}

*[+]==*+* ⦃ Hemiringℕ+* ⦄ = *-+-distrib
[+]*==*+* ⦃ Hemiringℕ+* ⦄ x y z =
  proof (x + y) * z
    === z * (x + y)   :by: comm (x + y) z
    === z * x + z * y :by: *-+-distrib z x y
    === z * x + y * z :by: ap (z * x +_) $ comm z y
    === x * z + y * z :by: ap (_+ y * z) $ comm z x
  qed

open import Structure.Group

Group+ : Group ℤ
_∙_ ⦃ Group+ ⦄ = _+_
e ⦃ Group+ ⦄ = zer
_⁻¹ ⦃ Group+ ⦄ = neg

Monoid* : Monoid ℤ
_∙_ ⦃ Monoid* ⦄ = _*_
e ⦃ Monoid* ⦄ = 1

