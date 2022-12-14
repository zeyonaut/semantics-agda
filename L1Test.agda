{-# OPTIONS --without-K --exact-split --safe #-}

module L1Test where

open import Prelude
open import L1
open import L1Properties

open import Agda.Builtin.FromNeg

+ : ℕ → ℤ
+ n = pos n

instance
  ℤNeg : Negative ℤ
  ℤNeg .Negative.Constraint _    = 𝟏
  ℤNeg .Negative.fromNeg zero    = pos zero
  ℤNeg .Negative.fromNeg (suc n) = nsuc n

test-0 : ev? []
             (int! -11 op[ o+ ] int! (+ 7))
             []
             1
       ≡ some (int! -4 , [])
test-0 = refl _

test-1 : ev? (intref :: [])
             (fin 0 := (* (fin 0) op[ o+ ] int! (+ 1)))
             ((+ 0) :: [])
             3
       ≡ some (skip , (+ 1) :: [])
test-1 = refl _

test-2 : ev? []
             (int! (+ 12) op[ o≥ ] int! (+ 12))
             []
             1
       ≡ some (bool! true , [])
test-2 = refl _

test-3 : ev? (intref :: intref :: intref :: [])
             (
             while * (fin 1) op[ o≥ ] * (fin 0)
             loop  ( (fin 2 := (* (fin 2) op[ o+ ] * (fin 0)))
                   ; (fin 0 := (* (fin 0) op[ o+ ] int! (+ 1)))
                   )
             )
             ((+ 0) :: (+ 10) :: (+ 0) :: [])
             159
             ≡ some (skip , (+ 11) :: (+ 10) :: (+ 55) :: [])
test-3 = refl _