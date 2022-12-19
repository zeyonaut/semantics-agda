{-# OPTIONS --without-K --exact-split --safe #-}

module L1Test where

open import Prelude
open import L1
open import L1Properties

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg

-- Enable integer literals for bounded naturals, integers, and L1 expressions.
private instance
  _ = nat!-Fin
  _ = nat!-ℤ
  _ = neg!-ℤ
  _ = nat!-Ex
  _ = neg!-Ex

-- Various tests for L1 evaluation.
test-0 : ev? []
             (-11 op[ o+ ] 7)
             []
             1
       ≡ some (-4 , [])
test-0 = refl _

test-1 : ev? (^int :: [])
             (0 := (^ 0 op[ o+ ] 1))
             (0 :: [])
             3
       ≡ some (skip , 1 :: [])
test-1 = refl _

test-2 : ev? []
             (12 op[ o≥ ] 12)
             []
             1
       ≡ some (bool: true , [])
test-2 = refl _

test-3 : ev? (^int :: ^int :: ^int :: [])
             (
             while ^ 1 op[ o≥ ] ^ 0
             loop  ( (2 := (^ 2 op[ o+ ] ^ 0))
                   ; (0 := (^ 0 op[ o+ ] 1))
                   )
             )
             (0 :: 10 :: 0 :: [])
             159
             ≡ some (skip , 11 :: 10 :: 55 :: [])
test-3 = refl _