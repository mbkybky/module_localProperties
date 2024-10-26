/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  (p : Ideal A) (P : Ideal B) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [Algebra K L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Normal K L]

example : Normal (A ⧸ p) (B ⧸ P) := sorry
