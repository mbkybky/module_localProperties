/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

attribute [local instance] FractionRing.liftAlgebra

instance {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [NoZeroSMulDivisors A B] :
    FiniteDimensional (FractionRing A) (FractionRing B) := sorry
