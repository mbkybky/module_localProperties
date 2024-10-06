/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IsTensorProduct

open TensorProduct

section ideal

def wfw {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
  (S : Submonoid R) : (Ideal.map (algebraMap R (Localization S)) I) →ₗ[R]
  (LocalizedModule S M) →ₗ[R] (LocalizedModule S (I ⊗[R] M)) := sorry

example {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
  (S : Submonoid R) : IsTensorProduct (wfw I M S) := by sorry

end ideal

section module

def efwef {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (S : Submonoid R) : (LocalizedModule S M) →ₗ[R] (LocalizedModule S N) →ₗ[R] (LocalizedModule S (M ⊗[R] N)) := sorry

example {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (S : Submonoid R) : IsTensorProduct (efwef M N S) := by sorry

end module
