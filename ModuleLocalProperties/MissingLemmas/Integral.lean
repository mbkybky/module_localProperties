/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SiHan Su
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AsSubring

open Localization IsLocalization

lemma IsLocalization.isIntegrallyClosed {R A : Type*} [CommRing R] [IsDomain R] (S : Submonoid R)
    [CommRing A] [Algebra R A] [IsLocalization S A] (int : IsIntegrallyClosed R) (hs : 0 ∉ S) :
    IsIntegrallyClosed A := by
  have le := le_nonZeroDivisors_of_noZeroDivisors hs
  letI alg := (mapToFractionRing (FractionRing R) S A le).toAlgebra
  letI : IsFractionRing A (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization S _ _ le
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨r, hr⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S _ hx
  obtain ⟨y, eqy⟩ := (isIntegrallyClosed_iff (FractionRing R)).mp int hr
  use (y • mk' A 1 r)
  calc
    _ = ((algebraMap R _) y) * (algebraMap _ _) (mk' A 1 r) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R A (FractionRing R),
        _root_.map_mul]
    _ = _ := by
      have : r • x = r.1 • x := rfl
      rw [eqy, this, Algebra.smul_def, IsScalarTower.algebraMap_apply R A _,
        mul_comm, ← mul_assoc, ← _root_.map_mul, mk'_spec, map_one, map_one, one_mul]

lemma Localization.isIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R]
    (int : IsIntegrallyClosed R) (S : Submonoid R) (hs : 0 ∉ S):
    IsIntegrallyClosed (Localization S) :=
  IsLocalization.isIntegrallyClosed S int hs
