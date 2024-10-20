/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SiHan Su
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AsSubring

open Localization
lemma Localization.IsIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R]
    (int : IsIntegrallyClosed R) (S : Submonoid R) (hs : 0 ∉ S):
    IsIntegrallyClosed (Localization S) := by
  have le := le_nonZeroDivisors_of_noZeroDivisors hs
  letI alg := (mapToFractionRing (FractionRing R) S (Localization S) le).toAlgebra
  letI : IsFractionRing (Localization S) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization S _ _ le
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨r, hr⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S _ hx
  obtain ⟨y, eqy⟩ := (isIntegrallyClosed_iff (FractionRing R)).mp int hr
  use (y • mk 1 r)
  calc
    _ = ((algebraMap R _) y) * (algebraMap _ _) (mk 1 r) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization S) (FractionRing R),
        _root_.map_mul]
    _ = _ := by
      have : r • x = r.1 • x := rfl
      rw [eqy, this, Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization S) _,
        mul_comm, ← mul_assoc, ← _root_.map_mul, ← mk_one_eq_algebraMap, mk_mul]
      simp only [mk_self, one_mul, mul_one, map_one]
