/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su
-/
import Mathlib.Algebra.Module.Submodule.Localization

open Submodule IsLocalizedModule LocalizedModule Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Submonoid R) [IsLocalization p S]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module S Q]
  [IsScalarTower R S Q] (f' : P →ₗ[R] Q) [IsLocalizedModule p f']

lemma LinearMap.localized'_range_eq_range_localizedMap (g : M →ₗ[R] P) :
    localized' S p f' (LinearMap.range g) =
      LinearMap.range ((map p f f' g).extendScalarsOfIsLocalization p S) := by
  ext x
  simp only [mem_localized', extendScalarsOfIsLocalization_apply']
  constructor
  · rintro ⟨r, hr, a, ha⟩
    obtain ⟨m, hm⟩ := mem_range.mp hr
    exact ⟨(mk' f m a), by rw [extendScalarsOfIsLocalization_apply', map_mk', hm, ha]⟩
  · intro h
    obtain ⟨n, hn⟩ := mem_range.mp h
    obtain ⟨m, hm⟩ := surj p f n
    exact ⟨(g m.1), mem_range_self g m.1, m.2, by
      rw [← hn, extendScalarsOfIsLocalization_apply', ← mk'_eq_iff.mpr hm.symm, map_mk']⟩
