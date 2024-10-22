/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Torsion
import ModuleLocalProperties.Basic

import ModuleLocalProperties.MissingLemmas.LocalizedModule

open Submodule LocalizedModule IsLocalizedModule LinearMap nonZeroDivisors

set_option linter.unusedVariables false

section missinglemma

lemma IsLocalization.mem_map_nonZeroDivisors {R : Type*} [CommSemiring R] (S : Submonoid R)
    (S_R : Type*) [CommSemiring S_R] [Algebra R S_R] [IsLocalization S S_R] (r : R⁰) :
    algebraMap R S_R r ∈ S_R⁰ :=
  map_nonZeroDivisors_le S S_R <| Submonoid.apply_coe_mem_map _ _ r

lemma Localization.mk_surjective {R : Type*} [CommSemiring R] (S : Submonoid R)
    (y : Localization S) : ∃ r ,∃ s, Localization.mk r s = y := by
  rcases IsLocalization.mk'_surjective S y with ⟨r, s, h⟩
  use r, s
  rw [← h, mk_eq_mk']

lemma Localization.mk_mem_nonZeroDivisors {R : Type*} [CommRing R] (S : Submonoid R)
    (nontrival : 0 ∉ S) (r : R) (s : S) (h : mk r s ∈ (Localization S)⁰) : r ≠ 0 := by
  haveI := OreLocalization.nontrivial_iff.mpr nontrival
  exact IsLocalization.ne_zero_of_mk'_ne_zero <| mk_eq_mk' (R := R) ▸ nonZeroDivisors.ne_zero h

end missinglemma

namespace Submodule

section localized_torsion_commutivity

variable {R : Type*} [CommRing R] (S : Submonoid R) (M : Type*) [AddCommGroup M] [Module R M]

lemma torsion_of_subsingleton {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (h : Subsingleton R) : torsion R M = ⊤ :=
  eq_top_iff'.mpr <| fun x ↦ (mem_torsion_iff x).mp
  ⟨⟨0, zero_mem_nonZeroDivisors⟩, by rw [Submonoid.mk_smul, zero_smul]⟩

lemma localized_torsion_le :
    localized S (torsion R M) ≤ torsion (Localization S) (LocalizedModule S M) := by
  intro x h
  rcases (mem_localized' _ _ _ _ _).mp h with ⟨m, hin, s, hmk⟩
  rcases (mem_torsion_iff _).mp hin with ⟨r, hr⟩
  have hr' : (r : R) • m = 0 := hr
  rw [mem_torsion_iff]
  use ⟨algebraMap R (Localization S) r, IsLocalization.mem_map_nonZeroDivisors S _ r⟩
  dsimp
  rw [← hmk, algebraMap_smul, ← mk'_smul, hr', IsLocalizedModule.mk'_zero]

lemma localized_torsion_nontrival_ge [IsDomain R] (nontrivial : 0 ∉ S) :
    localized S (torsion R M) ≥ torsion (Localization S) (LocalizedModule S M) := by
  intro x h
  rcases (mem_torsion_iff _).mp h with ⟨y, hxy⟩
  have hxy' : (y : Localization S) • x = 0 := hxy
  rcases mk'_surjective S (mkLinearMap S M) x with ⟨⟨m, s⟩, hx⟩
  dsimp at hx
  rw [mem_localized']
  use m
  constructor
  · rw [mem_torsion_iff]
    rcases Localization.mk_surjective S y with ⟨r, t, hy⟩
    rw [← mk_eq_mk'] at hx
    rw [← hy, ← hx, mk_smul_mk, mk_eq_zero_iff] at hxy'
    rcases hxy' with ⟨c, hc⟩
    have := Localization.mk_mem_nonZeroDivisors _ nontrivial r t <| hy ▸ y.prop
    have : c * r ≠ 0 := by
      apply mul_ne_zero _ this
      by_contra h
      exact (h.symm ▸ nontrivial) c.prop
    use ⟨c * r, mem_nonZeroDivisors_of_ne_zero <| this⟩
    dsimp
    rw [← smul_eq_mul, smul_assoc]
    exact hc
  · use s

lemma localized_torsion_trival [IsDomain R] (trivial : 0 ∈ S) :
    localized S (torsion R M) = torsion (Localization S) (LocalizedModule S M) :=
  (torsion_of_subsingleton (M := LocalizedModule S M) <|
  OreLocalization.subsingleton_iff.mpr trivial) ▸ localized_of_trivial S trivial

lemma localized_torsion [IsDomain R] :
    localized S (torsion R M) = torsion (Localization S) (LocalizedModule S M) := by
  by_cases trivial : 0 ∈ S
  · exact localized_torsion_trival _ _ trivial
  · apply eq_of_le_of_le
    exact localized_torsion_le _ _
    exact localized_torsion_nontrival_ge _ _ trivial

end localized_torsion_commutivity

section NoZeroSMulDivisors_local_property

variable {R : Type*} [CommRing R] [IsDomain R] (M : Type*) [AddCommGroup M] [Module R M]

lemma noZeroSMulDivisors_of_localization (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M)) :
    NoZeroSMulDivisors R M :=
  noZeroSMulDivisors_iff_torsion_eq_bot.mpr <| submodule_eq_bot_of_localization _ <| fun J hJ ↦
  localized_torsion J.primeCompl M ▸ noZeroSMulDivisors_iff_torsion_eq_bot.mp <| h J hJ

lemma LocalizedModule.noZeroSMulDivisors (h : NoZeroSMulDivisors R M) :
    ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M) :=
  fun J _ ↦ (noZeroSMulDivisors_iff_torsion_eq_bot.mp h) ▸ localized_torsion J.primeCompl M ▸
    noZeroSMulDivisors_iff_torsion_eq_bot.mpr <| localized_bot _

lemma noZeroSMulDivisors_of_localization_iff :
    NoZeroSMulDivisors R M ↔ ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M) :=
  ⟨LocalizedModule.noZeroSMulDivisors M, noZeroSMulDivisors_of_localization M⟩

end NoZeroSMulDivisors_local_property

section annihilator

end annihilator
