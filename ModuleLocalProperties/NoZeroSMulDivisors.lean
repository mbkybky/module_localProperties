/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Torsion
import ModuleLocalProperties.Basic

import ModuleLocalProperties.MissingLemmas.Localization
import ModuleLocalProperties.MissingLemmas.LocalizedModule


open Submodule LocalizedModule IsLocalizedModule LinearMap nonZeroDivisors

set_option linter.unusedVariables false

section missinglemma

lemma NoZeroSMulDivisors.of_subsingleton {R M : Type*} [Zero R] [Zero M] [SMul R M]
    [Subsingleton R] : NoZeroSMulDivisors R M := by
  apply (noZeroSMulDivisors_iff R M).mpr
  intro r m hr
  left
  exact Subsingleton.eq_zero r

lemma Localization.mk_surjective {R : Type*} [CommSemiring R] (S : Submonoid R)
    (y : Localization S) : ∃ r ,∃ s, Localization.mk r s = y := by
  rcases IsLocalization.mk'_surjective S y with ⟨r, s, h⟩
  use r, s
  rw [← h, mk_eq_mk']

lemma Localization.mk_mem_nonZeroDivisors {R : Type*} [CommRing R] (S : Submonoid R)
    (nontrival : 0 ∉ S) (r : R) (s : S) (h : mk r s ∈ (Localization S)⁰) : r ≠ 0 := by
  haveI := OreLocalization.nontrivial_iff.mpr nontrival
  exact IsLocalization.ne_zero_of_mk'_ne_zero <| mk_eq_mk' (R := R) ▸ nonZeroDivisors.ne_zero h

lemma torsion_of_subsingleton {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (h : Subsingleton R) : torsion R M = ⊤ :=
  eq_top_iff'.mpr <| fun x ↦ (mem_torsion_iff x).mp
  ⟨⟨0, zero_mem_nonZeroDivisors⟩, by rw [Submonoid.mk_smul, zero_smul]⟩

end missinglemma

section localized'_torsion_commutivity

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
include S f

namespace Submodule

lemma localized'_torsion_le :
    localized' S_R S f (torsion R M) ≤ torsion S_R S_M := by
  intro x h
  rcases (mem_localized' _ _ _ _ _).mp h with ⟨m, hin, s, hmk⟩
  rcases (mem_torsion_iff _).mp hin with ⟨r, hr⟩
  have hr' : (r : R) • m = 0 := hr
  rw [mem_torsion_iff]
  use ⟨algebraMap R S_R r, IsLocalization.mem_map_nonZeroDivisors _ S r⟩
  dsimp
  rw [← hmk, algebraMap_smul, ← mk'_smul, hr', IsLocalizedModule.mk'_zero]

lemma localized'_torsion_nontrival_ge [IsDomain R] (nontrivial : 0 ∉ S) :
    localized' S_R S f (torsion R M) ≥ torsion S_R S_M := by
  intro x h
  rcases (mem_torsion_iff _).mp h with ⟨y, hxy⟩
  have hxy' : (y : S_R) • x = 0 := hxy
  rcases mk'_surjective S f x with ⟨⟨m, s⟩, hx⟩
  dsimp at hx
  rw [mem_localized']
  use m
  constructor
  · rw [mem_torsion_iff]
    rcases IsLocalization.mk'_surjective S (y : S_R) with ⟨r, t, hy⟩
    rw [← hy, ← hx, mk'_smul_mk', mk'_eq_zero'] at hxy'
    rcases hxy' with ⟨c, hc⟩
    have := IsLocalization.mk'_mem_nonZeroDivisors S_R S nontrivial r t <| hy ▸ y.prop
    have : c * r ≠ 0 := by
      apply mul_ne_zero _ this
      by_contra h
      exact (h.symm ▸ nontrivial) c.prop
    use ⟨c * r, mem_nonZeroDivisors_of_ne_zero <| this⟩
    dsimp
    rw [← smul_eq_mul, smul_assoc]
    exact hc
  · use s

lemma localized'_torsion_trival [IsDomain R] (trivial : 0 ∈ S) :
    localized' S_R S f (torsion R M) = torsion S_R S_M :=
  (torsion_of_subsingleton (R := S_R) (M := S_M) <|
  IsLocalization.subsingleton trivial) ▸ localized'_of_trivial _ S f trivial

lemma localized'_torsion [IsDomain R] :
    localized' S_R S f (torsion R M) = torsion S_R S_M := by
  by_cases trivial : 0 ∈ S
  · exact localized'_torsion_trival _ _ _ trivial
  · apply eq_of_le_of_le
    exact localized'_torsion_le _ _ _
    exact localized'_torsion_nontrival_ge _ _ _ trivial

end Submodule

lemma IsLocalizedModule.noZeroSMulDivisors [IsDomain R] (h : NoZeroSMulDivisors R M) :
    NoZeroSMulDivisors S_R S_M := by
  by_cases ht : 0 ∈ S
  · haveI : Subsingleton S_R := IsLocalization.subsingleton ht
    exact NoZeroSMulDivisors.of_subsingleton
  · haveI := IsLocalization.isDomain_of_noZeroDivisors S_R S
    haveI := IsLocalization.nontrivial S_R S ht
    rw [noZeroSMulDivisors_iff_torsion_eq_bot] at h ⊢
    rw [← localized'_torsion _ S f, h, localized'_bot]

end localized'_torsion_commutivity

section localized_torsion_commutivity

variable {R : Type*} [CommRing R] (S : Submonoid R) (M : Type*) [AddCommGroup M] [Module R M]

namespace Submodule

lemma localized_torsion_le :
    localized S (torsion R M) ≤ torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion_le _ _ _

lemma localized_torsion_nontrival_ge [IsDomain R] (nontrivial : 0 ∉ S) :
    localized S (torsion R M) ≥ torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion_nontrival_ge _ _ _ nontrivial

lemma localized_torsion_trival [IsDomain R] (trivial : 0 ∈ S) :
    localized S (torsion R M) = torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion_trival _ _ _ trivial

lemma localized_torsion [IsDomain R] :
    localized S (torsion R M) = torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion _ _ _

end Submodule

lemma LocalizedModule.noZeroSMulDivisors [IsDomain R] (h : NoZeroSMulDivisors R M) :
    NoZeroSMulDivisors (Localization S) (LocalizedModule S M) :=
  IsLocalizedModule.noZeroSMulDivisors _ S (mkLinearMap S M) h

end localized_torsion_commutivity

section NoZeroSMulDivisors_local_property

variable {R : Type*} [CommRing R] [IsDomain R] (M : Type*) [AddCommGroup M] [Module R M]

namespace Submodule

lemma noZeroSMulDivisors_of_localization (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M)) :
    NoZeroSMulDivisors R M :=
  noZeroSMulDivisors_iff_torsion_eq_bot.mpr <| submodule_eq_bot_of_localization _ <| fun J hJ ↦
  localized_torsion J.primeCompl M ▸ noZeroSMulDivisors_iff_torsion_eq_bot.mp <| h J hJ

lemma noZeroSMulDivisors_of_localization_iff :
    NoZeroSMulDivisors R M ↔ ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M) :=
  ⟨fun h J _ ↦ LocalizedModule.noZeroSMulDivisors J.primeCompl _ h,
    noZeroSMulDivisors_of_localization M⟩

end Submodule
end NoZeroSMulDivisors_local_property
