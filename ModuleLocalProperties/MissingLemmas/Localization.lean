/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization

open nonZeroDivisors

namespace IsLocalization

section IsLocalization.nontrivial

variable {R : Type*} (S_R : Type*) [CommSemiring R] [CommSemiring S_R] [Algebra R S_R]
    (S : Submonoid R) [IsLocalization S S_R]
include S

lemma nontrivial (h : 0 ∉ S) : Nontrivial S_R := by
  apply nontrivial_of_ne (0 : S_R) 1
  intro heq
  rw [← (algebraMap R S_R).map_one, ← (algebraMap R S_R).map_zero] at heq
  obtain ⟨t, ht⟩ := (eq_iff_exists S S_R).mp heq
  rw [mul_zero, mul_one] at ht
  exact h (ht ▸ t.prop)

lemma nontrivial_iff : Nontrivial S_R ↔ 0 ∉ S := by
  constructor
  · contrapose!
    exact fun h ↦ not_nontrivial_iff_subsingleton.mpr <| subsingleton h
  · exact fun h ↦ nontrivial _ _ h

lemma mk'_mem_nonZeroDivisors (h : 0 ∉ S) (r : R) (s : S) (hmk : mk' S_R r s ∈ S_R⁰) : r ≠ 0 := by
  haveI : Nontrivial S_R := nontrivial S_R S h
  exact ne_zero_of_mk'_ne_zero <| nonZeroDivisors.ne_zero hmk

lemma mem_map_nonZeroDivisors (r : R⁰) : algebraMap R S_R r ∈ S_R⁰ :=
  map_nonZeroDivisors_le S S_R <| Submonoid.apply_coe_mem_map _ _ r

end IsLocalization.nontrivial

section IsDomain

variable {R : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    (S : Submonoid R) [IsLocalization S S_R] [IsDomain R]
include S

lemma isDomain_of_isDomain_nontrivial (h : 0 ∉ S) : IsDomain S_R :=
  isDomain_of_le_nonZeroDivisors R <| le_nonZeroDivisors_of_noZeroDivisors h

lemma isDomain_of_noZeroDivisors : NoZeroDivisors S_R := by
  by_cases trivial : 0 ∈ S
  · haveI : Subsingleton S_R := subsingleton trivial
    apply Subsingleton.to_noZeroDivisors
  · haveI := isDomain_of_isDomain_nontrivial S_R S trivial
    apply IsDomain.to_noZeroDivisors

end IsDomain
