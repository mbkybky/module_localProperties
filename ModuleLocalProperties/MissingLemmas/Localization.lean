/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.RingTheory.Localization.Ideal
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
    (S : Submonoid R) [IsLocalization S S_R]
include S

lemma isDomain_of_isDomain_nontrivial [IsDomain R] (h : 0 ∉ S) : IsDomain S_R :=
  isDomain_of_le_nonZeroDivisors R <| le_nonZeroDivisors_of_noZeroDivisors h

lemma isDomain_of_noZeroDivisors [IsDomain R] : NoZeroDivisors S_R := by
  by_cases trivial : 0 ∈ S
  · haveI : Subsingleton S_R := subsingleton trivial
    apply Subsingleton.to_noZeroDivisors
  · haveI := isDomain_of_isDomain_nontrivial S_R S trivial
    apply IsDomain.to_noZeroDivisors

lemma noZeroDivisors_of_noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors S_R := by
  by_cases nontrivial : Nontrivial R
  · haveI := (isDomain_iff_noZeroDivisors_and_nontrivial R).mpr ⟨inferInstance , nontrivial⟩
    exact isDomain_of_noZeroDivisors _ S
  · haveI := not_nontrivial_iff_subsingleton.mp nontrivial
    haveI : Subsingleton S_R := subsingleton <| (subsingleton_iff_zero_eq_one.mpr this) ▸ one_mem S
    apply Subsingleton.to_noZeroDivisors

end IsDomain

section

variable {R : Type*} (S_R : Type*) [CommSemiring R] [CommSemiring S_R] [Algebra R S_R]
    (S : Submonoid R) [IsLocalization S S_R] (p q : Ideal R)
include S

lemma ideal_map_inf : Ideal.map (algebraMap R S_R) (p ⊓ q) =
    Ideal.map (algebraMap R S_R) p ⊓ Ideal.map (algebraMap R S_R) q := by
  apply eq_of_le_of_le <| Ideal.map_inf_le (algebraMap R S_R)
  rintro x ⟨hp, hq⟩
  rcases mk'_surjective S x with ⟨r, s, hmk⟩
  rw [SetLike.mem_coe] at hp hq
  rw [← hmk, mk'_mem_map_algebraMap_iff S] at hp hq ⊢
  rcases hp with ⟨u, hu, hpmk⟩
  rcases hq with ⟨v, hv, hqmk⟩
  use u * v
  constructor
  · exact Submonoid.mul_mem S hu hv
  · apply Ideal.mem_inf.mpr
    constructor
    · rw [mul_comm u, mul_assoc]
      exact p.mul_mem_left _ hpmk
    · rw [mul_assoc]
      apply q.mul_mem_left _ hqmk

end
