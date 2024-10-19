/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.Algebra.Module.Torsion

open Submodule IsLocalizedModule LocalizedModule Ideal nonZeroDivisors

section zero_mem_nonZeroDivisors

lemma zero_mem_nonZeroDivisors {M : Type u_1} [MonoidWithZero M] [Subsingleton M] : 0 ∈ M⁰ :=
  mem_nonZeroDivisors_iff.mp fun _ _ ↦ Subsingleton.eq_zero _

end zero_mem_nonZeroDivisors

namespace Submodule

section localized'_operation_commutativity

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
    {p q : Submodule R M}

lemma localized'_of_trivial (h : 0 ∈ S) : localized' S_R S f p = ⊤  := by
  apply eq_top_iff'.mpr
  intro x
  rw [mem_localized']
  rcases mk'_surjective S f x with ⟨⟨m, r⟩, hmk⟩
  rw [Function.uncurry_apply_pair] at hmk
  refine ⟨0, ⟨Submodule.zero_mem p, ⟨⟨0, h⟩, ?_ ⟩⟩⟩
  rw [mk'_eq_iff, map_zero, Submonoid.mk_smul, zero_smul]

lemma localized'_bot : localized' S_R S f ⊥ = ⊥ := by
  have : ∃ x, x ∈ S := ⟨1, Submonoid.one_mem S⟩
  ext x
  rw [mem_localized']
  simp only [mem_bot, Subtype.exists, exists_eq_left, mk'_zero, exists_prop', nonempty_prop,
    exists_and_right, this, true_and]
  exact eq_comm

lemma localized'_top : localized' S_R S f ⊤ = ⊤ := by
  haveI h : IsLocalizedModule S f := inferInstance
  ext x
  rw [mem_localized']
  rcases  h.surj' x with ⟨⟨u,v⟩,h⟩
  simp only at h
  simp only [mem_top, true_and, iff_true]
  use u, v
  rw [mk'_eq_iff, h]

lemma localized'_sup :
    localized' S_R S f (p ⊔ q) = localized' S_R S f p ⊔ localized' S_R S f q := by
  ext x
  rw [mem_localized', mem_sup]
  constructor
  all_goals intro h
  · rcases h with ⟨m, ⟨hin, ⟨s, hmk⟩⟩⟩
    rcases mem_sup.mp hin with ⟨m1, hm1, m2, hm2, hadd⟩
    exact ⟨mk' f m1 s, ⟨m1, hm1, s, rfl⟩, mk' f m2 s, ⟨m2, hm2, s, rfl⟩, by rw [← mk'_add, hadd, hmk]⟩
  · rcases h with ⟨x1, ⟨m1, hm1, s, hmk1⟩, x2, ⟨m2, hm2, t, hmk2⟩, hadd⟩
    exact ⟨t • m1 + s • m2, mem_sup.mpr ⟨t • m1, smul_mem _ _ hm1, s • m2, smul_mem _ _ hm2, rfl⟩,
      ⟨s * t, by rw[← mk'_add_mk', hmk1, hmk2, hadd]⟩⟩

lemma localized'_inf :
    localized' S_R S f (p ⊓ q) = localized' S_R S f p ⊓ localized' S_R S f q := by
  ext x
  rw [mem_localized', mem_inf, mem_localized', mem_localized']
  constructor
  all_goals intro h
  · rcases h with ⟨m, ⟨⟨hinp, hinq⟩, hmk⟩⟩
    exact ⟨⟨m, hinp, hmk⟩, ⟨m, hinq, hmk⟩⟩
  · rcases h with ⟨⟨m, hminp, ⟨s, hmmk⟩⟩, ⟨n, hninq, ⟨t, hnmk⟩⟩⟩
    have ⟨u, hu⟩ := (mk'_eq_mk'_iff _ _ _ _ _).mp <| hnmk ▸ hmmk
    use u • s • n
    constructor
    · exact ⟨hu.symm ▸ smul_mem _ _ <| smul_mem _ _ hminp, smul_mem _ _ <| smul_mem _ _ hninq⟩
    · exact ⟨u * s * t, by rw [mul_assoc, mk'_cancel_left, mk'_cancel_left, hnmk]⟩

#check span
#check Submodule.map_span
--this may be right when s is finite
lemma localized'_span (s : Set M) : localized' S_R S f (span R s) = span S_R (f '' s) := by
  ext x
  rw [mem_localized', mem_span]
  constructor
  all_goals intro h
  · intro S_p hsub
    rcases h with ⟨m, hm, t, hmk⟩
    rw [mem_span] at hm
    sorry
  ·
    sorry

end localized'_operation_commutativity

section localized_operation_commutativity

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) {p q : Submodule R M}

lemma localized_of_trivial (h : 0 ∈ S) : localized S p = ⊤ := localized'_of_trivial _ _ _ h

lemma localized_bot : localized S (⊥ : Submodule R M) = ⊥ := localized'_bot _ _ _

lemma localized_top : localized S (⊤ : Submodule R M) = ⊤ := localized'_top _ _ _

lemma localized_sup : localized S (p ⊔ q) = localized S p ⊔ localized S q :=
  localized'_sup _ _ _

lemma localized_inf : localized S (p ⊓ q) = localized S p ⊓ localized S q :=
  localized'_inf _ _ _

end localized_operation_commutativity

section torsion

lemma torsion_of_subsingleton {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (h : Subsingleton R) : torsion R M = ⊤ :=
  eq_top_iff'.mpr <| fun x ↦ (mem_torsion_iff x).mp
  ⟨⟨0, zero_mem_nonZeroDivisors⟩, by rw [Submonoid.mk_smul, zero_smul]⟩

end torsion

section annihilator



end annihilator
