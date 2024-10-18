/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization

open Submodule IsLocalizedModule LocalizedModule Ideal

namespace Submodule

section localized'_operation_commutativity

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]

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

lemma localized'_sup {p q : Submodule R M} :
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

lemma localized'_inf {p q : Submodule R M} :
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

end localized'_operation_commutativity

section localized_operation_commutativity

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R)

lemma localized_bot : localized S (⊥ : Submodule R M) = ⊥ := localized'_bot _ _ _

lemma localized_top : localized S (⊤ : Submodule R M) = ⊤ := localized'_top _ _ _

lemma localized_sup {p q : Submodule R M} : localized S (p ⊔ q) = localized S p ⊔ localized S q :=
  localized'_sup _ _ _

lemma localized_inf {p q : Submodule R M} : localized S (p ⊓ q) = localized S p ⊓ localized S q :=
  localized'_inf _ _ _



end localized_operation_commutativity
