/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Submodule.Localization


open Submodule IsLocalizedModule LocalizedModule Ideal nonZeroDivisors

section zero_mem_nonZeroDivisors

lemma zero_mem_nonZeroDivisors {M : Type u_1} [MonoidWithZero M] [Subsingleton M] : 0 ∈ M⁰ :=
  mem_nonZeroDivisors_iff.mp fun _ _ ↦ Subsingleton.eq_zero _

end zero_mem_nonZeroDivisors

section mk_lemma

variable {R M S_M : Type*} (S_R : Type*) [CommSemiring R] [CommSemiring S_R] [Algebra R S_R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
    (S_p : Submodule S_R S_M)

namespace IsLocalizedModule

lemma mk'_right_smul_mk' (m : M) (s t : S) :
    IsLocalization.mk' S_R 1 s • mk' f m t = mk' f m (s * t) := by
  rw[mk'_smul_mk', one_smul]

lemma mk'_right_smul_mk'_left (m : M) (s : S) :
    IsLocalization.mk' S_R 1 s • f m = mk' f m s := by
  rw[← mul_one s, ← mk'_right_smul_mk' S_R, mk'_one, mul_one]

end IsLocalizedModule

namespace Submodule

section localized'OrderEmbedding

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
    (S_p : Submodule S_R S_M)

lemma localized'_comap_eq : localized' S_R S f (comap f (restrictScalars R S_p)) = S_p := by
  ext x
  constructor
  all_goals intro h
  · rw [mem_localized'] at h
    rcases h with ⟨m, hm, s, hmk⟩
    rw [mem_comap, restrictScalars_mem] at hm
    rw [← hmk, ← mk'_right_smul_mk'_left S_R]
    exact smul_mem _ _ hm
  · rw [mem_localized']
    rcases mk'_surjective S f x with ⟨⟨m, s⟩, hmk⟩
    dsimp at hmk
    use m
    constructor
    · rw [mem_comap, restrictScalars_mem, ← mk'_cancel' f m s, hmk]
      exact smul_of_tower_mem S_p s h
    · use s

lemma localized'_mono {p q : Submodule R M} : p ≤ q → localized' S_R S f p ≤ localized' S_R S f q :=
  fun h _ ⟨m, hm, s, hmk⟩ ↦ ⟨m, h hm, s, hmk⟩

def localized'OrderEmbedding : Submodule S_R S_M ↪o Submodule R M where
  toFun := fun S_p ↦ comap f (restrictScalars R S_p)
  inj' := Function.LeftInverse.injective <| localized'_comap_eq S_R S f
  map_rel_iff' := by
    intro S_p S_q
    constructor
    · intro h
      rw [← localized'_comap_eq S_R S f S_p, ← localized'_comap_eq S_R S f S_q]
      exact localized'_mono _ _ _ h
    · exact fun h ↦ comap_mono h

end localized'OrderEmbedding

section localized'_operation_commutativity

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
    {p q : Submodule R M}

lemma localized'_of_trivial (h : 0 ∈ S) : localized' S_R S f p = ⊤ := by
  apply eq_top_iff'.mpr
  intro x
  rw [mem_localized']
  rcases mk'_surjective S f x with ⟨⟨m, r⟩, hmk⟩
  rw [Function.uncurry_apply_pair] at hmk
  refine ⟨0, ⟨Submodule.zero_mem p, ⟨⟨0, h⟩, ?_ ⟩⟩⟩
  rw [mk'_eq_iff, map_zero, Submonoid.mk_smul, zero_smul]

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

lemma localized_span (s : Set M) :
    localized S (span R s) = span (Localization S) ((mkLinearMap S M) '' s) :=
  localized'_span _ _ _ _

end localized_operation_commutativity
