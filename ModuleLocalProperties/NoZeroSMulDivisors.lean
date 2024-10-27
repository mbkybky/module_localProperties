/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.LocalProperties.Basic
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

lemma torsion_of_subsingleton {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (h : Subsingleton R) : torsion R M = ⊤ :=
  eq_top_iff'.mpr <| fun x ↦ (mem_torsion_iff x).mp
  ⟨⟨0, zero_mem_nonZeroDivisors⟩, by rw [Submonoid.mk_smul, zero_smul]⟩

end missinglemma

section annihilator_sup

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  (p q : Submodule R M)

lemma annihilator_sup : annihilator (p ⊔ q) = p.annihilator ⊓ q.annihilator := by
  apply eq_of_le_of_le
  · apply le_inf
    · exact annihilator_mono <| SemilatticeSup.le_sup_left _ _
    · exact annihilator_mono <| SemilatticeSup.le_sup_right _ _
  · intro x hx
    rcases mem_inf.mp hx with ⟨hp, hq⟩
    rw [mem_annihilator'] at hp hq ⊢
    exact sup_le hp hq

end Submodule
end annihilator_sup

section noZeroSMulDivisors_iff_annihilator_singleton_eq_bot

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace Submodule

lemma noZeroSMulDivisors_iff_annihilator_singleton_eq_bot :
    NoZeroSMulDivisors R M ↔ ∀ m : M, m ≠ 0 → (span R {m}).annihilator = ⊥ := by
  rw [noZeroSMulDivisors_iff]
  constructor
  all_goals intro h
  · intro m hm
    rw [Submodule.eq_bot_iff]
    intro r hr
    rw [mem_annihilator_span_singleton] at hr
    exact or_iff_not_imp_right.mp (h hr) hm
  · intro r m hmul
    rw [or_iff_not_imp_right]
    intro hm
    exact ((Submodule.eq_bot_iff _).mp <| h m hm) r <| (mem_annihilator_span_singleton m r).mpr hmul

end Submodule
end noZeroSMulDivisors_iff_annihilator_singleton_eq_bot

section localized_torsion_commutivity

namespace Submodule

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
include S f

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

lemma localized'_torsion_nontrival_ge [NoZeroDivisors R] (nontrivial : 0 ∉ S) :
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

lemma localized'_torsion_of_trivial [NoZeroDivisors R] (trivial : 0 ∈ S) :
    localized' S_R S f (torsion R M) = torsion S_R S_M :=
  (torsion_of_subsingleton (R := S_R) (M := S_M) <|
  IsLocalization.subsingleton trivial) ▸ localized'_of_trivial _ S f trivial

lemma localized'_torsion [NoZeroDivisors R] :
    localized' S_R S f (torsion R M) = torsion S_R S_M := by
  by_cases trivial : 0 ∈ S
  · exact localized'_torsion_of_trivial _ _ _ trivial
  · apply eq_of_le_of_le
    exact localized'_torsion_le _ _ _
    exact localized'_torsion_nontrival_ge _ _ _ trivial

end Submodule

namespace Submodule

variable {R : Type*} [CommRing R] (S : Submonoid R) (M : Type*) [AddCommGroup M] [Module R M]

lemma localized_torsion_le :
    localized S (torsion R M) ≤ torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion_le _ _ _

lemma localized_torsion_nontrival_ge [NoZeroDivisors R] (nontrivial : 0 ∉ S) :
    localized S (torsion R M) ≥ torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion_nontrival_ge _ _ _ nontrivial

lemma localized_torsion_of_trivial [NoZeroDivisors R] (trivial : 0 ∈ S) :
    localized S (torsion R M) = torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion_of_trivial _ _ _ trivial

lemma localized_torsion [NoZeroDivisors R] :
    localized S (torsion R M) = torsion (Localization S) (LocalizedModule S M) :=
  localized'_torsion _ _ _

end Submodule
end localized_torsion_commutivity

section localized'_annihilator_commutivity

namespace IsLocalizedModule

variable {R M S_M : Type*} (S_R : Type*) [CommSemiring R] [CommSemiring S_R] [Algebra R S_R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
include S f

lemma span_eq (s : Set M) (t : S) : span S_R ((fun m ↦ mk' f m t) '' s) = span S_R (f '' s) := by
  ext x
  constructor
  all_goals intro h
  · induction' h using span_induction with a ains a b _ _ ha hb u a _ ha
    · rcases ains with ⟨m, hm, hmk⟩
      dsimp at hmk
      rw [← hmk, ← mk'_right_smul_mk'_left S_R]
      exact smul_mem _ _ <| mem_span.mpr fun p hsub ↦ hsub <| Set.mem_image_of_mem f hm
    · simp only [Submodule.zero_mem]
    · exact add_mem ha hb
    · exact smul_mem _ _ ha
  · induction' h using span_induction with a ains a b _ _ ha hb u a _ ha
    · rcases ains with ⟨m, hm, hmk⟩
      rw [← hmk, ← mk'_cancel' f m t]
      exact smul_of_tower_mem _ _<| mem_span.mpr fun p hsub ↦ hsub <|
        Set.mem_image_of_mem (fun m ↦ mk' f m t) hm
    · simp only [Submodule.zero_mem]
    · exact add_mem ha hb
    · exact smul_mem _ _ ha

lemma span_singleton_eq (m : M) (s : S) : span S_R {mk' f m s} = span S_R {f m} := by
  have := Set.image_singleton ▸ Set.image_singleton ▸ IsLocalizedModule.span_eq S_R S f {m} s
  exact this

lemma annihilator_span_singleton (m : M) :
    (span S_R {f m}).annihilator = Ideal.map (algebraMap R S_R) (span R {m}).annihilator := by
  ext u
  rw [mem_annihilator_span_singleton]
  constructor
  all_goals intro h
  · rcases IsLocalization.mk'_surjective S u with ⟨r, s, hmk⟩
    rw [← hmk, ← mk'_one S, mk'_smul_mk', mk'_eq_zero'] at h
    rcases h with ⟨w, hw⟩
    rw [← IsLocalization.mk'_cancel _ _ w, mul_comm, IsLocalization.mk'_eq_mul_mk'_one] at hmk
    have hin : w • r ∈ (annihilator (span R {m})) := by
      rw [mem_annihilator_span_singleton, smul_assoc, hw]
    apply Ideal.mem_map_of_mem (algebraMap R S_R) at hin
    rw [Submonoid.smul_def, smul_eq_mul] at hin
    rw [← hmk]
    exact Ideal.mul_mem_right _ _ hin
  · induction' h using span_induction with a hain a b _ _ ha hb x a _ ha
    · rcases hain with ⟨r, hr, hmk⟩
      rw [SetLike.mem_coe, mem_annihilator_span_singleton] at hr
      rw [← hmk, algebraMap_smul, ← map_smul, hr, map_zero]
    · rw [zero_smul]
    · rw [add_smul, ha, hb, zero_add]
    · rw [smul_assoc, ha, smul_zero]

end IsLocalizedModule

namespace Submodule

variable {R M S_M : Type*} (S_R : Type*) [CommRing R] [CommRing S_R] [Algebra R S_R]
    [AddCommGroup M] [Module R M] [AddCommGroup S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
    (p q : Submodule R M)
include S f

lemma annihilator_localized'_sup_of_commute
    (hp : (localized' S_R S f p).annihilator = Ideal.map (algebraMap R S_R) p.annihilator)
    (hq : (localized' S_R S f q).annihilator = Ideal.map (algebraMap R S_R) q.annihilator) :
    (localized' S_R S f (p ⊔ q)).annihilator = Ideal.map (algebraMap R S_R) (p ⊔ q).annihilator :=
  by
  rw [localized'_sup, annihilator_sup, hp, hq, annihilator_sup, IsLocalization.ideal_map_inf _ S]

lemma annihilator_localized'_of_finite (h : p.FG) :
    (localized' S_R S f p).annihilator = Ideal.map (algebraMap R S_R) p.annihilator :=
  fg_induction _ _
  (fun p ↦ (localized' S_R S f p).annihilator = Ideal.map (algebraMap R S_R) p.annihilator)
  (fun m ↦ by dsimp ; rw [localized'_span, Set.image_singleton, annihilator_span_singleton _ S])
  (fun p q hp hq ↦ annihilator_localized'_sup_of_commute S_R S f p q hp hq)
  p h

end Submodule
end localized'_annihilator_commutivity

section NoZeroSMulDivisors_local_property

namespace IsLocalizeModule

variable {R M S_M : Type*} (S_R : Type*) [CommSemiring R] [CommSemiring S_R] [Algebra R S_R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid S_M] [Module R S_M] [Module S_R S_M]
    [IsScalarTower R S_R S_M]
    (S : Submonoid R) [IsLocalization S S_R]
    (f : M →ₗ[R] S_M) [IsLocalizedModule S f]
include S f

lemma noZeroSMulDivisors [h : NoZeroSMulDivisors R M] :
    NoZeroSMulDivisors S_R S_M :=by
  rw [noZeroSMulDivisors_iff_annihilator_singleton_eq_bot] at h ⊢
  intro x hx
  rcases mk'_surjective S f x with ⟨⟨m, s⟩, hmk⟩
  dsimp at hmk
  have hm : m ≠ 0 := by
    by_contra hm
    rw [hm, mk'_zero, eq_comm] at hmk
    exact hx hmk
  rw [← hmk, span_singleton_eq, annihilator_span_singleton _ S, h m hm, Ideal.map_bot]

end IsLocalizeModule

namespace LocalizeModule

variable {R : Type*} [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

lemma noZeroSMulDivisors [NoZeroSMulDivisors R M] (S : Submonoid R) :
    NoZeroSMulDivisors (Localization S) (LocalizedModule S M) :=
  IsLocalizeModule.noZeroSMulDivisors _ S (mkLinearMap S M)

end LocalizeModule
namespace LocalizeModule

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

lemma noZeroSMulDivisors_of_localization [NoZeroDivisors R] (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M)) :
    NoZeroSMulDivisors R M := by
  by_cases nontrivial : Nontrivial R
  · haveI : IsDomain R := IsDomain.mk
    exact noZeroSMulDivisors_iff_torsion_eq_bot.mpr <| submodule_eq_bot_of_localization _ <|
      fun J hJ ↦ localized_torsion J.primeCompl M ▸ noZeroSMulDivisors_iff_torsion_eq_bot.mp <|
        h J hJ
  · haveI := not_nontrivial_iff_subsingleton.mp nontrivial
    exact NoZeroSMulDivisors.of_subsingleton

lemma noZeroSMulDivisors_of_localization_iff [NoZeroDivisors R] :
    NoZeroSMulDivisors R M ↔ ∀ (J : Ideal R) (hJ : J.IsMaximal),
    NoZeroSMulDivisors (Localization J.primeCompl) (LocalizedModule J.primeCompl M) :=
  ⟨fun h J _ ↦ LocalizeModule.noZeroSMulDivisors M J.primeCompl,
    noZeroSMulDivisors_of_localization M⟩

end LocalizeModule
namespace LocalizeModule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
(s : Finset R) (spn : Ideal.span (s : Set R) = ⊤)
include spn

lemma noZeroSMulDivisors_of_localization_finitespan [NoZeroDivisors R]
    (hs : 0 ∉ s)
    (h : ∀ r : s, NoZeroSMulDivisors
    (Localization (Submonoid.powers r.1)) (LocalizedModule (Submonoid.powers r.1) M)) :
    NoZeroSMulDivisors R M := by
  by_cases trivial : Nontrivial R
  · haveI : IsDomain R := IsDomain.mk
    exact noZeroSMulDivisors_iff_torsion_eq_bot.mpr <|
      submodule_eq_bot_of_localization_finitespan _ _ spn <|
      fun r ↦ localized_torsion (Submonoid.powers r.1) M ▸ by
        haveI : IsDomain (Localization (Submonoid.powers r.1)) := by
          apply IsLocalization.isDomain_of_le_nonZeroDivisors (M := (Submonoid.powers r.1))
          apply powers_le_nonZeroDivisors_of_noZeroDivisors
          by_contra heq
          exact hs (heq ▸ r.prop)
        exact noZeroSMulDivisors_iff_torsion_eq_bot.mp <| h r
  · haveI := not_nontrivial_iff_subsingleton.mp trivial
    exact NoZeroSMulDivisors.of_subsingleton

end LocalizeModule
end NoZeroSMulDivisors_local_property
