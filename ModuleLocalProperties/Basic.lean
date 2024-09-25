import Mathlib

open Submodule IsLocalizedModule LocalizedModule

abbrev IsLocalizedModule.AtPrime {R M M': Type*} [CommSemiring R] (J : Ideal R) [J.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M'):=
  IsLocalizedModule J.primeCompl f

abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (J : Ideal R) [J.IsPrime] (M : Type*) [AddCommMonoid M] [Module R M]:=
  LocalizedModule J.primeCompl M

lemma eq_zero_of_localization_module {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
{x : M} (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), (mkLinearMap J.primeCompl M) x  = 0) :
    x = 0 := by
  rw [← span_singleton_eq_bot (R := R), ← annihilator_eq_top_iff]
  by_contra H
  obtain ⟨m, maxm, lem⟩ := Ideal.exists_le_maximal _ H
  obtain ⟨s, hs⟩ := (mk'_eq_zero' _ _ ).mp
    ((mk_eq_mk' (1 : m.primeCompl) x) ▸ (mkLinearMap_apply m.primeCompl M x) ▸ (h m maxm))
  exact s.2 (lem ((mem_annihilator_span_singleton x s.1).mpr hs))

lemma module_eq_zero_of_localization {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
(h : ∀ (J : Ideal R) (_ : J.IsMaximal), Subsingleton (LocalizedModule.AtPrime J M)) :
Subsingleton M :=  subsingleton_of_forall_eq 0 fun x ↦ eq_zero_of_localization_module
  fun J maxJ ↦ (@Subsingleton.eq_zero _ _ (h J maxJ) (LocalizedModule.mk x 1))

lemma submodule_le_of_localization {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (P : Submodule R M) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Submodule.localized J.primeCompl N ≤ Submodule.localized J.primeCompl P) : N ≤ P := by
  by_contra nle
  obtain ⟨n, hn, hp⟩ := Set.not_subset.mp nle
  set I : Ideal R := {
    carrier := {x : R | x • n ∈ P}
    add_mem' := by
      intro a b ha hb
      exact (Set.mem_setOf_eq) ▸ (add_smul a b n).symm ▸ (Submodule.add_mem P ha hb)
    zero_mem' := by simp only [Set.mem_setOf_eq, zero_smul, Submodule.zero_mem]
    smul_mem' := by
      intro c x hx
      rw [smul_eq_mul, Set.mem_setOf_eq, ← smul_smul]
      exact smul_mem P c hx
  }
  have : I ≠ ⊤ := by
    apply (Ideal.ne_top_iff_one _).mpr
    by_contra! H
    unfold_let at H
    rw [mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, one_smul] at H
    exact hp H
  obtain ⟨m ,maxm, lem⟩ := Ideal.exists_le_maximal _ this
  obtain H := h m maxm
  have mem : (mkLinearMap m.primeCompl M) n ∈ localized m.primeCompl N := by
    simp only [mkLinearMap_apply, Submodule.mem_localized']
    exact ⟨n, hn, 1, by rw [mk'_one, mkLinearMap_apply]⟩
  apply H at mem
  simp only [mkLinearMap_apply, Submodule.mem_localized', mk_eq_mk'] at mem
  obtain ⟨p, inp, s, hs⟩ := mem
  obtain ⟨s', eq⟩ := (IsLocalizedModule.mk'_eq_mk'_iff _ p n s 1).mp hs
  simp only [one_smul, smul_smul] at eq
  have h1 : (s' * s).1 ∈ I := by
    unfold_let
    have : (s'.1 * s.1) • n = (s' * s) • n := rfl
    rw [Submonoid.coe_mul, mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, this, eq]
    exact smul_mem P (m.primeCompl.subtype s') inp
  exact (s' * s).2 (lem h1)

lemma submodule_eq_of_localization {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
(N : Submodule R M) (P : Submodule R M) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
Submodule.localized J.primeCompl N = Submodule.localized J.primeCompl P) : N = P :=
  eq_of_le_of_le (submodule_le_of_localization _ _ (fun J hJ ↦ le_of_eq (h J hJ)))
  (submodule_le_of_localization _ _ (fun J hJ ↦ le_of_eq (h J hJ).symm))

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Submonoid R) [IsLocalization p S]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module S Q]
  [IsScalarTower R S Q] (f' : P →ₗ[R] Q) [IsLocalizedModule p f']

lemma LinearMap.localized'_range_eq_range_localizedMap (g : M →ₗ[R] P) :
    Submodule.localized' S p f' (LinearMap.range g) =
      LinearMap.range ((IsLocalizedModule.map p f f' g).extendScalarsOfIsLocalization p S) := by
  ext x
  simp only [Submodule.mem_localized', extendScalarsOfIsLocalization_apply']
  constructor
  · rintro ⟨r, hr, a, ha⟩
    obtain ⟨m, hm⟩ := mem_range.mp hr
    exact ⟨(mk' f m a), by rw [extendScalarsOfIsLocalization_apply', map_mk', hm, ha]⟩
  · intro h
    obtain ⟨n, hn⟩ := mem_range.mp h
    obtain ⟨m, hm⟩ := IsLocalizedModule.surj p f n
    exact ⟨(g m.1), mem_range_self g m.1, m.2, by
      rw [← hn, extendScalarsOfIsLocalization_apply', ← mk'_eq_iff.mpr hm.symm, map_mk']⟩
