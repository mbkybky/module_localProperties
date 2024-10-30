/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Sihan Su
-/
import ModuleLocalProperties.Defs
import ModuleLocalProperties.MissingLemmas.Range
import ModuleLocalProperties.MissingLemmas.Submodule

open Submodule IsLocalizedModule LocalizedModule Ideal

lemma eq_zero_of_localization_module {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
{x : M} (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), (mkLinearMap J.primeCompl M) x  = 0) :
    x = 0 := by
  rw [← span_singleton_eq_bot (R := R), ← annihilator_eq_top_iff]
  by_contra H
  obtain ⟨m, maxm, lem⟩ := exists_le_maximal _ H
  obtain ⟨s, hs⟩ := (mk'_eq_zero' _ _ ).mp
    ((mk_eq_mk' (1 : m.primeCompl) x) ▸ (mkLinearMap_apply m.primeCompl M x) ▸ (h m maxm))
  exact s.2 (lem ((mem_annihilator_span_singleton x s.1).mpr hs))

lemma module_eq_zero_of_localization {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
(h : ∀ (J : Ideal R) (_ : J.IsMaximal), Subsingleton (LocalizedModule.AtPrime J M)) :
Subsingleton M :=  subsingleton_of_forall_eq 0 fun x ↦ eq_zero_of_localization_module
  fun J maxJ ↦ (@Subsingleton.eq_zero _ _ (h J maxJ) (mk x 1))

lemma submodule_le_of_localization {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (P : Submodule R M) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), localized J.primeCompl N ≤ localized J.primeCompl P) : N ≤ P := by
  by_contra nle
  obtain ⟨n, hn, hp⟩ := Set.not_subset.mp nle
  set I := P.colon (span R {n})
  obtain ⟨m ,maxm, lem⟩ := exists_le_maximal _ ((ne_top_iff_one _).mpr
    fun H ↦ (one_smul R n ▸ hp) (mem_colon_singleton.mp H))
  have mem : (mkLinearMap m.primeCompl M) n ∈ localized m.primeCompl N := by
    simp only [mkLinearMap_apply, mem_localized']
    exact ⟨n, hn, 1, by rw [mk'_one, mkLinearMap_apply]⟩
  apply (h m maxm) at mem
  simp only [mkLinearMap_apply, mem_localized', mk_eq_mk'] at mem
  obtain ⟨p, inp, s, hs⟩ := mem
  obtain ⟨s', eq⟩ := (mk'_eq_mk'_iff _ p n s 1).mp hs
  simp only [one_smul, smul_smul] at eq
  have h1 : (s'.1 * s.1) ∈ I := by
    unfold_let
    have : (s'.1 * s.1) • n = (s' * s) • n := rfl
    rw [Submodule.mem_colon_singleton, this, eq]
    exact smul_mem P (m.primeCompl.subtype s') inp
  exact (s' * s).2 (lem h1)

lemma submodule_eq_of_localization {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
(N : Submodule R M) (P : Submodule R M) (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
localized J.primeCompl N = localized J.primeCompl P) : N = P :=
  eq_of_le_of_le (submodule_le_of_localization _ _ (fun J hJ ↦ le_of_eq (h J hJ)))
  (submodule_le_of_localization _ _ (fun J hJ ↦ le_of_eq (h J hJ).symm))

lemma submodule_eq_bot_of_localization {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (h : ∀ (J : Ideal R) (_ : J.IsMaximal), localized J.primeCompl N = ⊥) :
  N = ⊥ := submodule_eq_of_localization _ _ fun _ _ ↦ by simp only [h, localized_bot]

lemma submodule_eq_top_of_localization {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (h : ∀ (J : Ideal R) (_ : J.IsMaximal), localized J.primeCompl N = ⊤) :
  N = ⊤ := submodule_eq_of_localization _ _ fun _ _ ↦ by simp only [h, localized_top]

lemma exact_of_localization {R M₀ M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₀] [Module R M₀]
[AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
(h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g := by
  simp only [LinearMap.exact_iff] at h ⊢
  apply submodule_eq_of_localization
  intro J hJ
  unfold localized
  rw [LinearMap.localized'_range_eq_range_localizedMap _ (mkLinearMap J.primeCompl M₀),
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ (mkLinearMap J.primeCompl M₂)]
  exact h J hJ

lemma eq_zero_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s, (mkLinearMap (Submonoid.powers r.1) M ) x = 0) : x = 0 := by
  rw [← span_singleton_eq_bot (R := R), ← annihilator_eq_top_iff]
  by_contra! H
  obtain ⟨m, maxm, lem⟩ := exists_le_maximal _ H
  have exr : ∃ r : s, r.1 ∉ m := by
    by_contra! H
    exact maxm.ne_top (top_le_iff.mp (spn ▸ (Ideal.span_le.mpr (Subtype.forall.mp H))))
  obtain ⟨r, nm⟩ := exr
  obtain ⟨s, hs⟩ := (mk'_eq_zero' _ _ ).mp ((mk_eq_mk' (1 : Submonoid.powers r.1) x)
    ▸ (mkLinearMap_apply (Submonoid.powers r.1) M x) ▸ (h r))
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  exact nm (maxm.isPrime.mem_of_pow_mem n (lem ((mem_annihilator_span_singleton x (r.1 ^ n)).mpr
    (hn ▸ hs))))

lemma submodule_le_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (P : Submodule R M) (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s, localized (Submonoid.powers r.1) N ≤ localized (Submonoid.powers r.1) P) : N ≤ P := by
  by_contra nle
  obtain ⟨n, hn, hp⟩ := Set.not_subset.mp nle
  set I := P.colon (span R {n})
  obtain ⟨m ,maxm, lem⟩ := exists_le_maximal _ ((ne_top_iff_one _).mpr
    fun H ↦ (one_smul R n ▸ hp) (mem_colon_singleton.mp H))
  have exr : ∃ r : s, r.1 ∉ m := by
    by_contra! H
    exact maxm.ne_top (top_le_iff.mp (spn ▸ (Ideal.span_le.mpr (Subtype.forall.mp H))))
  obtain ⟨r, nm⟩ := exr
  have mem : (mkLinearMap (Submonoid.powers r.1) M) n ∈ localized (Submonoid.powers r.1) N := by
    simp only [mkLinearMap_apply, mem_localized']
    exact ⟨n, hn, 1, by rw [mk'_one, mkLinearMap_apply]⟩
  apply (h r) at mem
  simp only [mkLinearMap_apply, mem_localized', mk_eq_mk'] at mem
  obtain ⟨p, inp, s, hs⟩ := mem
  obtain ⟨s', eq⟩ := (mk'_eq_mk'_iff _ p n s 1).mp hs
  simp only [one_smul, smul_smul] at eq
  have h1 : (s' * s).1 ∈ I := by
    unfold_let
    have : (s'.1 * s.1) • n = (s' * s) • n := rfl
    rw [Submonoid.coe_mul, Submodule.mem_colon_singleton, this, eq]
    exact smul_mem P ((Submonoid.powers r.1).subtype s') inp
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (s' * s).2
  exact nm (maxm.isPrime.mem_of_pow_mem k (hk ▸ (lem h1)))

lemma submodule_eq_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (P : Submodule R M) (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s, localized (Submonoid.powers r.1) N = localized (Submonoid.powers r.1) P) : N = P :=
  eq_of_le_of_le (submodule_le_of_localization_finitespan _ _ s spn (fun r ↦ le_of_eq (h r)))
  (submodule_le_of_localization_finitespan _ _ s spn (fun r ↦ le_of_eq (h r).symm))

lemma submodule_eq_bot_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (N : Submodule R M) (s : Finset R) (spn : span (s : Set R) = ⊤)
    (h : ∀ r : s, localized (Submonoid.powers r.1) N = ⊥) : N = ⊥ :=
  submodule_eq_of_localization_finitespan _ _ _ spn fun _ ↦ by simp only [h, localized_bot]

lemma submodule_eq_top_of_localization_finitespan {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (s : Finset R) (spn : span (s : Set R) = ⊤) (h : ∀ r : s, localized (Submonoid.powers r.1) N = ⊤) : N = ⊤ := submodule_eq_of_localization_finitespan _ _ _ spn fun _ ↦ by simp only [h, localized_top]

lemma exact_of_localization_finitespan {R M₀ M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] (s : Finset R) (spn : span (s : Set R) = ⊤) (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (h : ∀ r : s, Function.Exact
  ((map (Submonoid.powers r.1) f)) ((map (Submonoid.powers r.1) g))) :
    Function.Exact f g := by
  simp only [LinearMap.exact_iff] at h ⊢
  apply submodule_eq_of_localization_finitespan _ _ _ spn
  intro r
  unfold localized
  rw [LinearMap.localized'_range_eq_range_localizedMap _ (mkLinearMap (Submonoid.powers r.1) M₀),
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ (mkLinearMap (Submonoid.powers r.1) M₂)]
  exact h r
