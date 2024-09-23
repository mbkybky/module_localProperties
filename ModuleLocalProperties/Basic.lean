import Mathlib

open Submodule IsLocalizedModule LocalizedModule
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
(h : ∀ (J : Ideal R) (_ : J.IsMaximal), Subsingleton (LocalizedModule J.primeCompl M)) :
Subsingleton M :=  subsingleton_of_forall_eq 0 fun x ↦ eq_zero_of_localization_module
  fun J maxJ ↦ (@Subsingleton.eq_zero _ _ (h J maxJ) (LocalizedModule.mk x 1))
