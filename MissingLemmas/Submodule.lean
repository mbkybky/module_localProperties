/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Sihan Su
-/
import Mathlib.Algebra.Module.Submodule.Localization

open Submodule IsLocalizedModule LocalizedModule Ideal

lemma localized'_bot {R : Type u} (S : Type u') {M : Type v} {N : Type v'} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N] (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f] : Submodule.localized' S p f ⊥ = ⊥ := by
  have : ∃ x, x ∈ p := ⟨1, Submonoid.one_mem p⟩
  ext x
  rw[mem_localized']
  simp only [mem_bot, Subtype.exists, exists_eq_left, mk'_zero, exists_prop', nonempty_prop,
    exists_and_right, this, true_and]
  exact eq_comm

lemma localized_bot {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] (p : Submonoid R) : Submodule.localized p (⊥ : Submodule R M) = ⊥ := localized'_bot (Localization p) p (mkLinearMap p M)
