/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.FieldTheory.PurelyInseparable

namespace separableClosure

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L]

#check IsPurelyInseparable.injective_comp_algebraMap

#check instUniqueAlgHomOfIsPurelyInseparable

#check separableClosure.isPurelyInseparable

theorem restrictNormalHom_injective : Function.Injective
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) (separableClosure K L)) := by
  sorry

noncomputable def restrictNormalEquiv : (L ≃ₐ[K] L) ≃*
    (separableClosure K L) ≃ₐ[K] (separableClosure K L) :=
  MulEquiv.ofBijective _
    ⟨restrictNormalHom_injective K L, AlgEquiv.restrictNormalHom_surjective L⟩

example (e : PowerBasis K (separableClosure K L)) (σ τ : L ≃ₐ[K] L) (h : σ e.gen = τ e.gen) : σ = τ := by
  sorry

example [FiniteDimensional K L] : ∃ x : L, ∀ σ τ : L ≃ₐ[K] L, σ x = τ x → σ = τ := by
  sorry

end separableClosure
