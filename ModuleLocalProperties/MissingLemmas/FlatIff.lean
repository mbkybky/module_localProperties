/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct

universe u v

open LinearMap Submodule TensorProduct DirectSum Module

theorem Module.Flat.iff_isTensorProduct_lift_injective (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] :  Module.Flat R M ↔ ∀ (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R N]
    (f : I →ₗ[R] M →ₗ[R] N) (h : IsTensorProduct f),
    Function.Injective (IsTensorProduct.lift h ((lsmul R M).comp I.subtype)) := sorry

namespace Module.Flat

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

theorem iff_linearEquiv (R : Type*) [CommRing R] (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ => of_linearEquiv R M N e.symm, fun _ => of_linearEquiv R N M e⟩

/-- Drop `[Small.{v, u} R]` assumption in `iff_rTensor_preserves_injective_linearMap`. -/
theorem iff_rTensor_preserves_injective_linearMap' : Flat R M ↔
    ∀ ⦃N N' : Type max u v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) := by
  refine (iff_linearEquiv R M (ULift.{u} M) ULift.moduleEquiv.symm).trans <|
    iff_characterModule_injective.trans <|
      (injective_characterModule_iff_rTensor_preserves_injective_linearMap R (ULift.{u} M)).trans <|
        forall₅_congr <| fun N N' _ _ _ => forall₃_congr (fun _ f _ => ?_)
  let frmu := f.rTensor (ULift.{u, v} M)
  let frm := f.rTensor M
  let emn := TensorProduct.congr (N := ULift.{u} M) (LinearEquiv.refl R N) ULift.moduleEquiv
  let emn' := TensorProduct.congr (N := ULift.{u} M) (LinearEquiv.refl R N') ULift.moduleEquiv
  have h : emn'.toLinearMap.comp frmu = frm.comp emn.toLinearMap := TensorProduct.ext rfl
  apply (EmbeddingLike.comp_injective frmu emn').symm.trans
  apply Iff.trans (Eq.to_iff (congrArg Function.Injective _)) (EquivLike.injective_comp emn frm)
  ext x
  exact congrFun (congrArg DFunLike.coe h) x

/-- Drop `[Small.{v, u} R]` assumption in `iff_lTensor_preserves_injective_linearMap`. -/
theorem iff_lTensor_preserves_injective_linearMap' : Flat R M ↔
    ∀ ⦃N N' : Type max u v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

end Module.Flat
