/-
Copyright (c) 2024 Song Yi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Song Yi
-/
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import ModuleLocalProperties.MissingLemmas.LocalizedModule

open  TensorProduct LocalizedModule

section BilinearMapLift

namespace LocalizedModule

variable {R : Type*} {M N P : Type*} [CommSemiring R] (S : Submonoid R) [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P]
    [Module R P] (f : M →ₗ[R] N →ₗ[R] P)

noncomputable def BilinearMap : LocalizedModule S M →ₗ[Localization S]
    LocalizedModule S N →ₗ[Localization S] LocalizedModule S P :=
  LocalizedMapLift S ∘ₗ (map' (M := M) (N := N →ₗ[R] P) S f)

lemma BilinearMap_mk (m : M) (n : N) (s t : S) :
    BilinearMap S f (mk m s) (mk n t) = mk (f m n) (s * t) :=by
  unfold BilinearMap
  rw [LinearMap.coe_comp, Function.comp_apply, map'_mk, LocalizedMapLift_mk]

end LocalizedModule

section LocalizedModule_TensorProduct_Exchange

namespace LocalizedModule

variable {R : Type*} {M N : Type*} [CommSemiring R] (S : Submonoid R) [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

noncomputable def TensorProductBilinearMap : (LocalizedModule S M) →ₗ[Localization S]
    (LocalizedModule S N) →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  BilinearMap S <| TensorProduct.mk R M N

lemma TensorProductBilinearMap_mk (m : M) (n : N) (s t : S) :
    TensorProductBilinearMap S (mk m s) (mk n t) = mk (m ⊗ₜ n) (s * t) :=
  BilinearMap_mk S (TensorProduct.mk R M N) m n s t

noncomputable def TensorProductMap : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  TensorProduct.lift <| TensorProductBilinearMap S

lemma TensorProductMap_mk (m : M) (n : N) (s t : S) :
    TensorProductMap S ((mk m s) ⊗ₜ (mk n t)) = mk (m ⊗ₜ n) (s * t) :=
  TensorProductBilinearMap_mk S m n s t

noncomputable def InvTensorProductBilinearMap : M →ₗ[R] N →ₗ[R]
    (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) :=
  LinearMap.mk₂ _ (fun m n => mkLinearMap S M m ⊗ₜ mkLinearMap S N n)
  fun _ _ _ => by simp only [map_add, add_tmul]
  fun _ _ _ => by simp only [map_smul, smul_tmul']
  fun _ _ _ => by simp only [map_add, tmul_add]
  fun _ _ _ => by simp only [map_smul, tmul_smul]

lemma InvTensorProductBilinearMap_apply (m : M) (n : N) :
    InvTensorProductBilinearMap S m n = ((mk m 1) ⊗ₜ (mk n 1)) := rfl

noncomputable def InvTensorProductMap' : M ⊗[R] N →ₗ[R]
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N :=
  TensorProduct.lift <| InvTensorProductBilinearMap S

lemma InvTensorProductMap'_apply (m : M) (n : N) :
    InvTensorProductMap' S (m ⊗ₜ n) = ((mk m 1) ⊗ₜ (mk n 1)) :=
  InvTensorProductBilinearMap_apply S m n

noncomputable def InvTensorProductMap : LocalizedModule S (M ⊗[R] N) →ₗ[Localization S]
    (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) :=
  LiftOnLocalizationModule _ <| InvTensorProductMap' S

lemma InvTensorProductMap_apply (m : M) (n : N) (s : S) :
    InvTensorProductMap S (mk (m ⊗ₜ n) s) = Localization.mk 1 s • ((mk m 1) ⊗ₜ (mk n 1)) := by
  unfold InvTensorProductMap
  rw [LiftOnLocalizationModule_mk, InvTensorProductMap'_apply]

lemma InvTensorProductMap_apply' (m : M) (n : N) (s t : S) :
    InvTensorProductMap S (mk (m ⊗ₜ n) (s * t)) = ((mk m s) ⊗ₜ (mk n t)) := by
  rw [InvTensorProductMap_apply]
  symm
  rw [← mk_right_smul_mk_den_one, ← mk_right_smul_mk_den_one (s := t), TensorProduct.smul_tmul_smul,
    Localization.mk_mul, one_mul]

lemma TensorProductMap_rightInv :
    TensorProductMap S ∘ₗ (InvTensorProductMap S (M := M) (N := N)) = LinearMap.id := by
  unfold TensorProductMap
  ext x
  induction' x with y s
  dsimp
  induction' y with m n m n hm hn
  · simp only [zero_mk, map_zero]
  · rw [InvTensorProductMap_apply, map_smul, TensorProduct.lift.tmul, TensorProductBilinearMap_mk,
      one_mul, mk_right_smul_mk_den_one]
  · rw [mk_add_mk_right, map_add, map_add, hm, hn]

lemma TensorProductMap_leftInv :
    InvTensorProductMap S ∘ₗ (TensorProductMap S (M := M) (N := N)) = LinearMap.id :=by
  unfold TensorProductMap
  ext x y
  dsimp
  induction' x with m s
  induction' y with n t
  rw [TensorProductBilinearMap_mk, InvTensorProductMap_apply']

noncomputable def TensorProductEquiv : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    ≃ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  LinearEquiv.ofLinear (TensorProductMap S) (InvTensorProductMap S) (TensorProductMap_rightInv S)
  (TensorProductMap_leftInv S)

lemma TensorProductEquiv_apply (m : M) (n : N) (s t : S) :
    TensorProductEquiv S ((mk m s) ⊗ₜ (mk n t)) = mk (m ⊗ₜ n) (s * t) :=
  TensorProductMap_mk S m n s t

lemma TensorProductEquiv_symm_apply (m : M) (n : N) (s : S) :
    (TensorProductEquiv S).symm (mk (m ⊗ₜ n) s) = Localization.mk 1 s • ((mk m 1) ⊗ₜ (mk n 1)) :=
  InvTensorProductMap_apply S m n s

end LocalizedModule
