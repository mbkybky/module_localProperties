/-
Copyright (c) 2024 Song Yi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Song Yi
-/
import Mathlib.Algebra.Module.LocalizedModule

import ModuleLocalProperties.MissingLemmas.LocalizedModule

open  TensorProduct LocalizedModule

section BilinearMapLift

namespace LocalizedModule

variable {R : Type*} {M N P : Type*} [CommSemiring R] (S : Submonoid R) [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P]
    [Module R P] (f : M →ₗ[R] N →ₗ[R] P)

noncomputable def BilinearMap : LocalizedModule S M →ₗ[Localization S]
    LocalizedModule S N →ₗ[Localization S] LocalizedModule S P :=
  LocalizedMapLift S ∘ₗ (mapfromlift (M := M) (N := N →ₗ[R] P) S f)

lemma BilinearMap_mk (m : M) (n : N) (s t : S) :
    BilinearMap S f (mk m s) (mk n t) = mk (f m n) (s * t) :=by
  unfold BilinearMap
  rw [LinearMap.coe_comp, Function.comp_apply, mapfromlift_mk, LocalizedMapLift_mk]

end LocalizedModule

section LocalizedModule_TensorProduct_Exchange

namespace LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (M N : Type*) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]

noncomputable def TensorProductBilinearMap : (LocalizedModule S M) →ₗ[Localization S]
    (LocalizedModule S N) →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  BilinearMap S <| TensorProduct.mk R M N

lemma TensorProductBilinearMap_mk (m : M) (n : N) (s t : S) :
    TensorProductBilinearMap S M N (mk m s) (mk n t) = mk (m ⊗ₜ n) (s * t) :=
  BilinearMap_mk S (TensorProduct.mk R M N) m n s t

noncomputable def TensorProductMap : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  TensorProduct.lift <| TensorProductBilinearMap S M N

lemma TensorProductMap_mk (m : M) (n : N) (s t : S) :
    TensorProductMap S M N ((mk m s) ⊗ₜ (mk n t)) = mk (m ⊗ₜ n) (s * t) :=
  TensorProductBilinearMap_mk S M N m n s t

noncomputable def InvTensorProductBilinearMap : M →ₗ[R] N →ₗ[R]
    (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) :=
  LinearMap.mk₂ _ (fun m n => mkLinearMap S M m ⊗ₜ mkLinearMap S N n)
  fun _ _ _ => by simp only [map_add, add_tmul]
  fun _ _ _ => by simp only [map_smul, smul_tmul']
  fun _ _ _ => by simp only [map_add, tmul_add]
  fun _ _ _ => by simp only [map_smul, tmul_smul]

lemma InvTensorProductBilinearMap_apply (m : M) (n : N) :
    InvTensorProductBilinearMap S M N m n = ((mk m 1) ⊗ₜ (mk n 1)) := rfl

noncomputable def InvTensorProductMap' : M ⊗[R] N →ₗ[R]
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N :=
  TensorProduct.lift <| InvTensorProductBilinearMap S M N

lemma InvTensorProductMap'_apply (m : M) (n : N) :
    InvTensorProductMap' S M N (m ⊗ₜ n) = ((mk m 1) ⊗ₜ (mk n 1)) :=
  InvTensorProductBilinearMap_apply S M N m n

noncomputable def InvTensorProductMap : LocalizedModule S (M ⊗[R] N) →ₗ[Localization S]
    (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) :=
  LiftOnLocalizationModule _ <| InvTensorProductMap' S M N

lemma InvTensorProductMap_apply (m : M) (n : N) (s : S) :
    InvTensorProductMap S M N (mk (m ⊗ₜ n) s) = Localization.mk 1 s • ((mk m 1) ⊗ₜ (mk n 1)) := by
  unfold InvTensorProductMap
  rw [LiftOnLocalizationModule_mk, InvTensorProductMap'_apply]

lemma InvTensorProductMap_apply' (m : M) (n : N) (s t : S) :
    InvTensorProductMap S M N (mk (m ⊗ₜ n) (s * t)) = ((mk m s) ⊗ₜ (mk n t)) := by
  rw [InvTensorProductMap_apply]
  symm
  rw [← mk_right_smul_mk_left, ← mk_right_smul_mk_left (s := t), TensorProduct.smul_tmul_smul,
    Localization.mk_mul, one_mul]

lemma TensorProductMap_rightInv :
    TensorProductMap S M N ∘ₗ (InvTensorProductMap S M N) = LinearMap.id := by
  ext x
  induction' x with y s
  dsimp
  induction' y with m n m n hm hn
  · rw [zero_mk, map_zero, map_zero]
  · rw [InvTensorProductMap_apply, map_smul, TensorProductMap_mk,
      one_mul, mk_right_smul_mk_left]
  · rw [mk_add_mk_right, map_add, map_add, hm, hn]

lemma TensorProductMap_leftInv :
    InvTensorProductMap S M N ∘ₗ (TensorProductMap S M N) = LinearMap.id := by
  ext u
  induction' u with x y a b ha hb
  · rw [map_zero, map_zero]
  · dsimp
    induction' x with m s
    induction' y with n t
    rw [TensorProductMap_mk, InvTensorProductMap_apply']
  · rw [LinearMap.id_coe, id_eq, map_add] at *
    rw[ha, hb]

noncomputable def TensorProductEquiv : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    ≃ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  LinearEquiv.ofLinear _ _ (TensorProductMap_rightInv S M N)
  (TensorProductMap_leftInv S M N)

lemma TensorProductEquiv_apply (m : M) (n : N) (s t : S) :
    TensorProductEquiv S M N ((mk m s) ⊗ₜ (mk n t)) = mk (m ⊗ₜ n) (s * t) :=
  TensorProductMap_mk S M N m n s t

lemma TensorProductEquiv_symm_apply (m : M) (n : N) (s : S) :
    (TensorProductEquiv S M N).symm (mk (m ⊗ₜ n) s) = Localization.mk 1 s • ((mk m 1) ⊗ₜ (mk n 1)) :=
  InvTensorProductMap_apply S M N m n s

end LocalizedModule
