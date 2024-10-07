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

variable {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R)

noncomputable def Map1 :
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S (N →ₗ[R] (M ⊗[R] N)) :=
  LocalizedModule.map' _ <| TensorProduct.mk _ _ _

noncomputable def BiMap : LocalizedModule S M →ₗ[Localization S]
    LocalizedModule S N →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) where
  toFun := fun m => LocalizedMapLift _ <| Map1 _ _ _ m
  map_add' := fun _ _ => by simp only [map_add]
  map_smul' := fun _ _ => by simp only [map_smul, RingHom.id_apply]

noncomputable def Map : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  TensorProduct.lift <| BiMap _ _ _

noncomputable def InvBiMap : M →ₗ[R] N →ₗ[R]
    (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) :=
  LinearMap.mk₂ _ (fun m n => mkLinearMap _ _ m ⊗ₜ mkLinearMap _ _ n)
  fun _ _ _ => by simp only [map_add, add_tmul]
  fun _ _ _ => by simp only [map_smul, smul_tmul']
  fun _ _ _ => by simp only [map_add, tmul_add]
  fun _ _ _ => by simp only [map_smul, tmul_smul]

noncomputable def InvMapbeforeLocalized : M ⊗[R] N →ₗ[R]
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N :=
  TensorProduct.lift <| InvBiMap _ _ _

noncomputable def InvMap : LocalizedModule S (M ⊗[R] N) →ₗ[Localization S]
    (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) :=
  LiftOnLocalization _ <| InvMapbeforeLocalized _ _ _

#check LocalizedModule.lift
#check LocalizedModule.lift_comp
#check LocalizedModule.lift_unique
#check TensorProduct.lift
#check TensorProduct.lift.tmul
#check TensorProduct.lift_compr₂

noncomputable def Eqv : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    ≃ₗ[Localization S] LocalizedModule S (M ⊗[R] N) := by
  refine LinearEquiv.ofLinear (Map _ _ _) (InvMap _ _ _) ?_ ?_
  · ext x

    unfold InvMap LiftOnLocalization LiftOnLocalization' LocalizedModule.lift
    dsimp
    show (Map M N S) (lift' S (InvMapbeforeLocalized M N S) _ x) = x
    unfold InvMapbeforeLocalized InvBiMap

    dsimp
    unfold TensorProduct.lift liftAux lift'
    dsimp

    sorry
  · unfold Map
    rw [← TensorProduct.lift_compr₂]
    suffices (BiMap M N S).compr₂ (InvMap M N S) = mk _ _ _ from by rw [this, TensorProduct.lift_mk]
    ext m n
    simp
    unfold InvMap LiftOnLocalization
    simp
    unfold LiftOnLocalization'
    dsimp
    --have :=
    rw[LocalizedModule.lift_unique S _ _ _ _]
    sorry
    sorry
    sorry
