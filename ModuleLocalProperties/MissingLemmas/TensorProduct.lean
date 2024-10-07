/-
Copyright (c) 2024 Song Yi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Song Yi
-/
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import ModuleLocalProperties.MissingLemmas.LocalizedModule

open  TensorProduct

#check TensorProduct.mk

variable {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R)

noncomputable def Map1 :
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S (N →ₗ[R] (M ⊗[R] N)) :=
  LocalizedModule.map' _ <| TensorProduct.mk _ _ _

noncomputable def BiMap : LocalizedModule S M →ₗ[Localization S]
    LocalizedModule S N →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) where
  toFun := fun m => LocalizedMapLift _ <| Map1 _ _ _ m
  map_add' := fun _ _ => by simp only [map_add]
  map_smul' := fun r m => by simp only [map_smul, RingHom.id_apply]

noncomputable def Map : (LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N)
    →ₗ[Localization S] LocalizedModule S (M ⊗[R] N) :=
  TensorProduct.lift <| BiMap _ _ _

noncomputable def Eqv {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) :
(LocalizedModule S M) ⊗[Localization S] (LocalizedModule S N) ≃ₗ[Localization S] LocalizedModule S (M ⊗[R] N) := sorry
