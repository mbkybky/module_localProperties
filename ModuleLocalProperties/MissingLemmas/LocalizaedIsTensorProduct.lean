/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IsTensorProduct

open TensorProduct

section ideal

def wfw {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
  (S : Submonoid R) : (Ideal.map (algebraMap R (Localization S)) I) →ₗ[R]
  (LocalizedModule S M) →ₗ[R] (LocalizedModule S (I ⊗[R] M)) := sorry

example {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
  (S : Submonoid R) : IsTensorProduct (wfw I M S) := by sorry

end ideal

section module

def efwef {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (S : Submonoid R) : (LocalizedModule S M) →ₗ[R] (LocalizedModule S N) →ₗ[R] (LocalizedModule S (M ⊗[R] N)) := sorry

example {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (S : Submonoid R) : IsTensorProduct (efwef M N S) := by sorry

end module

section IsBaseChange

open IsBaseChange

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  {fm : M →ₗ[R] M'} (hm : IsBaseChange S fm)
  {N' : Type*} [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  {fn : N →ₗ[R] N'} (hn : IsBaseChange S fn)
  {P : Type*} [AddCommGroup P] [Module R P] (f : M →ₗ[R] N →ₗ[R] P) (hf : IsTensorProduct f)
  {P' : Type*} [AddCommGroup P'] [Module R P'] [Module S P'] [IsScalarTower R S P']
  (g : P →ₗ[R] P')

variable (fn) in
noncomputable def IsBaseChange.lift' (f : M →ₗ[R] N) : M' →ₗ[S] N' :=
  IsBaseChange.lift hm (fn.comp f)

variable (S) (N) (N') (fn) in
noncomputable def LinearMap.isBaseChangeHom : (M →ₗ[R] N) →ₗ[R] M' →ₗ[S] N' where
  toFun f := hm.lift' fn f
  map_add' f₁ f₂ := sorry
  map_smul' := sorry

noncomputable def IsBaseChange.lift_bilinMap : M' →ₗ[S] N' →ₗ[S] P' :=
  IsBaseChange.lift' hm (LinearMap.isBaseChangeHom S P hn P' g) f

theorem IsBaseChange.iff_isTensorProduct_lift_bilinMap :
  IsBaseChange S g ↔ IsTensorProduct (hm.lift_bilinMap hn f g) := sorry

end IsBaseChange
