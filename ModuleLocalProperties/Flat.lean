import Mathlib.RingTheory.Flat.Basic

import ModuleLocalProperties.Basic
import ModuleLocalProperties.Finite_presented

open Submodule IsLocalizedModule LocalizedModule Ideal IsLocalization

#check Module.Flat.iff_rTensor_injective'

noncomputable abbrev LocalizedModule.map' {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) := (LocalizedModule.map S f).extendScalarsOfIsLocalization S (Localization S)

lemma inj_of_local {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Function.Injective (map' J.primeCompl f)) : Function.Injective f := by
  refine LinearMap.ker_eq_bot.mp ?_
  sorry

#check Localization.localRingHom
#check LocalizedModule.map
#check IsLocalizedModule.linearEquiv
#check Submodule.subtype
#check LinearMap.ker_eq_bot'

#check IsLocalizedModule.iso
#check IsLocalizedModule

noncomputable def eqv1 {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (S : Submonoid R) (I : Ideal R) : LocalizedModule S (TensorProduct R I M) ≃ₗ[R] TensorProduct (Localization S) (Ideal.map (algebraMap R (Localization S)) I) (LocalizedModule S M) := by
  set f : (TensorProduct R I M) →ₗ[R] TensorProduct (Localization S) (Ideal.map (algebraMap R (Localization S)) I) (LocalizedModule S M) := by

    sorry
  letI : IsLocalizedModule S f (M := (TensorProduct R I M)) (M' := TensorProduct (Localization S) (Ideal.map (algebraMap R (Localization S)) I) (LocalizedModule S M)) := by

    sorry
  exact IsLocalizedModule.iso S f

def eqv2 {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]  (S : Submonoid R) (I : Ideal R) : LocalizedModule S (TensorProduct R R M) ≃ₗ[R] TensorProduct (Localization S) (Localization S) (LocalizedModule S M) := by

  sorry

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_injective' R M).mpr
  intro I
  apply inj_of_local
  intro J maxJ
  have hj := (Module.Flat.iff_rTensor_injective' _ _).mp (h J maxJ) (I.map (algebraMap R (Localization J.primeCompl)))

  set fi := (Submodule.subtype (Ideal.map (algebraMap R (Localization J.primeCompl)) I))
  set f' := LinearMap.rTensor (LocalizedModule.AtPrime J M) fi
  unfold LocalizedModule.AtPrime at f'
  set g := LinearMap.rTensor M (Submodule.subtype I)
  set g' := map' J.primeCompl g
  have : g' = (eqv2 M J.primeCompl I).symm ∘ f' ∘ (eqv1 M J.primeCompl I) := by sorry

  rw [this]
  simp only [EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact hj


#check IsLocalization.map_comap
#check mem_map_algebraMap_iff

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) : Module.Flat R M := by
  apply (Module.Flat.iff_rTensor_injective' R M).mpr
  intro I
  apply inj_of_local
  intro J maxJ
  have hj := (Module.Flat.iff_rTensor_injective' _ _).mp (h J maxJ) (I.map (algebraMap R (Localization J.primeCompl)))
  apply (LinearMap.ker_eq_bot (f := ((LocalizedModule.map _) _))).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro m hm
  apply LinearMap.ker_eq_bot.mpr at hj
  apply LinearMap.ker_eq_bot'.mp at hj
  simp only at hj

  sorry

#check Module.Flat.iff_rTensor_preserves_injective_linearMap

def ev {R : Type*} (N M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) : LocalizedModule S (TensorProduct R N M) ≃ₗ[R] TensorProduct (Localization S) (LocalizedModule S N) (LocalizedModule S M) := by sorry

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), Module.Flat (Localization.AtPrime J) (LocalizedModule.AtPrime J M)) : Module.Flat R M := by

  sorry
