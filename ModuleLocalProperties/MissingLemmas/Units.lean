/-
Copyright (c) 2024 Yi Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Song
-/

import Mathlib.Algebra.Group.Units

open IsUnit

lemma unit_inv_eq_of_left' [Monoid M] {a b : M} {isunita : IsUnit a} (isunitb : IsUnit b)
    (left : b * a = 1) : isunita.unit⁻¹ = isunitb.unit := by
  have : (isunitb.unit * isunita.unit).val = 1 := left
  symm
  rw[eq_inv_iff_mul_eq_one, ← Units.eq_iff, this, Units.val_one]

lemma unit_inv_eq_of_left [Monoid M] {a b : M} {isunita : IsUnit a} (isunitb : IsUnit b)
    (left : b * a = 1) : isunita.unit⁻¹.val = b := by
  rw[unit_inv_eq_of_left' isunitb left, unit_spec]

lemma unit_inv_eq_of_right' [Monoid M] {a b : M} {isunita : IsUnit a} (isunitb : IsUnit b)
    (right : a * b = 1) : isunita.unit⁻¹ = isunitb.unit := by
  have : (isunita.unit * isunitb.unit).val = 1 := right
  rw[inv_eq_iff_mul_eq_one, ← Units.eq_iff, this, Units.val_one]

lemma unit_inv_eq_of_right [Monoid M] {a b : M} {isunita : IsUnit a} (isunitb : IsUnit b)
    (right : a * b = 1) : isunita.unit⁻¹.val = b := by
  rw[unit_inv_eq_of_right' isunitb right, unit_spec]

lemma unit_inv_eq_of_both [Monoid M] {a b : M} {isunita : IsUnit a} (left : b * a = 1)
    (right : a * b = 1)  : isunita.unit⁻¹.val = b :=
  unit_inv_eq_of_right (isUnit_iff_exists.mpr ⟨a, left, right⟩) right

lemma unit_inv_eq_iff [Monoid M] {a b : M} (h : IsUnit a) :
    h.unit⁻¹.val = b ↔ b * a = 1 ∧ a * b = 1 :=
  ⟨fun h1 => h1.symm ▸ ⟨val_inv_mul h, mul_val_inv h⟩, fun ⟨h1, h2⟩ => unit_inv_eq_of_both h1 h2⟩
