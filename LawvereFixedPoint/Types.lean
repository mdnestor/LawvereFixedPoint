/-

Deriving Cantor's theorem from Lawvere's fixed point theorem

-/

import Mathlib.Logic.Function.Defs
import Mathlib.CategoryTheory.Closed.Types

import LawvereFixedPoint.LawvereFixedPoint

open CategoryTheory Limits

theorem surjective_iff_point_surjective {X Y: Type u} {f: X → Y}: Function.Surjective f ↔ point_surjective (↾f) := by
  apply Iff.intro
  intro h yhom
  let y := (Types.terminalIso.inv ≫ yhom) PUnit.unit
  obtain ⟨x, hx⟩ := h y
  let xhom := Types.terminalIso.hom ≫ homOfElement x
  exists Types.terminalIso.hom ≫ homOfElement x
  sorry
  intro h y
  let yhom := Types.terminalIso.hom ≫ homOfElement y
  obtain ⟨xhom, hx⟩ := h yhom
  exists (Types.terminalIso.inv ≫ xhom) PUnit.unit
  rw [←types_comp_apply (Types.terminalIso.inv ≫ xhom) f, Category.assoc, hx]
  rfl

theorem prop_fixed_point_property_false: ¬ fixed_point_property Prop := by
  simp
  exists Not
  intro h
  sorry

-- Cantor's theorem for types
theorem cantor {X: Type} (f: X → Set X): ¬ Function.Surjective f := by
  let fhom := f
  rw [Set] at fhom
  repeat rw [←CategoryTheory.types_hom] at fhom
  have h1 := lawvere_diagonal_weak fhom prop_fixed_point_property_false
  have h2 := weak_point_surjective_of_point_surjective.mt h1
  have h3 := (Iff.not surjective_iff_point_surjective).mpr h2
  sorry
