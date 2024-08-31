/-
Magmoidal fixed point theorem

References:
"Substructural fixed-point theorems and the diagonal argument: theme and variations" by Roberts (2021): https://arxiv.org/abs/2110.00239
-/

import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Closed.Cartesian

import LawvereFixedPoint.LawvereFixedPoint

open CategoryTheory Limits CartesianClosed

theorem magmoidal_fixed_point {C: Type u} [Category.{v} C] {A B T : C}
  {H : Functor (C × C) C}
  {δ : NatTrans (𝟭 C) (Functor.diag C ⋙ H)}
  {F : H.obj (A, A) ⟶ B}
  {t : B ⟶ B} {a: T ⟶ A}
  (h : ∀ a' : T ⟶ A, a' ≫ (δ.app A) ≫ F ≫ t = (δ.app T) ≫ (H.map ((a, a') : (T, T) ⟶ (A, A))) ≫ F) :
    ∃ b : T ⟶ B, fixed_point t b := by
  exists a ≫ (δ.app A) ≫ F
  simp [h a]
  have := δ.naturality a
  have hδ: a ≫ δ.app A = δ.app T ≫ H.map ((a, a): (T, T) ⟶ (A, A)) := by simpa
  simp [←Category.assoc, eq_whisker hδ F]

-- Yanofsky variant of the magmoidal fixed point theorem
theorem magmoidal_fixed_point_yanofsky {C: Type u} [Category.{v} C] {A A' B T : C}
  {H : Functor (C × C) C}
  {δ : NatTrans (𝟭 C) (Functor.diag C ⋙ H)}
  {F : H.obj (A, A') ⟶ B}
  {t : B ⟶ B} {a: T ⟶ A} {p: A' ⟶ A}
  (h1 : ∀ a': T ⟶ A', a' ≫ δ.app A' ≫ (H.map ((p, 𝟙 A'): (A', A') ⟶ (A, A'))) ≫ F ≫ t = δ.app T ≫ (H.map ((a, a') : (T, T) ⟶ (A, A'))) ≫ F)
  (h2 : t_point_surjective p T):
    ∃ b: T ⟶ B, fixed_point t b := by
  obtain ⟨l, hl⟩ := h2 a
  exists l ≫ (δ.app A') ≫ (H.map ((p, 𝟙 A'): (A', A') ⟶ (A, A'))) ≫ F
  simp [h1 l]
  have h3 : (H.map ((a, l): (T, T) ⟶ (A, A'))) = (H.map ((l, l): (T, T) ⟶ (A', A'))) ≫ (H.map ((p, 𝟙 A'): (A', A') ⟶ (A, A'))) := by
    simp [←Functor.map_comp, hl]
  have := δ.naturality l
  have h4 : l ≫ (δ.app A') = (δ.app T) ≫ (H.map ((l, l): (T, T) ⟶ (A', A'))) := by simpa
  simp [h3, ←Category.assoc, h4]

-- derive the Magmoidal fixed point theorem from the Yanofsky variant
theorem magmoidal_fixed_point.proof2 {C: Type u} [Category.{v} C] {A B t: C}
  {H: Functor (C × C) C}
  {δ: NatTrans (𝟭 C) (Functor.diag C ⋙ H)}
  {F: H.obj (A, A) ⟶ B}
  {σ: B ⟶ B} {a0: t ⟶ A}
  (h: ∀ a: t ⟶ A, a ≫ (δ.app A) ≫ F ≫ σ = (δ.app t) ≫ (H.map ((a0, a): (t, t) ⟶ (A, A))) ≫ F):
    ∃ b: t ⟶ B, b ≫ σ = b := by
  have h1: ∀ a: t ⟶ A, a ≫ δ.app A ≫ (H.map ((𝟙 A, 𝟙 A): (A, A) ⟶ (A, A))) ≫ F ≫ σ = δ.app t ≫ (H.map ((a0, a): (t, t) ⟶ (A, A))) ≫ F := by
    rw [← CategoryTheory.prod_id]
    have h2: (H.map ((𝟙 A, 𝟙 A): (A, A) ⟶ (A, A))) = 𝟙 (H.obj (A, A)) := by
      rw [← CategoryTheory.prod_id]
      rw [CategoryTheory.Functor.map_id]
    simp [h2]
    exact h
  exact magmoidal_fixed_point_yanofsky h1 (by simp)

-- derive the Lawvere fixed point theorem from the magmoidal fixed point theorem
theorem lawvere_fixed_point.proof3 {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} {g : A ⟶ A ⟹ Y}
  (h : weak_point_surjective g) : fixed_point_property Y := by
  let H : Functor (C × C) C := uncurry.obj prod.functor
  let δ : NatTrans (𝟭 C) (Functor.diag C ⋙ H) := {
    app := fun X => diag X
    naturality := by simp [H]
  }
  let F : H.obj (A, A) ⟶ Y := by
    simp [H]
    exact uncurry g
  intro t
  simp at h
  obtain ⟨a, ha⟩ := h (diag A ≫ F ≫ t)
  have h1: ∀ a' : ⊤_ C ⟶ A, a' ≫ (δ.app A) ≫ F ≫ t = (δ.app (⊤_ C)) ≫ (H.map ((a, a') : (⊤_ C, ⊤_ C) ⟶ (A, A))) ≫ F := by
    intro a'
    simp [H]
    have h2 : prod.lift a a' ≫ F = a' ≫ prod.lift (𝟙 A) (terminal.from A) ≫ CartesianClosed.uncurry (a ≫ g) := by
      simp [F, uncurry_decomp g a a']
      sorry -- why is order flipped ??
    rw [←ha a', h2]
  exact magmoidal_fixed_point h1
