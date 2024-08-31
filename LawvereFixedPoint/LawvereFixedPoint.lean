/-

Lawvere's fixed point theorem for Cartesian closed categories

-/

import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory Limits CartesianClosed

@[simp]
def t_point_surjective {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) (t : C) : Prop :=
  ∀ y: t ⟶ Y, ∃ x: t ⟶ X, x ≫ f = y

@[simp]
def point_surjective {C: Type u} [Category.{v} C] [HasTerminal C] {X Y: C} (f: X ⟶ Y) : Prop :=
  t_point_surjective f (⊤_ C)

@[simp]
def weak_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} (g : X ⟶ A ⟹ Y) : Prop :=
  ∀ f : A ⟶ Y, ∃ x : ⊤_ C ⟶ X, ∀ a : ⊤_C ⟶ A, a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ g) = a ≫ f

@[simp]
def fixed_point {C : Type u} [Category.{v} C] {X t : C} (f : X ⟶ X) (x : t ⟶ X) : Prop :=
  x ≫ f = x

@[simp]
def t_fixed_point_property {C : Type u} [Category.{v} C] (X t : C) : Prop :=
  ∀ f : X ⟶ X, ∃ x : t ⟶ X, fixed_point f x

@[simp]
def fixed_point_property {C : Type u} [Category.{v} C] [HasTerminal C] (X : C) : Prop :=
  t_fixed_point_property X (⊤_ C)

theorem weak_point_surjective_of_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} {g : X ⟶ A ⟹ Y} (h : point_surjective g) : weak_point_surjective g := by
  intro f
  obtain ⟨x, hx⟩ := h (curry ((prod.rightUnitor A).hom ≫ f))
  exists x
  simp [hx]

lemma uncurry_decomp {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} (f : X ⟶ A ⟹ Y) (x : ⊤_ C ⟶ X) (a : ⊤_ C ⟶ A) : a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ f) = prod.lift a x ≫ uncurry f := by
  simp [uncurry_natural_left]
  repeat rw [←Category.assoc]
  simp [eq_whisker]
  rw [←Category.assoc, terminal.hom_ext (a ≫ terminal.from A), Category.id_comp]

lemma uncurry_decomp_diag {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} (a : ⊤_ C ⟶ A) (g : A ⟶ A ⟹ Y) : a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (a ≫ g) = a ≫ diag A ≫ uncurry g := by
    rw [diag, ←Category.assoc a (prod.lift (𝟙 A) (𝟙 A)), prod.comp_lift a (𝟙 A) (𝟙 A), Category.comp_id a]
    exact uncurry_decomp g a a

-- Lawvere's fixed point theorem
theorem lawvere_fixed_point {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} {g : A ⟶ A ⟹ Y} (h : weak_point_surjective g) : fixed_point_property Y := by
  intro t
  obtain ⟨x, hx⟩ := h (diag A ≫ uncurry g ≫ t)
  exists x ≫ diag A ≫ uncurry g
  simp [Category.assoc]
  rw [←uncurry_decomp_diag, hx x]

theorem lawvere_diagonal_weak {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} (g : A ⟶ A ⟹ Y) (h : ¬ fixed_point_property Y) : ¬ weak_point_surjective g :=
  mt lawvere_fixed_point h

theorem lawvere_diagonal {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} (g : A ⟶ A ⟹ Y) (h : ¬ fixed_point_property Y) : ¬ point_surjective g :=
  mt weak_point_surjective_of_point_surjective (lawvere_diagonal_weak g h)

def representable {C : Type u} [Category.{v} C] [HasTerminal C] {A X Y : C} [HasBinaryProduct X A] (g : X ⨯ A ⟶ Y) (f : X ⟶ Y) : Prop :=
  ∃ a : ⊤_C ⟶ A, ∀ x : ⊤_C ⟶ X, x ≫ f = (prod.lift x a) ≫ g

theorem representable_of_weak_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} {f : X ⟶ A ⟹ Y} (h : weak_point_surjective f) : ∀ g : A ⟶ Y, representable (uncurry f) g := by
  intro g
  obtain ⟨x, hx⟩ := h g
  exists x
  intro a
  specialize hx a
  rw [←hx, uncurry_decomp f x a]

-- Yanofsky's version of Lawvere's fixed point theorem
theorem yanofsky_fixed_point {C: Type u} [Category.{v} C] [HasTerminal C] {A X Y : C} [HasBinaryProduct X A] {b : X ⟶ A} {f: X ⨯ A ⟶ Y}
  (h1: ∀ g: X ⟶ Y, representable f g) (h2: IsSplitEpi b): fixed_point_property Y := by
  intro t
  specialize h1 ((prod.lift (𝟙 X) b) ≫ f ≫ t)
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b', hb⟩ := h2
  exists a ≫ (prod.lift b' (𝟙 A)) ≫ f
  simp
  specialize ha (a ≫ b')
  simp at ha
  calc
    a ≫ prod.lift b' (𝟙 A) ≫ f ≫ t = a ≫ prod.lift b' (b' ≫ b) ≫ f ≫ t := by rw [hb]
                                   _ = a ≫ prod.lift (b' ≫ (𝟙 X)) (b' ≫ b) ≫ f ≫ t := by rw [Category.comp_id]
                                   _ = a ≫ (b' ≫ prod.lift (𝟙 X) b) ≫ f ≫ t := by rw [prod.comp_lift]
                                   _ = a ≫ b' ≫ prod.lift (𝟙 X) b ≫ f ≫ t := by rw [Category.assoc]
                                   _ = prod.lift (a ≫ b') a ≫ f := ha
                                   _ = prod.lift (a ≫ b') (a ≫ (𝟙 A)) ≫ f := by rw [Category.comp_id]
                                   _ = a ≫ prod.lift b' (𝟙 A) ≫ f := by rw [←Category.assoc, prod.comp_lift]

-- deriving Lawvere's fixed point theorem from Yanofsky's
theorem lawvere_fixed_point.proof2 {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} {g: A ⟶ A ⟹ Y} (h : weak_point_surjective g) : fixed_point_property Y :=
  yanofsky_fixed_point (representable_of_weak_point_surjective h) (IsSplitEpi.of_iso (𝟙 A))
