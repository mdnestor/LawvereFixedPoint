/-

Lawvere's fixed point theorem for Cartesian closed categories

Some results make use of terminal object, some use a generic object `T`

-/

import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory Limits CartesianClosed

variable {C: Type*}

def fixed_point [CategoryStruct C] {X T: C} (f: X ⟶ X) (x: T ⟶ X): Prop :=
  x ≫ f = x

def t_fixed_point_property [CategoryStruct C] (X T: C): Prop :=
  ∀ f: X ⟶ X, ∃ x: T ⟶ X, fixed_point f x

def t_point_surjective [CategoryStruct C] {X Y: C} (f: X ⟶ Y) (T: C): Prop :=
  ∀ y: T ⟶ Y, ∃ x: T ⟶ X, x ≫ f = y

def fixed_point_property [Category C] [HasTerminal C] (X: C): Prop :=
  t_fixed_point_property X (⊤_ C)

def point_surjective [Category C] [HasTerminal C] {X Y: C} (f: X ⟶ Y): Prop :=
  t_point_surjective f (⊤_ C)

def weak_point_surjective [Category C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} (g: X ⟶ A ⟹ Y): Prop :=
  ∀ f: A ⟶ Y, ∃ x: ⊤_ C ⟶ X, ∀ a: ⊤_ C ⟶ A, a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ g) = a ≫ f

-- if g: X ⟶ A ⟹ Y is point surjective then it is weak point surjective
theorem weak_point_surjective_of_point_surjective [Category C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} {g: X ⟶ A ⟹ Y} (h: point_surjective g): weak_point_surjective g := by
  intro f
  obtain ⟨x, hx⟩ := h (curry ((prod.rightUnitor A).hom ≫ f))
  exists x
  simp [hx]

-- couple useful lemmas
lemma uncurry_decomp [Category C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} (f: X ⟶ A ⟹ Y) (x: ⊤_ C ⟶ X) (a: ⊤_ C ⟶ A): a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ f) = prod.lift a x ≫ uncurry f := by
  simp [uncurry_natural_left]
  repeat rw [←Category.assoc]
  simp [eq_whisker]
  rw [←Category.assoc, terminal.hom_ext (a ≫ terminal.from A), Category.id_comp]

lemma uncurry_decomp_diag [Category C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} (a: ⊤_ C ⟶ A) (g: A ⟶ A ⟹ Y): a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (a ≫ g) = a ≫ diag A ≫ uncurry g := by
    rw [diag, ←Category.assoc a (prod.lift (𝟙 A) (𝟙 A)), prod.comp_lift a (𝟙 A) (𝟙 A), Category.comp_id a]
    exact uncurry_decomp g a a

-- Lawvere's fixed point construction
theorem lawvere_fixed_point [Category C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} {g: A ⟶ A ⟹ Y} {t: Y ⟶ Y} {a : ⊤_ C ⟶ A}
  (h: a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (a ≫ g) = a ≫ diag A ≫ uncurry g ≫ t):
  fixed_point t (a ≫ diag A ≫ uncurry g) := by
  simp [fixed_point, Category.assoc]
  rw [←uncurry_decomp_diag, h]

-- Lawvere's fixed point theorem
theorem lawvere_fixed_point_exists [Category C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} {g: A ⟶ A ⟹ Y} (h: weak_point_surjective g): fixed_point_property Y := by
  intro t
  obtain ⟨a, ha⟩ := h (diag A ≫ uncurry g ≫ t)
  exists a ≫ diag A ≫ uncurry g
  exact lawvere_fixed_point (ha a)

theorem lawvere_diagonal_weak [Category C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} (g: A ⟶ A ⟹ Y) (h: ¬ fixed_point_property Y): ¬ weak_point_surjective g :=
  mt lawvere_fixed_point_exists h

theorem lawvere_diagonal [Category C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} (g: A ⟶ A ⟹ Y) (h: ¬ fixed_point_property Y): ¬ point_surjective g :=
  mt weak_point_surjective_of_point_surjective (lawvere_diagonal_weak g h)

-- Yanofsky's version of Lawvere's fixed point theorem

-- g: X ⨯ A ⟶ Y "represents" f: X ⟶ Y if ∃ a, ∀ x, x ≫ f = (x ⨯ a) ≫ g
def t_representable [Category C] {A X Y: C} [HasBinaryProduct X A] (g: X ⨯ A ⟶ Y) (f: X ⟶ Y) (T: C): Prop :=
  ∃ a: T ⟶ A, ∀ x: T ⟶ X, x ≫ f = (prod.lift x a) ≫ g

def representable [Category C] [HasTerminal C] {A X Y: C} [HasBinaryProduct X A] (g: X ⨯ A ⟶ Y) (f: X ⟶ Y): Prop :=
  t_representable g f (⊤_ C)

-- if g: X ⟶ A ⟹ Y is weak point surjective then for all f, (uncurry g) represents f
theorem representable_of_weak_point_surjective [Category C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} {g: X ⟶ A ⟹ Y} (h: weak_point_surjective g): ∀ f: A ⟶ Y, representable (uncurry g) f := by
  intro f
  obtain ⟨x, hx⟩ := h f
  exists x
  intro a
  rw [←hx a, uncurry_decomp g x a]

-- construction of the fixed point
theorem yanofsky_fixed_point [Category C] {A X Y T: C} [HasBinaryProduct X A]
  {f: X ⨯ A ⟶ Y} {t : Y ⟶ Y} {a : T ⟶ A} {b: X ⟶ A} {b' : A ⟶ X}
  (ha : a ≫ b' ≫ prod.lift (𝟙 X) b ≫ f ≫ t = prod.lift (a ≫ b') a ≫ f)
  (hb : b' ≫ b = 𝟙 A):
  fixed_point t (a ≫ (prod.lift b' (𝟙 A)) ≫ f) := by
  simp [fixed_point]
  calc
    a ≫ prod.lift b' (𝟙 A) ≫ f ≫ t = a ≫ prod.lift b' (b' ≫ b) ≫ f ≫ t := by rw [hb]
                                   _ = a ≫ prod.lift (b' ≫ (𝟙 X)) (b' ≫ b) ≫ f ≫ t := by rw [Category.comp_id]
                                   _ = a ≫ (b' ≫ prod.lift (𝟙 X) b) ≫ f ≫ t := by rw [prod.comp_lift]
                                   _ = a ≫ b' ≫ prod.lift (𝟙 X) b ≫ f ≫ t := by rw [Category.assoc]
                                   _ = prod.lift (a ≫ b') a ≫ f := ha
                                   _ = prod.lift (a ≫ b') (a ≫ (𝟙 A)) ≫ f := by rw [Category.comp_id]
                                   _ = a ≫ prod.lift b' (𝟙 A) ≫ f := by rw [←Category.assoc, prod.comp_lift]

-- Yanofsky's fixed point theorem
theorem yanofsky_fixed_point_exists [Category C] {A X Y T: C} [HasBinaryProduct X A] {b: X ⟶ A} {f: X ⨯ A ⟶ Y}
  (h1: ∀ g: X ⟶ Y, t_representable f g T) (h2: IsSplitEpi b): t_fixed_point_property Y T := by
  intro t
  specialize h1 ((prod.lift (𝟙 X) b) ≫ f ≫ t)
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b', hb⟩ := h2
  exists a ≫ (prod.lift b' (𝟙 A)) ≫ f
  specialize ha (a ≫ b')
  simp at ha
  exact yanofsky_fixed_point ha hb

-- deriving Lawvere's fixed point theorem from Yanofsky's
theorem lawvere_fixed_point.proof2 [Category C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} {g: A ⟶ A ⟹ Y} (h: weak_point_surjective g): fixed_point_property Y :=
  yanofsky_fixed_point_exists (representable_of_weak_point_surjective h) (IsSplitEpi.of_iso (𝟙 A))
