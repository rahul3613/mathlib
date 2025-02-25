import category_theory.monoidal.coherence

open category_theory

universes w v u

section bicategory
open_locale bicategory
variables {B : Type u} [bicategory.{w v} B] {a b c d e : B}

example : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by coherence
example : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
 (α_ f g h).inv ≫ (α_ f g h).hom = 𝟙 (f ≫ g ≫ h) :=
by coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
 f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
 (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i :=
by coherence
example (f : a ⟶ b) (g : b ⟶ c) :
 f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g :=
by coherence
example (f g : a ⟶ a) (η : 𝟙 a ⟶ f) (θ : f ⟶ g) (w : false) :
 (λ_ (𝟙 a)).hom ≫ η ≫ 𝟙 f ≫ θ = (ρ_ (𝟙 a)).hom ≫ η ≫ θ :=
by coherence

example (f₁ : a ⟶ b) (g₁ : b ⟶ a) (f₂ : b ⟶ c) (g₂ : c ⟶ b) :
 (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
 𝟙 a ◁ (α_ (𝟙 a) f₁ f₂).inv ≫
 𝟙 a ◁ ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ f₂ ≫
 𝟙 a ◁ (α_ f₁ (𝟙 b) f₂).hom ≫
 (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
 ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ (𝟙 b ≫ f₂) ≫
 (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
 f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
 f₁ ◁ (α_ (𝟙 b) f₂ (𝟙 c)).inv ≫
 f₁ ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ▷ 𝟙 c ≫
 (f₁ ◁ (α_ f₂ (𝟙 c) (𝟙 c)).hom) ≫
 (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv =
 ((λ_ (𝟙 a)).hom ▷ (f₁ ≫ f₂) ≫ (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv) ≫
 (f₁ ≫ f₂) ◁ (λ_ (𝟙 c)).inv :=
by coherence

end bicategory

section monoidal
variables {C : Type u} [category.{v} C] [monoidal_category C]

example : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by coherence
example : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by coherence
example (X Y Z : C) : (α_ X Y Z).inv ≫ (α_ X Y Z).hom = 𝟙 (X ⊗ Y ⊗ Z) := by coherence
example (X Y Z W : C) :
 (𝟙 X ⊗ (α_ Y Z W).hom) ≫ (α_ X Y (Z ⊗ W)).inv ≫ (α_ (X ⊗ Y) Z W).inv =
 (α_ X (Y ⊗ Z) W).inv ≫ ((α_ X Y Z).inv ⊗ 𝟙 W) :=
by coherence
example (X Y : C) :
 (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y :=
by coherence
example (X Y : C) (f : 𝟙_ C ⟶ X) (g : X ⟶ Y) (w : false) :
 (λ_ (𝟙_ C)).hom ≫ f ≫ 𝟙 X ≫ g = (ρ_ (𝟙_ C)).hom ≫ f ≫ g :=
by coherence

example (X₁ Y₁ X₂ Y₂ : C) :
 (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
 (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) ≫
 (𝟙 (𝟙_ C) ⊗ (λ_ _).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 X₂) ≫
 (𝟙 (𝟙_ C) ⊗ (α_ X₁ (𝟙_ C) X₂).hom) ≫
 (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).inv ≫
 ((λ_ X₁).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 (𝟙_ C ⊗ X₂)) ≫
 (α_ X₁ (𝟙_ C) (𝟙_ C ⊗ X₂)).hom ≫
 (𝟙 X₁ ⊗ 𝟙 (𝟙_ C) ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv) ≫
 (𝟙 X₁ ⊗ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫
 (𝟙 X₁ ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv ⊗ 𝟙 (𝟙_ C)) ≫
 (𝟙 X₁ ⊗ (α_ X₂ (𝟙_ C) (𝟙_ C)).hom) ≫
 (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).inv =
 (((λ_ (𝟙_ C)).hom ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom ≫ (ρ_ (X₁ ⊗ X₂)).inv) ≫
 (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) :=
by coherence

end monoidal

