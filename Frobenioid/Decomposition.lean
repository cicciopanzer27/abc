/-!
# Frobenius-Multiplicative Decomposition

This module proves the canonical decomposition property of Frobenioids.
-/

import Frobenioid.Basic

namespace Frobenioid

/-- The canonical decomposition theorem -/
theorem canonical_decomposition {F : Type*} [Category F] [Frobenioid F]
    (X Y : F) (φ : X ⟶ Y) :
    ∃! (φ_Frob : X ⟶ Y) (φ_mult : X ⟶ Y),
      φ_Frob ∈ Frobenioid.Frob F ∧ 
      φ_mult ∈ Frobenioid.Mult F ∧ 
      φ = φ_Frob ≫ φ_mult :=
  Frobenioid.decomposition X Y φ

/-- The Frobenius component of a morphism -/
def frobenius_component {F : Type*} [Category F] [Frobenioid F]
    (X Y : F) (φ : X ⟶ Y) : X ⟶ Y :=
  (canonical_decomposition X Y φ).choose

/-- The multiplicative component of a morphism -/
def multiplicative_component {F : Type*} [Category F] [Frobenioid F]
    (X Y : F) (φ : X ⟶ Y) : X ⟶ Y :=
  (canonical_decomposition X Y φ).choose_spec.choose

/-- The decomposition property -/
theorem decomposition_property {F : Type*} [Category F] [Frobenioid F]
    (X Y : F) (φ : X ⟶ Y) :
    φ = frobenius_component X Y φ ≫ multiplicative_component X Y φ :=
  (canonical_decomposition X Y φ).choose_spec.choose_spec.2.2.2

end Frobenioid
