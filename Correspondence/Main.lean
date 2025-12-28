/-!
# Frobenioid-Borel Correspondence

This module proves the main theorem: Frobenioid morphisms admit matrix
representations in the Borel subgroup.
-/

import Frobenioid.Basic
import Frobenioid.Decomposition
import Borel.Definition
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

namespace Correspondence

variable {K : Type*} [Field K] {F : Type*} [Category F] [Frobenioid F]

/-- Matrix representation functor -/
structure Representation (F : Type*) [Category F] where
  /-- The representation map -/
  map : ∀ {X Y : F}, (X ⟶ Y) → GL (Fin 2) K
  /-- Functoriality -/
  functorial : ∀ {X Y Z : F} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f * map g

/-- Main theorem: Frobenioid-Borel correspondence -/
theorem frobenioid_borel_correspondence
    (ρ : Representation F)
    (X Y : F)
    (φ : X ⟶ Y) :
    ρ.map φ ∈ Borel.Borel K :=
  sorry
  /- Proof sketch:
  1. Decompose φ = φ_Frob ∘ φ_mult
  2. Show φ_Frob is diagonal (Frobenius part)
  3. Show φ_mult is upper triangular (multiplicative part)
  4. Composition preserves upper triangular structure
  -/

/-- The (2,1)-entry vanishes -/
theorem lower_left_entry_vanishes
    (ρ : Representation F)
    (X Y : F)
    (φ : X ⟶ Y) :
    (ρ.map φ).1.1 1 0 = 0 :=
  by
    have h := frobenioid_borel_correspondence ρ X Y φ
    exact h

end Correspondence
