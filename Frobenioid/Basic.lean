/-!
# Frobenioid Category: Basic Definitions

This module defines the basic structure of Frobenioids, following Mochizuki's framework.

A Frobenioid is a category equipped with:
- A degree functor: `deg : F → ℤ`
- Frobenius morphisms: `Frob(F)`
- Multiplicative morphisms: `F^×`
- Canonical decomposition: every morphism factors uniquely as Frobenius ∘ multiplicative
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.Basic

namespace Frobenioid

/-- A Frobenioid is a category with additional structure -/
class Frobenioid (F : Type u) [Category.{v} F] where
  /-- The degree functor from the Frobenioid to integers -/
  deg : F → ℤ
  /-- The class of Frobenius morphisms -/
  Frob : Set (∀ X Y : F, (X ⟶ Y))
  /-- The class of multiplicative morphisms -/
  Mult : Set (∀ X Y : F, (X ⟶ Y))
  /-- Every morphism admits a unique Frobenius-multiplicative decomposition -/
  decomposition : ∀ (X Y : F) (φ : X ⟶ Y),
    ∃! (φ_Frob : X ⟶ Y) (φ_mult : X ⟶ Y),
      φ_Frob ∈ Frob ∧ φ_mult ∈ Mult ∧ φ = φ_Frob ≫ φ_mult

/-- A local Frobenioid associated to a local field -/
structure LocalFrobenioid (K : Type*) [Field K] where
  /-- Objects are fractional ideals -/
  objects : Type*
  /-- Morphisms preserve ideals -/
  morphisms : objects → objects → Type*
  /-- Uniformizer of the local field -/
  uniformizer : K
  /-- Ring of integers -/
  ringOfIntegers : Subring K

/-- A global Frobenioid associated to a number field -/
structure GlobalFrobenioid (K : Type*) [Field K] where
  /-- Local Frobenioids at each place -/
  localFrobenioids : Type*
  /-- Product structure -/
  product : localFrobenioids → Type*

end Frobenioid
