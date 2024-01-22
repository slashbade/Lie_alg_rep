import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.DirectSum.Decomposition

import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.FiniteDimensional

import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic

variable {R : Type u} {L : Type v} {V : Type w}

#check LieAlgebra.IsSemisimple
#check Matrix.trace

open LinearMap

section

variable (K : Type*) [CommRing K]
  (L : Type*) [LieRing L] [LieAlgebra K L]
  (V : Type*) [AddCommGroup V] [Module K V]

abbrev Representation :=
  L →ₗ⁅K⁆ V →ₗ[K] V

end

section GeneralLinear

variable (K : Type*) [CommRing K]
  (L : Type*) [LieRing L] [LieAlgebra K L]
  (V : Type*) [AddCommGroup V] [Module K V]


-- instance : LieRingModule K (V →ₗ[K] V) := LinearMap.instLieRingModule
-- #check LieModule K L (V →ₗ[K] V)

instance : LieRing (V →ₗ[K] V) where
  bracket := fun f g => f ∘ₗ g - g ∘ₗ f
  lie_add := by
    simp [add_comp, comp_add]
    intro x y z; abel;
  add_lie := by
    simp [add_comp, comp_add]
    intro x y z; abel;
  lie_self := by simp
  leibniz_lie := by
    simp [sub_comp, comp_sub, comp_assoc]
    intro x y z; abel;


instance : LieAlgebra K (V →ₗ[K] V) where
  lie_smul := by simp



end GeneralLinear


section kernel

variable {K : Type*} [CommRing K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]
variable (f : V →ₗ[K] V)

end kernel



namespace Representation

variable {K : Type*} [CommRing K]
  {L : Type*} [LieRing L] [LieAlgebra K L]
  {V : Type*} [AddCommGroup V] [Module K V]

variable (φ : Representation K L V)


section Module

def asLieModule (_ : Representation K L V) := V


instance : AddCommGroup (asLieModule φ) := inferInstanceAs <| AddCommGroup V

instance : Module K (asLieModule φ) := inferInstanceAs <| Module K V

def asLieModuleEquiv : V ≃ₗ[K] asLieModule φ := by rfl


instance : LieRingModule L (asLieModule φ) where
  bracket := fun x v => φ x v
  lie_add := by simp
  add_lie := by simp
  leibniz_lie := by
    dsimp; intro x y f;
    rw [LieHom.map_lie]
    simp [Bracket.bracket]

instance : LieModule K L (asLieModule φ) where
  smul_lie := by
    intro k l m
    simp [Bracket.bracket]
  lie_smul := by simp [Bracket.bracket]

variable {φ : Representation K L V}
variable (f : V →ₗ[K] V) (commute : ∀ x : L, f ∘ₗ φ x = φ x ∘ₗ f)

example (k : K) (v : V) : k • (φ.asLieModuleEquiv v) = φ.asLieModuleEquiv (k • v) := by
  rw [LinearEquiv.map_smul]


def kernel : LieSubmodule K L φ.asLieModule where
  carrier := { v | f v = 0 }
  zero_mem' := by simp
  add_mem' := by
    simp; intro x y hx hy; rw [hx, hy]; simp;
  smul_mem' := by
    simp; intro x y hy; rw [hy]; simp;
  lie_mem := by
    simp; intro x y hy;
    simp [Bracket.bracket];
    let hhh := commute x
    have : f (φ x y) = φ x (f y) := by
      rw [ext_iff] at hhh
      exact hhh y
    rw [this, hy]; simp;

@[simp]
theorem mem_kernel (v : φ.asLieModule) : v ∈ φ.kernel f commute ↔ f v = 0 := by
  simp [kernel]


end Module



section Reducibility
variable {K : Type*} [CommRing K]
  {L : Type*} [LieRing L] [LieAlgebra K L]
  {V : Type*} [AddCommGroup V] [Module K V]



variable (φ : Representation K L V)

class IsIrreducible (φ : Representation K L V) : Prop where
  Irreducible : ∀ W : LieSubmodule K L φ.asLieModule, W ≠ ⊥ →  W = ⊤

class IsCompletelyReducible (φ : Representation K L V) : Prop where
  CompletelyReducible : ∀ W : LieSubmodule K L φ.asLieModule, ∃ W' : LieSubmodule K L φ.asLieModule,
    W + W' = ⊤ ∧ W ⊓ W' = ⊥

end Reducibility


end Representation

variable {K : Type*} [Field K] [IsAlgClosed K]
  {L : Type*} [LieRing L] [LieAlgebra K L]
  {V : Type*} [AddCommGroup V] [Module K V]

open Representation

variable {φ : Representation K L V}


variable [FiniteDimensional K (asLieModule φ)] [Nontrivial (asLieModule φ)]

lemma Schur  (h0 : IsIrreducible φ) :
(f : φ.asLieModule →ₗ[K] φ.asLieModule) → (∀ x : L, f ∘ₗ φ x = φ x ∘ₗ f) →
  (∃ (c : K), ∀ v : φ.asLieModule, f v = c • v) := by
  intro f hf
  have : ∃ (c : K), ∃ (v : V), v ≠ 0 ∧ f v = c • v := by
    rcases Module.End.exists_eigenvalue f with ⟨c, hc⟩
    rcases hc.exists_hasEigenvector with ⟨v, hv⟩
    use c; use v; constructor
    . exact hv.right
    . exact hv.apply_eq_smul
  rcases this with ⟨c, ⟨v, hcv⟩⟩
  let f1 := f - c • (@id K φ.asLieModule _ _ _)
  have : f1 v = 0 := by
    simp [f1]; rw [sub_eq_zero]; exact hcv.right;
  have : f1 = 0 := by
    have hf1 : ∀ x : L, f1 ∘ₗ φ x = φ x ∘ₗ f1 := by
      intro x
      simp [f1]
      rw [comp_sub, sub_comp, hf x, comp_smul,smul_comp,id_comp, comp_id]
    have : v ∈ (kernel f1 hf1: LieSubmodule K L φ.asLieModule) := by
      simp [kernel]; exact this
    have : (kernel f1 hf1: LieSubmodule K L φ.asLieModule) ≠ ⊥ := by
      intro h; simp [h] at this;
      rcases hcv.left with a; contradiction;
    have : (kernel f1 hf1: LieSubmodule K L φ.asLieModule) = ⊤ := by
      apply h0.Irreducible; assumption
    apply ext; intro w; rw [zero_apply]
    have : w ∈ (kernel f1 hf1: LieSubmodule K L φ.asLieModule) := by
      simp [this]
    rw [← mem_kernel f1 hf1]
    assumption
  use c; intro w
  apply eq_of_sub_eq_zero
  calc
    f w - c • w = f1 w := by simp [f1]
    _ = 0 := by simp [this]



variable (V : Type*) [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Nontrivial V]

open scoped DirectSum

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {L : Type w} [LieRing L] [LieAlgebra K L]
variable (I : Fin t → LieIdeal K L)

instance : LieAlgebra K (⨁ i, I i) := DirectSum.lieAlgebra fun i => ↥(I i)

#check (⨁ i, I i)
variable (j : Fin t)
#check LieIdeal.killingCompl K L (I j)

theorem killing_compl_ideal_eq_top (I : LieIdeal K L) : (I ⊔ LieIdeal.killingCompl K L I) = ⊤ := by sorry

theorem killing_compl_ideal_eq_top' (I : LieIdeal K L) : (I ⊓ LieIdeal.killingCompl K L I) = ⊥ := by sorry

theorem decomp_of_semisimple (hsemisimple : LieAlgebra.IsSemisimple K L) :
  ∃ (I : Fin t → LieIdeal K L),
  (∀ i, LieAlgebra.IsSimple K (I i)) ∧ (Nonempty (DirectSum.Decomposition I)) := by sorry



def Trace (x : V →ₗ[K] V) : ℝ := sorry


lemma triv_1dim_of_semisimplicity (φ : Representation K L V)
  (hsemisimple : LieAlgebra.IsSemisimple K L) :
  ∀ x : L, (Trace V) (φ x) = 0 := by sorry


variable {K : Type*} [CommRing K]
  {L : Type*} [LieRing L] [LieAlgebra K L]
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V]

theorem Weyl (ϕ : Representation K L V) (hsemisimple : LieAlgebra.IsSemisimple K L) :
  Representation.IsCompletelyReducible ϕ := by sorry
