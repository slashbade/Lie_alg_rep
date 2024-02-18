import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Quotient

import Mathlib.LinearAlgebra.FiniteDimensional

universe u v w

section Hom

variable {K : Type u} [CommRing K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {V : Type w} [AddCommGroup V] [Module K V]

-- instance : LieRingModule K (V →ₗ[K] V) := LinearMap.instLieRingModule
-- #check LieModule K L (V →ₗ[K] V)

open LinearMap

instance : LieRing (V →ₗ[K] V) where
  bracket := fun f g => f ∘ₗ g - g ∘ₗ f
  lie_add := by
    simp only [comp_add, add_comp]
    intro x y z; abel;
  add_lie := by
    simp only [add_comp, comp_add]
    intro x y z; abel;
  lie_self := by simp only [sub_self, forall_const]
  leibniz_lie := by
    simp only [comp_sub, sub_comp, comp_assoc]
    intro x y z; abel;


instance : LieAlgebra K (V →ₗ[K] V) where
  lie_smul := by simp only [lie_smul, forall_const]

instance : LieModule K (V →ₗ[K] V) V where
  smul_lie := by simp only [smul_lie, forall_const]
  lie_smul := by simp only [lie_smul, forall_const]

end Hom

section FiniteDimensional

open FiniteDimensional

variable {K : Type u} {L : Type v} (V : Type w)
variable [Field K]
variable [AddCommGroup V][Module K V] [FiniteDimensional K V]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable (v : Basis n K V)
variable [LieRing L] [LieAlgebra K L][LieRingModule L V] [LieModule K L V]
variable (W : LieSubmodule K L V)

lemma rank_eq_one' : finrank K K = 1 := by
  apply finrank_eq_one
  pick_goal 3
  . let k : K := 1
    use k
  . exact one_ne_zero
  . intro w; use w; simp;


lemma equiv_scalar_iff_rank_one : finrank K V = (1 : Nat) ↔ Nonempty (V ≃ₗ[K] K) := by
  constructor
  swap
  . intro h_equiv
    rcases h_equiv with ⟨f⟩
    rw [←@rank_eq_one' K]
    exact LinearEquiv.finrank_eq f
  . intro h_rank1
    unfold finrank at h_rank1
    sorry



noncomputable def Codimension (W : LieSubmodule K L V) : Nat :=
  (finrank K (V⧸W))


noncomputable def Trace (f : V →ₗ[K] V) : K := LinearMap.toMatrix v v f |>.trace

end FiniteDimensional
