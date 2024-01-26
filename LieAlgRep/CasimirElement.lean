import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.DirectSum.Decomposition

import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.BilinearForm.Properties

import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic

section


end
variable {R : Type u} {L : Type v} {V : Type w}

#check LieAlgebra.IsSemisimple
#check Matrix.trace

open LinearMap

section

variable (K : Type*) [Field K]
  (L : Type*) [LieRing L] [LieAlgebra K L]
  (V : Type*) [AddCommGroup V] [Module K V]

abbrev Representation :=
  L →ₗ⁅K⁆ V →ₗ[K] V

end

section GeneralLinear

variable (K : Type*) [Field K]
  (L : Type*) [LieRing L] [LieAlgebra K L]
  (V : Type*) [AddCommGroup V] [Module K V]

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

section

variable {ι : Type*}
{K : Type*} [Field K]
{L : Type*} [LieRing L] [Module K L] [LieAlgebra K L]

def IsAssociativeBilForm   (B : BilinForm K L) : Prop :=
  ∀ x y z : L,  B ⁅x, y⁆ z = B x ⁅y, z⁆

variable
{ι : Type*} [Finite ι] [DecidableEq ι] [Fintype ι]
{K : Type*} [Field K]
{L : Type*} [LieRing L]  [LieAlgebra K L] [Module K L]
{V : Type*} [AddCommGroup V] [Module K V]

example (φ : Representation K L V) (x y : L) : φ ⁅x, y⁆ = ⁅φ x, φ y⁆ := by simp

example (f : ι → V) (g : V →ₗ[K] V) : g (Finset.sum Finset.univ fun (i : ι) => f i) = Finset.sum Finset.univ fun (i : ι) => g (f i) := by
  apply map_sum

noncomputable def CasimirElement (B : BilinForm K L) (φ : Representation K L V) (BasisL : Basis ι K L)
  (hBnondeg : BilinForm.Nondegenerate B)  : (V →ₗ[K] V) := by
  have DualBasisL : Basis ι K L := BilinForm.dualBasis B hBnondeg BasisL
  let f : ι → V →ₗ[K] V := fun i => (φ (BasisL i)) ∘ₗ (φ (DualBasisL i))
  have Casimir : (V →ₗ[K] V) := Finset.sum Finset.univ fun (i : ι) => f i
  exact Casimir

lemma bracket_in_glV (f g : V →ₗ[K] V) :
  ⁅f, g⁆ = f ∘ₗ g - g ∘ₗ f := by
    simp [Bracket.bracket]
    constructor

lemma comm_zero_bracket (f g : V →ₗ[K] V) :
⁅f, g⁆ = 0 ↔ g ∘ₗ f = f ∘ₗ g := by
  rw [bracket_in_glV]
  constructor
  · intro h
    have : f ∘ₗ g - g ∘ₗ f + g ∘ₗ f = 0 + g ∘ₗ f := Mathlib.Tactic.LinearCombination.pf_add_c h (g ∘ₗ f)
    rw [zero_add, sub_add, sub_self, sub_zero] at this
    rw[←this]
  · intro h
    rw[h,sub_self]

lemma CasimirIntertwin (B : BilinForm K L) (φ : Representation K L V) (BasisL : Basis ι K L) (hBnondeg : BilinForm.Nondegenerate B) (hBsymm : BilinForm.IsSymm B) (hBassoc : IsAssociativeBilForm B) :
  ∀ l : L, (CasimirElement B φ BasisL hBnondeg) ∘ₗ (φ l) = (φ l) ∘ₗ (CasimirElement B φ BasisL hBnondeg) := by
  intro l
  -- Define the dual basis of BasisL
  have DualBasisL : Basis ι K L := BilinForm.dualBasis B hBnondeg BasisL
  -- [l x_i] = Σ a_ij x_j, [l y_i] = Σ b_ij y_j
  -- Then a_ij + b_ji = 0
  let BasisCoeff_l : ι → ι → K := fun i j => BasisL.repr (⁅l, (BasisL i)⁆) j
  let DualBasisCoeff_l : ι → ι → K := fun i j => DualBasisL.repr (⁅l, (DualBasisL i)⁆) j
  have aij_eq_neg_bji : ∀ i j, (BasisCoeff_l i j) + (DualBasisCoeff_l j i) = 0 := by sorry
  -- an nick name of Casimir Element
  let cphi := CasimirElement B φ BasisL hBnondeg
  have essentialIdentity : ∀ (x y z : V →ₗ[K] V), ⁅x, y ∘ₗ z⁆ = ⁅x, y⁆ ∘ₗ z + y ∘ₗ ⁅x, z⁆ := by
    intro x y z
    simp only [bracket_in_glV]
    rw [LinearMap.sub_comp, LinearMap.comp_sub]
    rw [←LinearMap.comp_assoc z x y]
    abel

  have CasimirCommute : ⁅φ l, cphi⁆ = 0 := by sorry
  rw [comm_zero_bracket] at CasimirCommute
  assumption

end
