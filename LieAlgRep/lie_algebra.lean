import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.OfAssociative

import Mathlib.Algebra.DirectSum.Decomposition

import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.BilinearForm.Properties

import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic

import LieAlgRep.Basic

variable {R : Type u} {L : Type v} {V : Type w}

#check LieAlgebra.IsSemisimple
#check Matrix.trace


open LinearMap




section Schur

variable {K : Type*} {L : Type*} {V : Type*}
variable [Field K] [IsAlgClosed K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]

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

end Schur


-- Deprecated
section LieSubalgebra

variable {K : Type*} [Field K] [IsAlgClosed K]
  {L : Type*} [LieRing L] [LieAlgebra K L]

instance HasBracket : Bracket (LieSubalgebra K L) (LieSubalgebra K L) where
  bracket := fun s1 s2 =>
  LieSubalgebra.lieSpan K L {m | ∃ (x : s1) (y : s2), ⁅(x : L), (y : L)⁆ = m}

end LieSubalgebra

section

open scoped DirectSum

variable {K : Type*} (V : Type*)
variable [Field K] [IsAlgClosed K]
variable {L : Type w} [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Nontrivial V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (I : Fin t → LieIdeal K L)

instance : LieAlgebra K (⨁ i, I i) := DirectSum.lieAlgebra fun i => ↥(I i)


-- theorem killing_compl_ideal_eq_top (I : LieIdeal K L) :
--   (I ⊕ LieIdeal.killingCompl K L I) = (⊤ : LieIdeal K L) := by sorry


-- theorem decomp_of_semisimple (hsemisimple : LieAlgebra.IsSemisimple K L) :
--   ∃ (I : Fin t → LieIdeal K L),
--   (∀ i, LieAlgebra.IsSimple K (I i)) ∧ (Nonempty (DirectSum.Decomposition I)) := by
--   sorry

-- theorem ad_eq_self_of_semisimple (hsemisimple : LieAlgebra.IsSemisimple K L) :
--   ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ = (⊤ : LieIdeal K L) := by sorry

end

section

variable {K : Type*} {L : Type*} {V : Type*}
variable [CommRing K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

noncomputable def Codimension (W : LieSubmodule K L V) : ℕ :=
  (FiniteDimensional.finrank K (V⧸W))


variable {K : Type*} [Field K] [IsAlgClosed K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {n : Type*} [DecidableEq n] [Fintype n]
variable (v : Basis n K V)

noncomputable def Trace (f : V →ₗ[K] V) : K := LinearMap.toMatrix v v f |>.trace

-- lemma triv_1dim_of_semisimplicity (φ : Representation K L V)
--   (hsemisimple : LieAlgebra.IsSemisimple K L) :
--   ∀ x : L, Trace v (φ x) = 0 := by sorry

end

section Weyl

section

variable (K : Type*) [CommRing K]
variable (L : Type*) [LieRing L] [LieAlgebra K L]
variable (M : Type*) [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable (N' : LieSubmodule K L M)

open Representation
lemma map_LieModuleHomResScalar: (LieModuleHomResScalar K L M N') →ₗ[K] K := by
  let fl := fun f => Exists.choose (ResScalar K L M N' f)  --get the function
  constructor
  swap
  constructor
  swap
  . exact fl
  . intro f1 f2 --proof add_hom property
    simp [fl]
    let k1 := Exists.choose (ResScalar K L M N' f1)
    have hk1 := Exists.choose_spec (ResScalar K L M N' f1)
    let k2 := Exists.choose (ResScalar K L M N' f2)
    have hk2 := Exists.choose_spec (ResScalar K L M N' f2)
    let k1pk2 := Exists.choose (ResScalar K L M N' (f1 + f2))
    have hk12 := Exists.choose_spec (ResScalar K L M N' (f1 + f2))
    simp at hk12
    have : k1 + k2 = k1pk2 := by sorry
    exact symm this
  . intro k f
    dsimp [fl]
    sorry

end

variable {K : Type*} [CommRing K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V]



open Representation

lemma Weyl_cod1 (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  (W : LieSubmodule K L V) (h_cod1 : Codimension W = 1) :
  ∃ (X : LieSubmodule K L V), (W ⊕ X) = (⊤ : LieSubmodule K L V) := by sorry

theorem Weyl (φ : Representation K L V) (hsemisimple : LieAlgebra.IsSemisimple K L) :
  IsCompletelyReducible φ := by
  constructor
  intro W
  let 𝒱 := LieModuleHomResScalar K L φ.asLieModule W
  let 𝒲 := LieModuleHomResZero' K L φ.asLieModule W
  have cod1 : Codimension 𝒲 = 1 := by
    have : Nonempty ((𝒱⧸𝒲) ≃ₗ[K] K) := by
      let θ := map_LieModuleHomResScalar K L φ.asLieModule W
      sorry
    have : FiniteDimensional.finrank K (𝒱⧸𝒲) = 1 := by
      let f := Classical.choice this
      rw [←FiniteDimensional.rank_eq_one_iff_finrank_eq_one]
      have : Module.rank K K = 1 := by sorry
      sorry
    exact this
  have : ∃ (𝒳 : LieSubmodule K L 𝒱), (𝒲 ⊕ 𝒳) = (⊤ : LieSubmodule K L 𝒱) := by sorry
  rcases this with ⟨𝒳, h𝒳⟩
  have : ∃ (f : 𝒳), ∀ (w : W), (f: φ.asLieModule →ₗ⁅K, L⁆ W) w = w := by sorry
  rcases this with ⟨f, hf⟩
  have : (W ⊕ (f.1.1.ker)) = (⊤ : LieSubmodule K L φ.asLieModule) := by sorry
  use (f : φ.asLieModule →ₗ⁅K, L⁆ W).ker

end Weyl
