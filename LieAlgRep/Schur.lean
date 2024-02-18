import LieAlgRep.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic

section Schur

variable {K : Type*} {L : Type*} {V : Type*}
variable [Field K] [IsAlgClosed K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]

open Representation
open LinearMap

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
      rw [comp_sub, sub_comp, hf x, comp_smul, smul_comp, id_comp, comp_id]
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
