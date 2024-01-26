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

variable [Field K] [IsAlgClosed K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end GeneralLinear

section

variable {ι : Type*}
{K : Type*} [Field K]
{L : Type*} [LieRing L] [Module K L] [LieAlgebra K L]

def IsAssociativeBilForm   (B : BilinForm K L) : Prop :=
  ∀ x y z : L,  B ⁅x, y⁆ z = B x ⁅y, z⁆

end

section CasimirElement

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

end CasimirElement


namespace Representation

section asModule

variable {K : Type*} {L : Type*} {V : Type*}
variable [CommRing K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]

def asLieModule (_ : Representation K L V) := V

variable (φ : Representation K L V)

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

lemma smul_map (k : K) (v : V) : k • (φ.asLieModuleEquiv v) = φ.asLieModuleEquiv (k • v) := by
  rw [LinearEquiv.map_smul]

end asModule

section kernel

variable {K : Type*} {L : Type*} {V : Type*}
variable [CommRing K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]
variable {φ : Representation K L V}
variable (f : V →ₗ[K] V) (commute : ∀ x : L, f ∘ₗ φ x = φ x ∘ₗ f)



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

end kernel

section LieModuleHomAsLieModule

section

variable {K : Type*} {L : Type*} {V : Type*}
variable [CommRing K]
variable [LieRing L] [LieAlgebra K L]

variable (M : Type*) [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]

variable (N : Type*) [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]

#check LieRingModule.toBracket

-- A Lie module homomorphism is a LieRingModule
instance lie_ring_module_of_lie_hom : LieRingModule L (M →ₗ⁅K,L⁆ N) where
  bracket := fun x f =>
    LieModuleHom.mk
      (LinearMap.mk
        (AddHom.mk (fun v => ⁅x, f v⁆ - f ⁅x, v⁆) (by intro v w; simp only [LieModuleHom.map_add,
          lie_add, LieModuleHom.map_lie, sub_self, add_zero];))
        (by simp only [LieModuleHom.map_smul, lie_smul, LieModuleHom.map_lie, sub_self,
          RingHom.id_apply, smul_zero, forall_const];))
      (by simp only [LieModuleHom.map_lie, sub_self, lie_zero, forall_const])
  lie_add := by intro x f1 f2; ext; simp [Bracket.bracket]
  add_lie := by intro x1 x2 f; ext; simp [Bracket.bracket]
  leibniz_lie := by intro x y f; ext; simp [Bracket.bracket]

instance lie_module_of_lie_hom : LieModule K L (M →ₗ⁅K,L⁆ N) where
  smul_lie := by
    intro k x f; ext; simp [Bracket.bracket]
  lie_smul := by
    intro k x f; ext; simp [Bracket.bracket]

-- @[simp]
-- lemma smul_smul_lie_module_hom (k k' : K) (f : M →ₗ⁅K,L⁆ N) :
--   (k * k') • f = k • (k' • f) := by apply

-- variable (N' : Type) [AddCommGroup N'] [Module K N']
-- variable [LieRingModule L N']
@[simp]
lemma lie_module_of_lie_hom_apply (x : L) (f : M →ₗ⁅K,L⁆ N) (v : M) :
  ⁅x, f⁆ v = ⁅x, f v⁆ - f ⁅x, v⁆ := rfl

@[simp]
lemma coe_add (f g : M →ₗ⁅K,L⁆ N) : (↑(f + g) : M →ₗ[K] N) = (↑f + ↑g) := rfl

@[simp]
lemma coe_zero : (↑(0 : M →ₗ⁅K,L⁆ N) : M →ₗ[K] N) = 0 := rfl

@[simp]
lemma coe_smul : ∀ (k : K) (f : M →ₗ⁅K,L⁆ N), (↑(k • f) : M →ₗ[K] N) = k • ↑f := by
  intros; ext; simp

end


namespace LieSubmodule'

variable {K : Type*} {L : Type*} {V : Type*}
variable [CommRing K]
variable [LieRing L] [LieAlgebra K L]

variable {M : Type*} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]

variable {N : Type*} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]

variable (p : LieSubmodule K L M)

def liesubtype : p →ₗ⁅K, L⁆ M := by refine' { toFun := Subtype.val.. } <;> simp [coe_smul]

end LieSubmodule'



section domRestrict

variable {K : Type*} {L : Type*} {V : Type*}
variable [CommRing K]
variable [LieRing L] [LieAlgebra K L]

variable {M : Type*} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]

variable {N : Type*} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]

-- variable (p : LieSubmodule K L M)
-- #check p.subtype

def domRestrict' (f : M →ₗ⁅K, L⁆ N) (p : LieSubmodule K L M) : p →ₗ⁅K, L⁆ N :=
  f.comp (LieSubmodule'.liesubtype p)

@[simp]
theorem dom_restrict'_add (f g: M →ₗ⁅K, L⁆ N) :
  domRestrict' (f + g) p = domRestrict' f p + domRestrict' g p := rfl

@[simp]
theorem dom_restrict'_zero :
  domRestrict' (0 : M →ₗ⁅K, L⁆ N) p = 0 := rfl

@[simp]
theorem dom_restrict'_smul (k : K) (f : M →ₗ⁅K, L⁆ N) :
  domRestrict' (k • f) p = k • domRestrict' f p := rfl

-- variable (ss :  M →ₗ[K] N)
-- #check ss.domRestrict

@[simp]
theorem dom_restrict'_map_lie (x : L) (f : M →ₗ⁅K, L⁆ N) :
  domRestrict' (↑⁅x, f⁆ : M →ₗ⁅K, L⁆ N) p = ⁅x, (domRestrict' f p)⁆ := rfl

end domRestrict


section

variable (K : Type*) [CommRing K]
variable (L : Type*) [LieRing L] [LieAlgebra K L]
variable (M : Type*) [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable (N' : LieSubmodule K L M)

def LieModuleHomResScalar : LieSubmodule K L (M →ₗ⁅K,L⁆ N') where
  carrier := {f | ∃ (k : K), domRestrict' f N' = k • (LinearMap.id : N' →ₗ[K] N')}
  add_mem' := by
    simp; intro f1 f2 k1 hf1 k2 hf2;
    use k1 + k2; rw[add_smul k1 k2 LinearMap.id, ←hf1, ←hf2]
  zero_mem' := by simp; use 0; simp;
  smul_mem' := by
    simp; intro k f k' hfk1; use k * k';
    simp [mul_smul, mul_comm, ←hfk1]
  lie_mem := by simp; intro _ _ _ h; use 0; rw [zero_smul]; apply ext; simp [h];

@[simp]
lemma mem_LieModuleHomResScalar {f} : f ∈ LieModuleHomResScalar K L M N' ↔
    ∃ (k : K), domRestrict' f N' = k • (LinearMap.id : N' →ₗ[K] N') := by rfl

@[simp]
lemma ResScalar (f : LieModuleHomResScalar K L M N') :
  ∃ (k : K), domRestrict' f.1 N' = k • (LinearMap.id : N' →ₗ[K] N') := by
  have := f.2
  rw [mem_LieModuleHomResScalar] at this
  -- constructor
  -- constructor
  -- swap
  -- intro kk sss
  -- . intro nn
  --   rcases this with ⟨k, hk⟩
  --   simp [hk nn]

  exact this

noncomputable def obtain_scalar (f : LieModuleHomResScalar K L M N') : K := by
  have := f.2
  rw [mem_LieModuleHomResScalar] at this
  exact Exists.choose this



@[simp]
lemma lie_apply_of_lie_hom_res_scalar (f : LieModuleHomResScalar K L M N') (x : L) (v : M) :
  (↑⁅x, f⁆ : M →ₗ⁅K,L⁆ N') v = ⁅x, (f : M →ₗ⁅K,L⁆ N') v⁆ - (f : M →ₗ⁅K,L⁆ N') ⁅x, v⁆ := rfl


def LieModuleHomResZero: LieSubmodule K L (M →ₗ⁅K,L⁆ N') where
  carrier := {f | ∀ (n : N'), (f.domRestrict N') n = 0}
  add_mem' := by
    simp; intro f1 f2 hf1 hf2 a ha;
    rw [Pi.add_apply, hf1 a ha, hf2 a ha, add_zero]
  zero_mem' := by simp;
  smul_mem' := by simp; intro k f hh m b; simp [hh m b]
  lie_mem := by simp only [domRestrict_apply, LieModuleHom.coe_toLinearMap, Subtype.forall,
    Set.mem_setOf_eq, lie_module_of_lie_hom_apply, LieModuleHom.map_lie, sub_self, implies_true,
    forall_const];

def LieModuleHomResZero': LieSubmodule K L (LieModuleHomResScalar K L M N') where
  carrier := {f | ∀ (n : N'), (f : M →ₗ⁅K,L⁆ N') n = 0}
  add_mem' := by
    simp; intro f1 k1 _ f2 k2 _ hf10 hf20 a ha
    rw [Pi.add_apply, hf10 a ha, hf20 a ha, add_zero]
  zero_mem' := by simp;
  smul_mem' := by simp; intro k f k' _ hh a ha; simp [hh a ha]
  lie_mem := by
    intro x m;
    simp only [LieModuleHom.coe_toLinearMap, Subtype.forall, Set.mem_setOf_eq]
    intro _ a _
    rw [lie_apply_of_lie_hom_res_scalar _ _ _ _ m x a]
    simp

@[simp]
lemma mem_LieModuleHomResZero' {f}:
    f ∈ LieModuleHomResZero' K L M N' ↔ ∀ (n : N'), (f : M →ₗ⁅K,L⁆ N') n = 0 :=
  Iff.rfl

@[simp]
lemma ResZero {f : LieModuleHomResZero' K L M N'} : ∀ (n : N'), (f : M →ₗ⁅K,L⁆ N') n = 0 := by
  have := f.2
  rw [mem_LieModuleHomResZero'] at this
  exact this

-- variable {f : LieModuleHomResZero' K L M N'}
-- #check f.2
-- #check (LieModuleHomResZero' K L M N').zero_mem'

end

end LieModuleHomAsLieModule




section Reducibility

variable {K : Type*} [CommRing K]
  {L : Type*} [LieRing L] [LieAlgebra K L]
  {V : Type*} [AddCommGroup V] [Module K V]

class IsIrreducible (φ : Representation K L V) : Prop where
  Irreducible : ∀ W : LieSubmodule K L φ.asLieModule, W ≠ ⊥ →  W = ⊤

class IsCompletelyReducible (φ : Representation K L V) : Prop where
  CompletelyReducible : ∀ W : LieSubmodule K L φ.asLieModule, ∃ W' : LieSubmodule K L φ.asLieModule,
    (W ⊕ W') = (⊤ : LieSubmodule K L φ.asLieModule)

end Reducibility


end Representation

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

variable {U : Type*} [AddCommGroup U] [Module K U]
variable {Y : Submodule K U}
variable (f : U⧸Y) (x : U)

open Representation


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
