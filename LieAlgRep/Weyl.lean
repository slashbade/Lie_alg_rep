import LieAlgRep.Basic
import LieAlgRep.GeneralLinear
import Mathlib.Algebra.Lie.Semisimple

open Representation

variable (K : Type*) [CommRing K]
variable (L : Type*) [LieRing L] [LieAlgebra K L]
variable (M : Type*) [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable (N' : LieSubmodule K L M)

def LieModuleHomResScalar : LieSubmodule K L (M →ₗ⁅K,L⁆ N') where
  carrier := {f | ∃ (k : K), domRestrict' f N' = k • LieModuleHom.id}
  add_mem' := by
    simp; intro f1 f2 k1 hf1 k2 hf2;
    use k1 + k2; rw[add_smul k1 k2 LieModuleHom.id, ←hf1, ←hf2]
  zero_mem' := by simp; use 0; simp;
  smul_mem' := by
    simp; intro k f k' hfk1; use k * k';
    simp [mul_smul, mul_comm, ←hfk1]
  lie_mem := by simp; intro _ _ _ h; use 0; rw [zero_smul]; apply LieModuleHom.ext; simp [h];

@[simp]
lemma mem_LieModuleHomResScalar {f} : f ∈ LieModuleHomResScalar K L M N' ↔
    ∃ (k : K), domRestrict' f N' = k • LieModuleHom.id := by rfl

@[simp]
lemma ResScalar (f : LieModuleHomResScalar K L M N') :
  ∃ (k : K), domRestrict' f.1 N' = k • LieModuleHom.id := by
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
  lie_mem := by simp only [LinearMap.domRestrict_apply, LieModuleHom.coe_toLinearMap, Subtype.forall,
    Set.mem_setOf_eq, lie_module_of_lie_hom_apply, LieModuleHom.map_lie, sub_self, implies_true,
    forall_const];

def LieModuleHomResZero': LieSubmodule K L (LieModuleHomResScalar K L M N') where
  carrier := {f | ∀ (n : N'), (f : M →ₗ⁅K,L⁆ N') n = 0}
  add_mem' := by
    simp only [Subtype.forall, Set.mem_setOf_eq, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
      LieModuleHom.coe_add, LieSubmodule.mem_coeSubmodule, mem_LieModuleHomResScalar,
      forall_exists_index]; intro f1 k1 _ f2 k2 _ hf10 hf20 a ha
    rw [Pi.add_apply, hf10 a ha, hf20 a ha, add_zero]
  zero_mem' := by simp only [Subtype.forall, Set.mem_setOf_eq, ZeroMemClass.coe_zero,
    LieModuleHom.coe_zero, Pi.zero_apply, implies_true, forall_const];
  smul_mem' := by simp only [Subtype.forall, Set.mem_setOf_eq, SetLike.val_smul,
    LieModuleHom.coe_smul, Pi.smul_apply, LieSubmodule.mem_coeSubmodule, mem_LieModuleHomResScalar,
    forall_exists_index]; intro k f k' _ hh a ha; simp only [hh a ha, smul_zero]
  lie_mem := by
    intro x m;
    simp only [LieModuleHom.coe_toLinearMap, Subtype.forall, Set.mem_setOf_eq]
    intro _ a _
    rw [lie_apply_of_lie_hom_res_scalar _ _ _ _ m x a]
    simp only [LieModuleHom.map_lie, sub_self]

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

section Weyl

open Representation

variable {K : Type*} [Field K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V]



open Representation

lemma Weyl_cod1 (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  (W : LieSubmodule K L V) (h_cod1 : Codimension V W = 1) :
  ∃ (X : LieSubmodule K L V), (W ⊕ X) = (⊤ : LieSubmodule K L V) := by sorry

theorem Weyl (φ : Representation K L V) (hsemisimple : LieAlgebra.IsSemisimple K L) :
  IsCompletelyReducible φ := by
  constructor
  intro W
  let 𝒱 := LieModuleHomResScalar K L φ.asLieModule W
  let 𝒲 := LieModuleHomResZero' K L φ.asLieModule W
  have cod1 : Codimension 𝒱 𝒲 = 1 := by
    -- construct a function f maps x to x if x in W, to 0 if x not in W
    -- then f lies in McV
    sorry
  have : ∃ (𝒳 : LieSubmodule K L 𝒱), (𝒲 ⊕ 𝒳) = (⊤ : LieSubmodule K L 𝒱) := by exact Weyl_cod1 𝒱 𝒲 cod1
  rcases this with ⟨𝒳, h𝒳⟩
  have : ∃ (f : 𝒳), ∀ (w : W), (f: φ.asLieModule →ₗ⁅K, L⁆ W) w = w := by sorry
  rcases this with ⟨f, hf⟩
  have : (W ⊕ (f.1.1.ker)) = (⊤ : LieSubmodule K L φ.asLieModule) := by sorry
  use (f : φ.asLieModule →ₗ⁅K, L⁆ W).ker
