import Mathlib.Algebra.Lie.Basic


import LieAlgRep.GeneralLinear

universe u v w

section
variable (K : Type u) [CommRing K]
variable (L : Type v) [LieRing L] [LieAlgebra K L]
variable (V : Type w) [AddCommGroup V] [Module K V]

abbrev Representation :=
  L →ₗ⁅K⁆ V →ₗ[K] V

end
namespace Representation
section asModule

variable {K : Type u} [CommRing K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {V : Type w} [AddCommGroup V] [Module K V]

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
variable (f : V →ₗ[K] V) (h_commute : ∀ x : L, f ∘ₗ φ x = φ x ∘ₗ f)



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
    let hhh := h_commute x
    have : f (φ x y) = φ x (f y) := by
      rw [LinearMap.ext_iff] at hhh
      exact hhh y
    rw [this, hy]; simp;

@[simp]
theorem mem_kernel (v : φ.asLieModule) : v ∈ φ.kernel f h_commute ↔ f v = 0 := by
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

def codRestrict' (f : M →ₗ⁅K, L⁆ N) (p : LieSubmodule K L N) (h : ∀ c, f c ∈ p) : M →ₗ⁅K, L⁆ p := by
  refine' { toFun := fun c => ⟨f c, h c⟩.. } <;> intros <;> apply SetCoe.ext <;> simp

end domRestrict



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
