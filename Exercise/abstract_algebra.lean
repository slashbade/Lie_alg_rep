import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Finite
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.QuotientGroup

import Mathlib.RingTheory.Ideal.Basic


variable {G : Type } [Group G] [Fintype G]


theorem group_theory_prob1 (H1 H2 : Subgroup G) :
  (∃ H : Subgroup G, H.carrier = (H1.carrier ∪ H2.carrier)) → (H1 ≤ H2 ∨ H2 ≤ H1) := by
  contrapose!
  rintro ⟨H1notinc, H2notinc⟩ H
  have hh1 : ∃ h1, h1 ∈ H1 ∧ ¬h1 ∈ H2 := by
    by_contra h1any
    push_neg at h1any
    have : H1 ≤ H2 := by
      intros h1 h1inH1
      exact h1any h1 h1inH1
    contradiction
  have hh2 : ∃ h2, h2 ∈ H2 ∧ ¬h2 ∈ H1 := by
    by_contra h2any
    push_neg at h2any
    have : H2 ≤ H1 := by
      intros h2 h2inH2
      exact h2any h2 h2inH2
    contradiction
  intro hh12
  rcases hh1 with ⟨h1, h1prop⟩
  rcases hh2 with ⟨h2, h2prop⟩
  have h1h2inH : h1 * h2 ∈ H.carrier := by
    apply Subsemigroup.mul_mem'
    . rw [hh12, Set.mem_union]
      left
      rw [Subgroup.mem_carrier]
      exact h1prop.left
    . rw[hh12, Set.mem_union]
      right
      rw [Subgroup.mem_carrier]
      exact h2prop.left
  rw [hh12] at h1h2inH
  apply Set.mem_or_mem_of_mem_union at h1h2inH
  rcases h1h2inH with h1h2inH1 | h1h2inH2
  . have h2inH1 : h2 ∈ H1 := by
      rw [Subgroup.mem_carrier] at h1h2inH1
      have : h2 = h1⁻¹ * (h1 * h2) := by group
      rw [this]
      apply mul_mem
      . apply inv_mem
        exact h1prop.left
      . exact h1h2inH1
    absurd h2prop.right
    exact h2inH1
  . have h1inH2 : h1 ∈ H2 := by
      rw [Subgroup.mem_carrier] at h1h2inH2
      have : h1 = h1 * h2 * h2⁻¹ := by group
      rw [this]
      apply mul_mem
      . exact h1h2inH2
      . apply inv_mem
        exact h2prop.left
    absurd h1prop.right
    exact h1inH2

-- variable {K : Type*} [Group K] [IsKleinFour K]
-- variable {Z4 : Type*} [Group Z4] [IsCyclic Z4]

open Fintype
open Subgroup
open QuotientGroup

-- lemma fin_subgroup_of_fin_group (K : Subgroup G) [Fintype G] : Fintype K := by sorry



#check card_subgroup_dvd_card
#check card_dvd_of_le
#check card_top
#check eq_bot_of_card_eq
#check eq_top_of_card_eq
#check card_eq_iff_eq_top
#check CommGroup.center_eq_top
#check Group.commGroupOfCenterEqTop
#check Nat.mem_factors_iff_dvd
#check isCyclic_of_prime_card
#check card_eq_card_quotient_mul_card_subgroup
-- lemma test := sorry
theorem card_eq_card_quotient_mul_card_subgroup' {α : Type*} [Group α] [Fintype α] (s : Subgroup α) [Fintype s]
    [Fintype (α ⧸ s)] : Fintype.card α = Fintype.card (α ⧸ s) * Fintype.card s := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr Subgroup.groupEquivQuotientProdSubgroup

lemma comm_of_cyclic_over_center {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [nN : N.Normal]
  (hc : IsCyclic (G ⧸ N)) : CommGroup G := by
  constructor
  sorry

lemma p_eq_of_p_dvd_psq [Fact (Nat.Prime p)] {n : ℕ}
  (h : n ∣ p ^ 2) (h1 : n ≠ 1) : n = p ∨ n = p ^ 2 := by sorry

lemma no_center_of_order_prime_pow {G : Type*} [Group G] [Fintype G]
  (h : card G = p ^ 2) : (Subgroup.center G) ≠ ⊥ := by sorry

lemma center_eq_top' {G : Type*} (h : CommGroup G) : Subgroup.center G = ⊤ := by
  rw [eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  exact mul_comm y x

lemma center_normal' {G : Type*} [Group G]: Normal (center G) := by sorry

theorem group_theory_prob2 {G : Type*} [Group G] [Fintype G]
[Fact (Nat.Prime p)] (h : card G = p ^ 2) : CommGroup G := by
  let Z := Subgroup.center G
  have finz : Fintype (Z : Subgroup G) := by apply ofFinite
  have : card Z = p ∨ card Z = p ^ 2 := by
    have : card Z ∣ card G := by apply card_subgroup_dvd_card
    rw [h] at this
    apply p_eq_of_p_dvd_psq this
    have Z_ne_top : Z ≠ ⊥ := by
      apply no_center_of_order_prime_pow h
    by_contra cardz1
    have Z_eq_top: Z = ⊥ := by exact eq_bot_of_card_eq Z cardz1
    contradiction
  apply Group.commGroupOfCenterEqTop
  apply eq_top_of_card_eq Z
  rw [h]
  rcases this with cardz_p | cardz_p2
  . have : Subgroup.Normal Z := by
      exact center_normal'
    let pmz := G ⧸ Z
    have : Fintype pmz := by exact fintypeQuotientOfFiniteIndex Z
    have p_pos : p > 0 := by apply Nat.Prime.pos Fact.out
    have : card pmz = p := by
      rw [← Nat.mul_right_cancel_iff p_pos, ←pow_two, ←h, ←cardz_p]
      apply symm
      exact card_eq_card_quotient_mul_card_subgroup' Z
    have : IsCyclic pmz := by
      exact isCyclic_of_prime_card this
    have : CommGroup G := by apply comm_of_cyclic_over_center Z this
    exfalso
    have : card Z = p ^ 2 := by
      rw [←h]
      rw [card_eq_iff_eq_top]
      dsimp
      --apply center_eq_top' this
      sorry
    rw [cardz_p] at this
    rw [pow_two] at this
    have : p = 1 := by
      rw [← Nat.mul_right_cancel_iff p_pos]
      rw [Nat.one_mul]
      exact symm this
    have p_ne_one: p ≠ 1 := by apply ne_of_gt (Nat.Prime.one_lt Fact.out)
    contradiction
  exact cardz_p2


section

#check Fin 10


variable {R : Type*} [Ring R]

theorem ring_theory_prob {n : ℕ}
  (I : Ideal R) (p : Fin (n + 1) → Ideal R) (h : ∀ i, Ideal.IsPrime (p i)) :
  (∀i, ¬ I ≤ p i) → (∃ x ∈ I, ∀ i, ¬ x ∈ p i) := by
  induction' n with n ind_hyp
  . intro h0; simp;
    by_contra xnp
    push_neg at xnp
    have : (i : Fin (Nat.succ Nat.zero)) → i = 0 := by
      intro j; fin_cases j; simp
    simp [this] at h0 xnp
    have : I ≤ p 0 := by exact xnp
    contradiction
  have : ∃ (a : Fin (n + 1) → R), (∀ i, a i ∈ I) ∧ (∀ (i j), j ≠ i → a i ∈ p j) := by sorry
  rcases this with ⟨a, h2⟩
  let p_cond := ∃ (i : Fin (n + 1)), a i ∉ p i
  rcases Classical.em p_cond with p_cond_true | p_cond_false
  . rcases p_cond_true with ⟨i1, hi1⟩
    intro h3
    use a i1
    constructor
    . apply h2.left i1
    intro i2
    rcases Classical.em (i2 = i1) with i2eqi1 | i2nei1
    . rw [i2eqi1]
      exact hi1
    have h_i2 : ∃ k : Fin (n + 1), i2 = if i2 < ↑↑i1 then ↑k else ↑(k + 1) := by sorry
    rcases h_i2 with ⟨k, h_k⟩
    rw [h_k]
  simp at p_cond_false
  sorry

end
