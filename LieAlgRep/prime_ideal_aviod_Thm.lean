import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PNat.Defs
import Init.Prelude

open Classical

theorem Ideal.IsPrime_not_mem_mul {α : Type u} [CommSemiring α]  {I : Ideal α}
(hI : Ideal.IsPrime I) {x : α} {y : α} : x ∉ I ∧ y ∉ I → x * y ∉ I := by
  intro h
  by_contra hxy
  rcases h with ⟨hx, hy⟩
  by_cases h' : x ∈ I
  · exact hx h'
  have hyin : x ∈ I ∨ y ∈ I := (Ideal.IsPrime.mul_mem_iff_mem_or_mem hI).mp hxy
  exact Or.elim hyin hx hy

theorem Ideal.multiset_not_mem {α :Type u} [CommRing α] {β : Type u}
{I : Ideal α } (hI : Ideal.IsPrime I) (S : Multiset β)
(g : (s : β ) → (s ∈ S ) → α)
(h : ∀ s (h : s ∈ S),  g s h ∉ I)
:
  (S.pmap g (fun x hx ↦ hx)).prod ∉ I := sorry

theorem Ideal.multiset_mem_in {α :Type u} [CommRing α] {β : Type u}
{I : Ideal α }  (S : Multiset β)
(g : (s : β ) → (s ∈ S ) → α)
(h : ∃ s, (h : s ∈ S) →  g s h ∈  I)
:
  (S.pmap g (fun x hx ↦ hx)).prod ∈  I := sorry

theorem Multiset.erase_refl {β : Type u} {S : Multiset β}{s₀ s : β }
(h₀ : s₀ ∈ S) (h : s ∈ S.erase s₀) : s₀ ∈ S.erase s := by
  by_cases heq : s = s₀
  · rw [heq] at h
    rwa [heq]
  apply (Multiset.mem_erase_of_ne _).mpr h₀
  intro h₁
  exact heq h₁.symm

theorem prime_ideal_finset_version {α : Type u}  [CommRing α]  {I : Ideal α}
{β : Type u } {n : ℕ} {f : β → Ideal α}
: ∀ (S : Multiset β), (Multiset.card S = n) → (∀ s ∈ S, Ideal.IsPrime (f s) ∧  ¬ I ≤ f s)
  → (∃ x ∈ I, ∀ s ∈ S, (x ∉ f s)) := by
  induction' n with n ih
  · simp only [Nat.zero_eq, Multiset.card_eq_zero, forall_eq, Multiset.not_mem_zero,
    IsEmpty.forall_iff, implies_true, and_true, forall_true_left]
    use 0
    simp only [Submodule.zero_mem]
  · intro S h₁ h₂
    have : ∀ s ∈ S, Multiset.card (Multiset.erase S s) + 1 = Nat.succ n := by
      intro s tins
      rw [←h₁]
      norm_num [Multiset.card_erase_add_one tins]
    -- use the assumption of induction
    have cardOfSone : ∀ s ∈ S, Multiset.card (Multiset.erase S s) = n := by
      intro s hs
      have this'' : Multiset.card (Multiset.erase S s) + 1 = n + 1 := by
        norm_num [this s hs]
      exact Nat.succ_inj'.mp this''
    have existb : ∀ s ∈ S, ∃ x ∈ I, ∀ b ∈ (Multiset.erase S s), x ∉ f b := by
      intro s hs
      let S₁ := (Multiset.erase S s)
      apply ih S₁ (cardOfSone s hs)
      intro t ht
      exact h₂ t (Multiset.mem_of_mem_erase ht)
    choose g'' hg' using existb
    let g' : β -> α := fun s =>
      if h : s ∈ S then g'' s h else 1
    by_cases hx : ∃ s ∈ S, (∀ s' ∈ (Multiset.erase S s), (g' s) ∉ f s') ∧ (g' s) ∉ f s
    · rcases hx with ⟨s, hs, _, hx₁⟩
      let x := g' s
      use x
      have this' : x ∈ I ∧ ∀ b ∈ (Multiset.erase S s), x ∉ f b := by
        simp only [dite_true, hs]
        exact hg' _ _
      constructor
      exact this'.1
      intro b
      by_cases beqs : b = s
      · intro _
        rwa [beqs]
      intro h'
      have bnots : b ∈ (Multiset.erase S s) := (Multiset.mem_erase_of_ne beqs).mpr h'
      exact this'.2 b bnots
    push_neg at hx
    have Snotzero : S ≠ 0 := by
      intro hseqzero
      have cardSeqzero : Multiset.card S = 0 := by simp [hseqzero]
      linarith
    choose s₀ szeroin using Multiset.exists_mem_of_ne_zero Snotzero
    let x₁ := ((S.erase s₀).pmap g'' (fun _ ↦ Multiset.mem_of_mem_erase)).prod
    let x₂ := g' s₀
    let x := x₁ + x₂
    use x
    have hgeq : ∀ s (h : s ∈ S ), g' s = g'' s h := by
        intro s h
        simp only [dite_true, h]
    -- use the property of prime ideal below
    have xonenotin : x₁ ∉ f s₀ := by
      simp [x₁, *, Multiset.mem_of_mem_erase]
      --↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓repeat part↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓
      let g''' : (s : β) → s ∈ (S.erase s₀) → α := fun s _ ↦
        if h : s ∈  (S.erase s₀) then g'' s (Multiset.mem_of_mem_erase h) else 1
      have this' : ∀ s (h : s ∈ (S.erase s₀)),
        g'' s (Multiset.mem_of_mem_erase h) = g''' s h := by
          intro s hsin
          simp only [hsin, dite_true]
      have this'' : ((S.erase s₀).pmap g'' (fun _ ↦ Multiset.mem_of_mem_erase)).prod
        = ((S.erase s₀).pmap g''' (fun x hx ↦ hx)).prod := by
          congr 1
          apply Multiset.pmap_congr (S.erase s₀)
          intro a ha _ _
          exact this' a ha
      --↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑repeat part↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
      have hnotin : ∀ s (hnotin : s ∈ (S.erase s₀)),
        g''' s hnotin ∉ f s₀ := by
        intro s hnotin
        rw [← this' s hnotin]
        exact ((hg' s (Multiset.mem_of_mem_erase hnotin)).2 s₀ (Multiset.erase_refl szeroin hnotin))
      rw [this'']
      exact Ideal.multiset_not_mem (h₂ s₀ szeroin).1 (S.erase s₀) g''' hnotin
    have xonein : ∀ b ∈ (S.erase s₀), x₁ ∈ f b := by
      intro b _
      simp [x₁, *, Multiset.mem_of_mem_erase]
      --↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓repeat part↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓
      let g''' : (s : β) → s ∈ (S.erase s₀) → α := fun s _ ↦
        if h : s ∈  (S.erase s₀) then g'' s (Multiset.mem_of_mem_erase h) else 1
      have this' : ∀ s (h : s ∈ (S.erase s₀)),
        g'' s (Multiset.mem_of_mem_erase h) = g''' s h := by
          intro s hsin
          simp only [hsin, dite_true]
      have this'' : ((S.erase s₀).pmap g'' (fun _ ↦ Multiset.mem_of_mem_erase)).prod
        = ((S.erase s₀).pmap g''' (fun x hx ↦ hx)).prod := by
          congr 1
          apply Multiset.pmap_congr (S.erase s₀)
          intro a ha _ _
          exact this' a ha
      --↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑repeat part↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
      rw [this'']
      apply Ideal.multiset_mem_in (S.erase s₀) g'''
      use b
      intro hb'
      rw [←this' b hb', ← hgeq b (Multiset.mem_of_mem_erase hb')]
      apply hx b (Multiset.mem_of_mem_erase hb')
      intro s' hs'
      rw [hgeq b (Multiset.mem_of_mem_erase hb')]
      exact (hg' b (Multiset.mem_of_mem_erase hb')).2 s' hs'
    have xtwoin : x₂ ∈ f s₀ := by
      apply (hx s₀ szeroin)
      simp only [dite_true, szeroin]
      exact (hg' s₀ szeroin).2
    have xtwonotin : ∀ b ∈ (S.erase s₀), x₂ ∉ f b := by
      simp only [dite_true, szeroin]
      exact (hg' s₀ szeroin).2
    --use the property of prime ideal above
    constructor
    · -- goal : x ∈ I
      have hx₁ : x₁ ∈ I := by
        simp [x₁, *, Multiset.mem_of_mem_erase]
        --↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓repeat part↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓
        let g''' : (s : β) → s ∈ (S.erase s₀) → α := fun s _ ↦
          if h : s ∈  (S.erase s₀) then g'' s (Multiset.mem_of_mem_erase h) else 1
        have this' : ∀ s (h : s ∈ (S.erase s₀)),
          g'' s (Multiset.mem_of_mem_erase h) = g''' s h := by
            intro s hsin
            simp only [hsin, dite_true]
        have this'' : ((S.erase s₀).pmap g'' (fun _ ↦ Multiset.mem_of_mem_erase)).prod
          = ((S.erase s₀).pmap g''' (fun x hx ↦ hx)).prod := by
            congr 1
            apply Multiset.pmap_congr (S.erase s₀)
            intro a ha _ _
            exact this' a ha
        --↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑repeat part↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
        rw [this'']
        apply Ideal.multiset_mem_in (S.erase s₀) g'''
        by_cases hserase : Multiset.erase S s₀ = 0
        · simp [hserase]
          use s₀
        choose s₁ _ using Multiset.exists_mem_of_ne_zero hserase
        use s₁
        intro hs₁
        rw [← this' s₁ hs₁]
        exact (hg' s₁ (Multiset.mem_of_mem_erase hs₁)).1
      have hx₂ : x₂ ∈ I := by
        rw [show x₂ = g' s₀ by simp, hgeq s₀ szeroin]
        exact (hg' s₀ szeroin).1
      rw [show x = x₁ + x₂ by simp]
      exact Ideal.add_mem _ hx₁ hx₂
    by_contra hfalse
    push_neg at hfalse
    rcases hfalse with ⟨s, hs1, hs2⟩
    by_cases hseqszero : s = s₀
    rw [hseqszero] at hs2
    apply xonenotin
    rw [show x₁ = x - x₂ by simp]
    exact Ideal.sub_mem _ hs2 xtwoin
    apply xtwonotin s
    exact (Multiset.mem_erase_of_ne hseqszero).mpr hs1
    rw [show x₂ = x - x₁ by simp]
    exact Ideal.sub_mem _ hs2 (xonein s ((Multiset.mem_erase_of_ne hseqszero).mpr hs1))
