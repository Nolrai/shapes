import data.rat
import data.quot
import topology.basic

structure computable_real := 
  (cut : rat → bool)
  (monotonic : ∀ p q, p ≤ q → cut p ≤ cut q)
  (bounded_above : ∃ q, cut q = true)
  (bounded_below : ∃ q, cut q = false)
  (sharp : ∀ q, (∀ p, q < p → cut p) → cut q)

abbreviation ℝ := computable_real

lemma imp_to_le (P Q : Prop) [p : decidable P] [q : decidable Q] (H : P → Q) : 
  to_bool P ≤ to_bool Q :=
  match p, q with
  | is_false p', _ := bool.ff_le
  | is_true p', is_true q' := le_refl true
  | is_true p', is_false q' := false.rec _ (q' (H p'))
  end


lemma exists_midpoint (p q : ℚ) (p_lt_q : p < q) : ∃ x, p < x ∧ x < q :=
  ⟨(p + q)/2, by {split; linarith}⟩

instance : has_coe ℚ ℝ :=
  ⟨ λ x,
    {
      cut := λ p, x ≤ p,
      monotonic := λ p q p_le_q, imp_to_le _ _ (λ H, le_trans H p_le_q),
      bounded_above := ⟨x, by {congr, rw eq_true}⟩,
      bounded_below := ⟨x - 1, by {congr, rw eq_false, linarith}⟩,
      sharp := λ q, by 
        { 
          simp_rw bool.coe_to_bool, 
          intros all_p, 
          apply le_of_not_lt, 
          intro q_lt_x, 
          have : ∃ midpoint, q < midpoint ∧ midpoint < x := exists_midpoint _ _ q_lt_x,
          cases this with midpoint, cases this_h with q_lt_midpoint midpoint_lt_x, apply not_le_of_lt midpoint_lt_x, 
          apply all_p, 
          apply q_lt_midpoint
        },
    },
  ⟩

section by_continuousness 

def rat.open_disk (center : ℚ) (radius : {r : ℚ // 0 < r}) : set ℚ := 
  λ x, center - radius < x ∧ x < center + radius

lemma open_disk_monotonic (q : ℚ) (r₁ r₂ : {r : ℚ // 0 < r}) : 
  r₁ ≤ r₂ ↔ q.open_disk r₁ ⊆ q.open_disk r₂ :=
  by {
    unfold rat.open_disk,
    split; intro h,
    {
      intros x,
      unfold has_mem.mem set.mem,
      intro in_disk₁,
      cases in_disk₁,
      obtain ⟨r₁, r₁_pos⟩ := r₁,
      obtain ⟨r₂, r₂_pos⟩ := r₂,
      unfold_coes at *, simp at *,
      split,
        exact lt_of_le_of_lt (sub_le_sub_left h q) in_disk₁_left,
        exact lt_of_lt_of_le in_disk₁_right (add_le_add_left h q),
    },
    {
      unfold has_subset.subset set.subset has_mem.mem set.mem at h,
      apply le_of_not_lt,
      intro r₂_lt_r₁,
      obtain ⟨midpoint, r₂_lt_midpoint, midpoint_lt_r₁⟩ := exists_midpoint _ _ r₂_lt_r₁,
      have H : q + midpoint < q + ↑r₂, suffices H' : q - ↑r₂ < q + midpoint ∧ q + midpoint < q + ↑r₂, 
      exact H'.right,
      {
        cases r₁, cases r₂, repeat {rw subtype.coe_mk at *}, rw subtype.mk_lt_mk at *,
        simp at r₂_lt_midpoint,
        simp at midpoint_lt_r₁,
        apply @h (q + midpoint),
        split, linarith,
        exact add_lt_add_left midpoint_lt_r₁ q,
      },
      simp at H,
      have imposible : r₂ < r₂, 
      {
        cases r₂,
        rw subtype.mk_lt_mk,
        rw subtype.val_eq_coe at r₂_lt_midpoint,
        rw subtype.coe_mk at *,
        exact lt_trans r₂_lt_midpoint H,
      },
      apply lt_irrefl _ imposible,
    }
  }

example (α : Type) (s : set α) : s ⊆ set.univ := set.subset_univ s

lemma aux {α} {s l' r' : set α} {l r} : (s ⊆ l) → (s ⊆ r) → (l ⊆ l') → (r ⊆ r') → s ⊆ l' ∩ r' :=
  by {
    intros s_l s_r l_l' r_r',
    simp; split,
    transitivity' l; assumption,
    transitivity' r; assumption,
  }

example (α) (s : set (set α)) (t : set α) : t ∈ s → t ⊆ ⋃₀ s := by refine set.subset_sUnion_of_mem

instance : topological_space ℚ :=
  {
    is_open := λ s, ∀ q : ℚ, q ∈ s → ∃ r, q.open_disk r ⊆ s,
    is_open_univ := λ q _, ⟨⟨(1 : ℚ), zero_lt_one⟩, set.subset_univ _⟩,
    is_open_inter := λ s t s_open t_open q q_in_s_inter_t, 
      by {
        have q_in_s : q ∈ s := set.mem_of_mem_inter_left q_in_s_inter_t,
        have q_in_t : q ∈ t := set.mem_of_mem_inter_right q_in_s_inter_t,
        obtain ⟨⟨r_s, h_s_lt⟩, h_s_sub⟩ := s_open q q_in_s,
        obtain ⟨⟨r_t, h_t_lt⟩, h_t_sub⟩ := t_open q q_in_t,
        exact ⟨ (⟨min r_s r_t, lt_min h_s_lt h_t_lt⟩ : {r : ℚ // 0 < r}),
        by {
        apply aux _ _ h_s_sub h_t_sub; apply (open_disk_monotonic _ _ _).mp; rw subtype.mk_le_mk,
        exact min_le_left r_s r_t, 
        exact min_le_right r_s r_t,
        }⟩,
      },
    is_open_sUnion := 
      by {
        intros family items_are_open q q_in_union,
        obtain ⟨t, t_in_family, q_in_t⟩ := q_in_union,
        obtain ⟨r, r_disk_in_t⟩ := items_are_open t t_in_family q q_in_t,
        use r,
        transitivity t, exact r_disk_in_t,
        apply set.subset_sUnion_of_mem t_in_family,
      },
  }

parameter f : ℚ → ℚ
parameter f_is_continous : continuous f

def lift_to_ℝ : ℝ → ℝ 

end by_continuousness