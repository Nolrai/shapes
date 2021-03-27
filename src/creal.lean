import data.rat
import data.quot

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
          suffices : ∃ midpoint, q < midpoint ∧ midpoint < x, 
          { 
            cases this with midpoint, cases this_h with q_lt_midpoint midpoint_lt_x, apply not_le_of_lt midpoint_lt_x, 
            apply all_p, 
            apply q_lt_midpoint
          },
          existsi ((q + x) / 2),
          split; linarith,
        }
    }
  ⟩