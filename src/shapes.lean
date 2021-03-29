import data.set
import data.matrix.basic

section point

parameters {dim : nat}

abbreviation point := fin dim → ℚ
abbreviation point.dot : point → point → ℚ := λ x y, matrix.dot_product x y

abbreviation direction := {p : point // p.dot p = 1}

abbreviation support_function := {s : direction → point // ∀ d₁ d₂ : direction, (s d₂).dot d₁ ≤ (s d₁).dot d₁}

def hull (s : support_function) : set point := (λ p : point, ∀ d : direction, d.val.dot d ≤ (s.val d).dot d)

instance : has_mem point support_function := ⟨λ p s, p ∈ hull s⟩ 

def minkowski_diff (a b : set point) : set point :=
  set.image2 has_sub.sub a b

lemma minkowski_diff.def (a b : set point) : minkowski_diff a b = set.image2 has_sub.sub a b :=
  rfl

lemma minkowski_dif_contains_zero_iff_intersect (a b : set point) :
  (0 : point) ∈ minkowski_diff a b ↔ (a ⊓ b).nonempty :=
  by {
    split; intros h,
    {
      obtain ⟨x, y, a_x, b_y, x_y⟩ := h,
      use x,
      split, {exact a_x},
      rw (sub_eq_zero.mp x_y),
      exact b_y,
    },
    {
      obtain ⟨x, x_a, x_b⟩ := h,
      use [x, x, x_a, x_b],
      exact sub_self x
    }
  }



end point