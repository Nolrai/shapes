import data.set
import analysis.convex.basic
import analysis.normed_space.inner_product

section GJK

parameters (n : nat)

abbreviation point := array n ℝ

instance : has_add point := ⟨λ x y, ⟨λ i, x.data i + y.data i⟩⟩   
instance : has_zero point := ⟨⟨λ i, 0⟩⟩
instance : has_neg point := ⟨λ p, ⟨λ i, - p.data i⟩⟩
instance : add_comm_group point :=
  {
    add_assoc := by {
      intros x y z,
      unfold has_add.add,
      congr,
      ext,
      apply add_assoc,
    },
    zero_add := λ x, array.ext (λ (i : fin n), zero_add (x.data i)),
    add_zero := λ x, array.ext (λ (i : fin n), add_zero (x.data i)),
    add_left_neg := λ x, array.ext (λ i, add_left_neg (x.data i)),
    add_comm := λ x y, array.ext (λ i, add_comm (x.data i) (y.data i)),
    .. point.has_add,
    .. point.has_zero,
    .. point.has_neg
  }

instance : has_scalar ℝ point := ⟨λ r p, ⟨λ i, r * p.data i⟩⟩ 

def point.semimodule.core  : semimodule.core ℝ point :=
  {
    add_smul := λ r₀ r₁ p, by {
      ext,
      unfold_projs,
      simp,
      unfold array.read d_array.read,
      simp,
      apply right_distrib,
    },
    smul_add := λ r₀ r₁ p, by {
      ext,
      unfold_projs,
      simp,
      unfold array.read d_array.read,
      simp,
      apply left_distrib,
    },
    mul_smul := λ r₀ r₁ p, by {
      ext,
      unfold array.read d_array.read,
      unfold_projs,
      simp,
      apply mul_assoc,
    },
    one_smul := λ x, by {
      ext,
      unfold array.read d_array.read,
      unfold_projs,
      simp,
      apply one_mul,
    },
    .. point.has_scalar
  }

instance : semimodule ℝ point := 

instance : inner_product_space.core ℝ point :=


end