import data.set
import analysis.convex.basic
import analysis.normed_space.inner_product
import algebra.big_operators.basic

namespace array

def zip_with {α β γ : Type} {n} (x : array n α) (f : α → β → γ) (y : array n β) : array n γ := 
  ⟨λ i, f (x.data i) (y.data i)⟩

@[simp]
lemma zip_with_read {α β γ : Type} {n : ℕ} (f : α → β → γ) (x : array n α) (y : array n β) {i : fin n} : 
  (zip_with x f y).read i = f (x.read i) (y.read i) := rfl

def sum {α} [add_monoid α] {n} (x : array n α) : α := x.foldl 0 (+)

@[simp]
lemma sum_zero {α} [add_monoid α] (x : array 0 α) : x.sum = 0 := rfl

@[simp]
lemma sum_succ {α} [add_monoid α] (n : ℕ) (x : array (n+1) α) : x.sum = (x.pop_back).sum + x.read (fin.last n) := 
  by {
    unfold sum,
    unfold foldl,
    unfold pop_back iterate d_array.iterate,
    simp,
  }

end array

section point

parameters {dim : nat}

abbreviation point := array dim ℚ

instance : has_add point := ⟨λ x y, x.zip_with (+) y⟩
instance : has_zero point := ⟨⟨λ i, 0⟩⟩
instance : has_neg point := ⟨λ p, p.map has_neg.neg⟩
instance : add_comm_group point :=
  {
    add_assoc := by {
      intros x y z,
      unfold has_add.add,
      ext,
      simp,
      apply add_assoc,
    },
    zero_add := λ x, array.ext (λ (i : fin dim), zero_add (x.data i)),
    add_zero := λ x, array.ext (λ (i : fin dim), add_zero (x.data i)),
    add_left_neg := λ x, array.ext (λ i, add_left_neg (x.data i)),
    add_comm := λ x y, array.ext (λ i, add_comm (x.data i) (y.data i)),
    .. point.has_add,
    .. point.has_zero,
    .. point.has_neg
  }

instance : has_scalar ℚ point := ⟨λ r p, ⟨λ i, r * p.data i⟩⟩ 

def point.semimodule.core  : semimodule.core ℚ point :=
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

instance : vector_space ℚ point := semimodule.of_core point.semimodule.core

abbreviation point.dot_aux (x y : point) : ℚ := (x.zip_with (*) y).sum

lemma dot_add_left (x y z : point) : point.dot_aux (x + y) z = (x.dot_aux z) + (y.dot_aux z) :=
  by {
    unfold array.sum,
  }

def dot : bilin_form ℚ point :=
  {
    bilin := point.dot_aux,
    bilin_add_left := _,
  }
     

end GJK

end