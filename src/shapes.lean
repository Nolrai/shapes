import data.set
import data.matrix.basic
import data.set.finite
import data.fincard
import order.basic
import tactic

section point

parameters {dim : nat}

abbreviation point := fin dim → ℚ
def point.dot : point → point → ℚ := λ x y, matrix.dot_product x y

abbreviation direction := {p : point // p.dot p = (1 : ℚ)}

abbreviation support_function := {s : direction → point // ∀ d₁ d₂ : direction, (s d₂).dot d₁ ≤ (s d₁).dot d₁}

def support_function.hull (s : support_function) : set point := (λ p : point, ∀ d : direction, d.val.dot d ≤ (s.val d).dot d)

def support_function.range (s : support_function) := s.val '' set.univ

instance : has_mem point support_function := ⟨λ p s, p ∈ s.hull⟩ 

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

section get_maximum_by
parameters {α β : Type} [linear_order β] (f : α → β)

def get_maximum_by.aux_aux (new : α) (old : β × α) : β × α :=
  let new_β := f new in
  if old.1 < new_β
    then (new_β, new)
    else old

lemma get_maximum_by.aux_aux.def (x y : α) : 
  get_maximum_by.aux_aux x (f y, y) =
  if f y < f x
    then (f x, x)
    else (f y, y) := rfl

lemma get_maximum_by.aux_aux.or (x : α) (y) : get_maximum_by.aux_aux x (f y, y) ∈ [(f x, x), (f y, y)] := 
  by {
    rw get_maximum_by.aux_aux.def,
    split_ifs,
    {left, refl},
    {right, left, refl}
  }

lemma get_maximum_by.aux_aux.le_fx (x y : α) : f x ≤ f (get_maximum_by.aux_aux x (f y, y)).2 :=
  by {
    rw get_maximum_by.aux_aux.def,
    split_ifs,
    {refl},
    {apply le_of_not_lt h},
  }

lemma get_maximum_by.aux_aux.le_fy (x y : α) : f y ≤ f (get_maximum_by.aux_aux x (f y, y)).2 :=
  by {
    rw get_maximum_by.aux_aux.def,
    split_ifs,
    {apply le_of_lt h},
    {refl}
  }

def get_maximum_by.aux (x : β × α) (xs : list α) := list.foldr get_maximum_by.aux_aux x xs 

lemma get_maximum_by.aux.def (x xs) : get_maximum_by.aux x xs = list.foldr get_maximum_by.aux_aux x xs := rfl

lemma get_maximum_by.aux.in_l.aux (n : ℕ) : ∀ x (xs : list α), 
  xs.length = n → 
  (get_maximum_by.aux (f x, x) xs) ∈ ((x::xs).map (λ y : α, (f y, y))) :=
  by {
    simp_rw get_maximum_by.aux.def,
    induction n; intros x xs h,
    case zero {rw list.length_eq_zero at h, rw h, simp},
    case succ {
      cases xs with y ys, 
      case list.nil {
        rw list.foldr_nil,
        rw list.map_singleton,
        apply list.mem_cons_self,
      },
      case list.cons {
        rw list.foldr_cons,
        have : list.foldr get_maximum_by.aux_aux (f x, x) ys ∈ list.map (λ y, (f y, y)) (x :: ys),
        apply n_ih,
        rw list.length_cons at h,
        apply (add_left_inj 1).mp h,
        clear h n_ih n_n,
        cases this,
        rw this, clear this,
        have : ((λ (y : α), (f y, y)) x) = (f x, x) := rfl, rw this, clear this,
        have : get_maximum_by.aux_aux y (f x, x) ∈ [(f y, y), (f x, x)],
        apply get_maximum_by.aux_aux.or,
        cases this,
        { 
          rw this,
          simp_rw [list.map_cons],
          {right, left, refl},
        },
        {
          have H : (get_maximum_by.aux_aux y (f x, x)) = (f x, x),
          apply list.mem_singleton.mp,
          apply this, clear this,
          rw H, clear H,
          simp_rw list.map_cons,
          {left, refl},
        },
        {
          rw list.map_cons,
          right,
          have H : (list.foldr get_maximum_by.aux_aux (f x, x) ys) ∈ (list.map (λ (y : α), (f y, y)) ys),
          exact this,
          clear this,
          rw list.mem_map at H,
          rcases H with ⟨z, z_in, f_z_z_is⟩,
          rw ← f_z_z_is,
          have : list.map (λ y, (f y, y)) [y, z] ⊆ list.map (λ (y : α), (f y, y)) (y :: ys),
            {
              clear_except z, 
              apply list.map_subset, 
              intros w h, cases h, 
              {left, exact h}, 
              {right, cases h, rw h, exact z_in, cases h},
            },
          clear_except this,
          apply this, clear this,
          apply get_maximum_by.aux_aux.or,
        }
      },
    },
  }

lemma get_maximum_by.aux.in_l (x xs) : (get_maximum_by.aux (f x, x) xs) ∈ ((x::xs).map (λ y : α, (f y, y))) :=
  by {apply get_maximum_by.aux.in_l.aux (xs.length), refl}

def get_maximum_by : {l : list α // ¬ l.is_nil} → α
  | ⟨x::xs, _⟩ := (get_maximum_by.aux (f x, x) xs).2
  | ⟨[], p⟩ := by {exfalso, apply p, exact list.is_nil_iff_eq_nil.mpr rfl}

lemma get_maximum_by.cons (x xs p) : get_maximum_by ⟨x :: xs, p⟩ = (get_maximum_by.aux (f x, x) xs).2 := rfl

lemma get_maximum_by.in_l : ∀ l : {l : list α // ¬ l.is_nil}, get_maximum_by l ∈ l.val
  | ⟨x::xs, is_not_nil⟩ := by {
      rw get_maximum_by.cons, 
      unfold subtype.val,
      have : (get_maximum_by.aux (f x, x) xs) ∈ ((x::xs).map (λ y : α, (f y, y))), 
        {apply get_maximum_by.aux.in_l},
      cases this,
      rw this,
      unfold prod.snd,
      {left, refl},
      have H : (get_maximum_by.aux (f x, x) xs) ∈ (list.map (λ (y : α), (f y, y)) xs) := this,
      rw list.mem_map at H,
      rcases H with ⟨z, z_in, f_z_z_eq⟩,
      rw ← f_z_z_eq,
      unfold prod.snd,
      {right, exact z_in},
    }
  | ⟨[], p⟩ := by {exfalso, apply p, exact list.is_nil_iff_eq_nil.mpr rfl}

end get_maximum_by

def polygon.val (points : {l : list point // ¬ l.is_nil}) (dir : direction) : point :=
  get_maximum_by (λ p : point, p.dot dir.val) points

lemma polygon.property {dim : ℕ} (points : list point) (d₁ d₂ : direction) :
    (polygon.val points d₂).dot ↑d₁ ≤ (polygon.val points d₁).dot ↑d₁ :=
  by {

  }

def support_function.polygon (points : list point) : support_function :=
  
  {
    val := polygon.val points,
    property := by {extract_goal, }
  }

-- "canon" because you can add (some) points on bounding faces of a simplex to the support function and not change the hull. So the hull of every `s` such that `s.is_canon_simplex` is a simplex, and every simplex has such a support_function, but there are `s` such that `¬ s.is_canon_simplex` and `s.hull` is a simplex.

def support_function.is_canon_simplex (s : support_function) : Prop := enat.card (s.range) ≤ dim + 1

lemma aux (a b : support_function) (s : support_function) (p : point) 
  (s_supports : s.hull = minkowski_diff a.hull b.hull)  (p_in_s : p ∈ s) :
  ∃ s' : support_function, s'.is_canon_simplex ∧ s'.range ⊆ s.range ∧ p ∈ s' :=
  by {

  }

end point