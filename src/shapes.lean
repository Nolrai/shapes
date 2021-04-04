import data.set
import data.matrix.basic
import data.set.finite
import data.fincard
import order.basic
import tactic

abbreviation nonempty_list (α) := {l : list α // ¬ l.is_nil}

section point

parameters (dim : nat)

abbreviation point := fin dim → ℚ

parameters {dim}

def point.dot : point → point → ℚ := λ x y, matrix.dot_product x y

lemma point.dot.def (x y : point) : x.dot y = matrix.dot_product x y := rfl

lemma point.dot.neg_neg (x y : point) : x.dot y = (-x).dot (-y) :=
  by {
    simp_rw point.dot.def, 
    rw matrix.dot_product_neg, 
    rw matrix.dot_product_comm (-x), 
    rw matrix.dot_product_neg,
    rw neg_neg,
    apply matrix.dot_product_comm,
  }

abbreviation direction := {p : point // p.dot p = (1 : ℚ)}

instance : has_neg direction := ⟨λ ⟨p, magnitude_one⟩, ⟨-p, (point.dot.neg_neg p p).symm.trans magnitude_one⟩ ⟩

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

def minkowski_diff_support (a b : support_function) : support_function :=
  { 
    val := λ dir, a.val dir - b.val (-dir),
    property := sorry
  }

end point

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

lemma get_maximum_by.aux.is_maximal.aux (n : ℕ) : ∀ x (xs : list α), 
  xs.length = n → 
  ∀ y, y ∈ x::xs → f y ≤ f (get_maximum_by.aux (f x, x) xs).2 :=
  by {
    simp_rw get_maximum_by.aux.def,
    induction n; intros x xs h y y_in_x_xs,
    case zero {
      rw list.length_eq_zero at h, rw h at *, clear h xs,
      rw list.mem_singleton at y_in_x_xs, rw y_in_x_xs at *, clear y_in_x_xs y,
      rw list.foldr_nil,
    },
    case succ {
      cases xs with z zs,
      case nil {
        unfold list.length at *,
        cases h,
      },
      case cons {
        have n_ih' : y ∈ x :: zs → f y ≤ f (list.foldr get_maximum_by.aux_aux (f x, x) zs).snd,
          {apply n_ih, unfold list.length at h, rw nat.add_one at h, injection h},
        have y_in : y = z ∨ y ∈ x :: zs, 
          { rcases y_in_x_xs with _ | _ | _, 
            {right, left, exact y_in_x_xs}, 
            {left, exact y_in_x_xs},
            {right, right, exact y_in_x_xs},
          },
        rw list.foldr_cons,
        have exists_fw_w : ∃ w, (list.foldr get_maximum_by.aux_aux (f x, x) zs) = (f w, w),
          {
            have H : (list.foldr get_maximum_by.aux_aux (f x, x) zs) ∈ list.map (λ t, (f t, t)) (x :: zs),
            {
              have H : get_maximum_by.aux (f x, x) zs ∈ (x::zs).map (λ y : α, (f y, y)) := 
                by {apply get_maximum_by.aux.in_l},
              rw get_maximum_by.aux.def at H,
              exact H,
            },
            clear_except H,
            cases H, 
              {use x, apply H},
              { 
                have H : list.foldr get_maximum_by.aux_aux (f x, x) zs ∈ list.map (λ (t : α), (f t, t)) zs := H, 
                rw list.mem_map at H,
                rcases H with ⟨a, a_in_zs, f_a_a_eq⟩,
                use a, symmetry, exact f_a_a_eq,
              },
          },
        obtain ⟨w, fw_w⟩ := exists_fw_w,
        rw fw_w,
        cases y_in,
        case inl {
          transitivity (f z), {rw y_in},
          apply get_maximum_by.aux_aux.le_fx,
        },
        case inr {
          have HH := n_ih' y_in,
          transitivity (f w),
          rw fw_w at HH,
          apply HH,
          apply get_maximum_by.aux_aux.le_fy,
        },
      },
    },
  }

lemma get_maximum_by.aux.is_maximal (x xs) (y) (y_in_l :y ∈ x::xs) : f y ≤ f (get_maximum_by.aux (f x, x) xs).2 :=
  get_maximum_by.aux.is_maximal.aux (list.length xs) x xs (eq.refl _) y y_in_l

def get_maximum_by : {l : list α // ¬ l.is_nil} → α
  | ⟨x::xs, _⟩ := (get_maximum_by.aux (f x, x) xs).2
  | ⟨[], p⟩ := by {exfalso, apply p, exact list.is_nil_iff_eq_nil.mpr rfl}

lemma get_maximum_by.cons (x xs p) : get_maximum_by ⟨x :: xs, p⟩ = (get_maximum_by.aux (f x, x) xs).2 := rfl

lemma get_maximum_by.in_l : ∀ l : nonempty_list α, get_maximum_by l ∈ l.val
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
  | ⟨[], p⟩ := false.rec _ (p (list.is_nil_iff_eq_nil.mpr rfl))

lemma get_maximum_by.is_maximal : ∀ (l : nonempty_list α) (x : α), (x ∈ l.val) → f x ≤ f (get_maximum_by l)
  | ⟨x::xs, is_not_nil⟩ := by {
      rw get_maximum_by.cons,
      unfold subtype.val,
      exact get_maximum_by.aux.is_maximal x xs
    }

  | ⟨[], p⟩ := λ _, false.rec _ (p (list.is_nil_iff_eq_nil.mpr rfl))

end get_maximum_by

def polygon.val {n} (points : nonempty_list (point n)) (dir : direction) : point n :=
  get_maximum_by (λ p : point n, p.dot dir.val) points

lemma polygon.val.def {n} (points : nonempty_list (point n)) (dir) 
  : polygon.val points dir = get_maximum_by (λ p : point n, p.dot dir.val) points :=
  rfl

lemma polygon.property {n : ℕ} (points : nonempty_list (point n)) (d₁ d₂ : direction) :
    (polygon.val points d₂).dot ↑d₁ ≤ (polygon.val points d₁).dot ↑d₁ :=
  by {
    simp_rw polygon.val.def,
    apply get_maximum_by.is_maximal (λ p : (point n), p.dot ↑d₁ ) points _,
    apply get_maximum_by.in_l,
  }

def support_function.polygon {n} (points : nonempty_list (point n)) : support_function :=
  {
    val := polygon.val points,
    property := polygon.property points
  }

-- "canon" because you can add (some) points on bounding faces of a simplex to the support function and not change the hull. So the hull of every `s` such that `s.is_canon_simplex` is a simplex, and every simplex has such a support_function, but there are `s` such that `s.hull` is a simplex `¬ s.is_canon_simplex` and

def support_function.is_canon_simplex {dim} (s : @support_function dim) : Prop := enat.card (s.range) ≤ dim + 1

section GJK

parameters {dim : ℕ} (a b : @support_function dim)

namespace GJK

def getNextPoint (dir) : point dim := (minkowski_diff_support a b).val dir

def nearestSimplex (simplex : list (point dim)) : list (point dim) × @direction dim × bool := sorry

def loop : @direction dim → list (point dim) → bool
  | dir simplex :=
    let a : point dim := getNextPoint dir in
    if a.dot dir.val < 0
      then ff
      else match nearestSimplex simplex with
        | (_, _, tt) := tt
        | (simplex', dir', ff) := loop dir simplex
      end
  using_well_founded _

def start (dir : @direction dim) : bool := 
  let nextPoint := getNextPoint dir in
  let simplex := [nextPoint] in
  loop (-dir) simplex

def GJK.aux  : (0 : point _) ∈ minkowski_diff a.hull b.hull

def GJK {dim} (a b : @support_function dim) : (∃ p : point dim, p ∈ a ∧ p ∈ b) ∨ ¬ (∃ p : point dim, p ∈ a ∧ p ∈ b) :=