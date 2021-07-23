import set_theory.ordinal order.bounded_lattice order.zorn data.set.intervals.ord_connected order.rel_iso

open_locale cardinal

set_option old_structure_cmd true

-- A partial order with a least and greatest element.
class bounded_partial_order (α : Type*) extends order_top α, order_bot α

namespace bounded_partial_order
section

parameters (α : Type*) [bl : bounded_lattice α]

instance of_top_bot : bounded_partial_order α :=
{ ..bl }

end
end bounded_partial_order

-- An element `c` covers `a` whenever `a < c` and no face `a < b < c` exists.
def covers {α : Type*} [preorder α] (a c : α) : Prop :=
a < c ∧ ¬ ∃ b, a < b ∧ b < c

-- A graded poset has a function from elements to naturals that's compatible 
-- with the ordering, and consistent with the covering relation. 
class graded (α : Type*) extends order_bot α :=
(grade : α → ℕ)
(grade_bot_eq_zero : grade ⊥ = 0)
(lt_grade_of_lt : ∀ {a b : α}, a < b → grade a < grade b)
(eq_p1_of_cover : ∀ {a b : α}, covers a b → grade a + 1 = grade b)

namespace graded

theorem le_grade_of_le {α : Type*} [graded α] : ∀ {a b : α}, a ≤ b → graded.grade a ≤ graded.grade b :=
begin
  intros a b a_le_b,
  cases lt_or_eq_of_le a_le_b with a_lt_b a_eq_b, {
    exact le_of_lt (@graded.lt_grade_of_lt α _ a b a_lt_b),
  },
  exact (congr_arg grade (eq.symm a_eq_b)).ge,
end

end graded

-- A graded, bounded partial order.
class graded_bounded_partial_order (α : Type*) extends bounded_partial_order α, graded α

set_option old_structure_cmd false

namespace abstract_polytope

variables {α : Type*} [graded_bounded_partial_order α] (f f' : set α)

-- A flag is a maximal chain.
def is_flag (c : set α) : Prop :=
@zorn.is_max_chain _ (<) c

-- Two flags are adjacent when they differ by exactly one element.
def flag_adj : Prop :=
is_flag f → is_flag f' → #(set.diff f f') = 1

-- In a flag, `grade a < grade b` implies `a < b`.
theorem flag_grade_lt_of_lt (a b : α) (ha : a ∈ f) (hb : b ∈ f): is_flag f → graded.grade a < graded.grade b → a < b := 
begin
  intros ff ga_lt_gb,
  cases ff with ch _,
  have h : a ≠ b → a < b ∨ a > b := ch a ha b hb, 
  by_cases a_ne_b : a ≠ b, {
    cases h a_ne_b with a_lt_b b_lt_a, {
      exact a_lt_b,
    },
    have a_lt_b : graded.grade b < graded.grade a := graded.lt_grade_of_lt b_lt_a,
    exact false.elim (nat.lt_asymm ga_lt_gb a_lt_b),
  },
  simp at a_ne_b,
  rw a_ne_b at ga_lt_gb,
  finish,
end

end abstract_polytope

class abstract_polytope (α : Type*) extends (graded_bounded_partial_order α), (set.ord_connected (@set.univ α)) :=
(all_flags_same_card : ∀ {c c' : set α}, abstract_polytope.is_flag c → abstract_polytope.is_flag c' → #c = #c')
(diamond : ∀ {a b : α}, grade a + 2 = grade b → #(set.Ioo a b) = 2)

set_option old_structure_cmd true

namespace abstract_polytope

variables {α : Type*} [abstract_polytope α] (f f' : set α)

def grade : α → ℕ := graded.grade

-- Any flag contains the bottom element `⊥`.
theorem bot_in_flag : is_flag f → ⊥ ∈ f :=
begin
  -- We add `⊥` to the flag. 
  intro ff,
  by_contra,
  let f' : set α := f ∪ {⊥},
  have hf' : ∀ a ∈ f', a ∈ f ∨ a = ⊥ := by simp,
    
  -- f is not equal to f'.
  have f_ne_f' : f ≠ f' := begin
    intro f_eq_f',
    rw f_eq_f' at h,
    exact h (set.mem_union_right f rfl),
  end,

  -- f is a strict subset of f'.
  have f_in_f' : f ⊂ f' := set.ssubset_iff_subset_ne.mpr ⟨set.subset_union_left f {⊥}, f_ne_f'⟩,

  -- We prove that `f'` is a super chain of `f`.
  have h₁ : @zorn.super_chain _ (<) f f' := begin
    split, {
      intros a af' b bf' a_ne_b,

      -- Cases depending on whether `a` or `b` equal `⊥`. 
      cases hf' a af' with af a_eq_t, {
        cases hf' b bf' with bf b_eq_t, {
          exact ff.left a af b bf a_ne_b,
        },
        rw b_eq_t at *,
        exact or.inr ((ne.symm a_ne_b).le_iff_lt.mp bot_le),        
      },
      rw a_eq_t at *,
      exact or.inl (bot_lt_iff_ne_bot.mpr (ne.symm a_ne_b)),      
    },

    exact f_in_f',
  end,

  -- We then prove that `f` is not a max chain.
  have h₂ : ¬ @zorn.is_max_chain _ (<) f := begin
    by_contra, exact h.right ⟨f', h₁⟩,
  end,

  -- But this contradicts the definition of a flag.
  exact h₂ ff,
end

-- The set of grades of a flag.
def flag_grades : set ℕ := {n | ∃ a ∈ f, grade a = n}

-- A flag contains faces of each grade up to the grade of its topmost face.
theorem flag_grades_Iic : is_flag f → flag_grades f = set.Iic (grade (⊤ : α)) :=
begin
  intro ff,
  let G := flag_grades f,
  let N := grade (⊤ : α),
  let I := set.Iic N,

  -- Every flag grade is between 0 and N.
  have G_in_I : G ⊆ I := begin
    intros _ g_mem_G,
    cases g_mem_G with a ha, 
    cases ha with a_in_f ga_eq_f,
    have ga_lt_N : grade a ≤ N := graded.le_grade_of_le le_top,
    rw ga_eq_f at ga_lt_N,
    exact ga_lt_N,
  end,

  -- Every number between 0 and N is a flag grade.
  have I_in_G : I ⊆ G := begin
    intros n n_mem_I,
    by_contra n_nmem_G,

    have hm : ∃ m : ℕ, m ∈ G ∧ m < n ∧ ∀ k : ℕ, k ∈ set.Ioo m n → k ∉ G := begin
      let S := set.Iic n ∩ G,
      let Sf := set.finite.to_finset (set.finite.inf_of_left (set.finite_le_nat n) G),
      have Sn : Sf.nonempty := begin
        have h : 0 ∈ Sf := begin
          rw set.finite.mem_to_finset,
          split, {
            exact zero_le n,
          },
          exact ⟨⊥, bot_in_flag f ff, graded.grade_bot_eq_zero⟩,
        end,
        exact ⟨0, h⟩,
      end,
      let m := finset.max' Sf Sn,
      use m,
      sorry,
    end,
    cases hm with m hm,
    cases hm with m_in_G hm,
    cases hm with m_le_n hm,
    cases m_in_G with a ha,
    cases ha with a_mem_f ga_eq_m,

    have hM : ∃ M : ℕ, M ∈ G ∧ n < M ∧ ∀ k : ℕ, k ∈ set.Ioo n M → k ∉ G := sorry,
    cases hM with M hM,
    cases hM with M_in_G hM,
    cases hM with n_le_M hM,
    cases M_in_G with b hb,
    cases hb with b_mem_f gb_eq_M,

    have c : covers a b := begin
      split, {

      }
    end,
    have h₁ : m.succ = N := sorry,
    have h₂ : m.succ < N := sorry,
    finish,
  end,

  exact set.subset.antisymm G_in_I I_in_G,
end

-- No two elements in a flag have the same grade,
theorem flag_grade_inj (a b ∈ f) : is_flag f → grade a = grade b → a = b := 
begin
  -- Flags are total orders.
  intro ff,
  contrapose,
  intro hab,
  have h : a < b ∨ a > b := ff.left _ ‹_› _ ‹_› hab,

  -- `a` can be neither less nor greater than `b`.
  cases h with hl hg,
  {
    apply ne_of_lt,
    exact graded.lt_grade_of_lt hl,
  },
  {
    apply ne_of_gt,
    exact graded.lt_grade_of_lt hg,
  }
end

-- Flag adjacency in an abstract polytope is commutative.
theorem flag_adj_comm : is_flag f → is_flag f' → flag_adj f f' → flag_adj f' f :=
begin
  intros ff ff',
  sorry,
end

-- Any nontrivial section contains a vertex.
theorem section_vertex (a b : α) : b < a → ∃ c ∈ set.Icc b a, covers b c :=
begin
  -- Set up an induction on (grade a), which can almost certainly be done more elegantly
  let m := nat.succ (grade a),
  have grade_a_m_succ : grade a < m,
  {
    apply lt_add_one,
  },
  revert grade_a_m_succ,
  generalize : m = n,
  clear m,
  revert a b,
  induction n with n ih,
  {
    intros a b grade_a_lt_zero,
    cases nat.not_lt_zero _ grade_a_lt_zero,
  },
  intros a b grade_a_n_succ b_lt_a,
  -- Is there something between a and b?
  by_cases ∃ c : α, b < c ∧ c < a,
  {
    -- Yes, try to find a cover between that and b.
    cases h with c h,
    cases h with b_lt_c c_lt_a,
    have h : ∃ (d ∈ set.Icc b c), covers b d,
    {
      apply ih,
      {
        let grade_c_lt_grade_a := graded.lt_grade_of_lt c_lt_a,
        have grade_a_le_n : grade a ≤ n,
        {
          exact nat.le_of_lt_succ grade_a_n_succ,
        },
        exact nat.lt_of_lt_of_le grade_c_lt_grade_a grade_a_le_n,
      },
      exact b_lt_c,
    },
    cases h with d h,
    use d,
    cases h with d_between_b_a covers_b_d,
    split,
    {
      rewrite set.mem_Icc,
      rewrite set.mem_Icc at d_between_b_a,
      cases d_between_b_a with b_le_d d_le_c,
      split,
      {
        exact b_le_d,
      },
      exact le_trans d_le_c (le_of_lt c_lt_a),
    },
    exact covers_b_d,
  },
  -- No, so a is covering.
  use a,
  split,
  {
    rewrite set.mem_Icc,
    split,
    {
      exact le_of_lt b_lt_a,
    },
    apply le_refl,
  },
  split,
  {
    exact b_lt_a,
  },
  exact h,
end
end abstract_polytope
