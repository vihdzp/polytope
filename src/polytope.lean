import tactic set_theory.ordinal order.bounded_lattice order.zorn data.set.intervals.ord_connected order.rel_iso

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

variables {α : Type*} [graded_bounded_partial_order α] {f f' : set α}

-- A flag is a maximal chain.
def is_flag (c : set α) : Prop :=
@zorn.is_max_chain _ (<) c

-- Two flags are adjacent when they differ by exactly one element.
def flag_adj : Prop :=
is_flag f → is_flag f' → #(set.diff f f') = 1

-- In a flag, `grade a < grade b` implies `a < b`.
theorem flag_grade_lt_of_lt {a b : α} (ha : a ∈ f) (hb : b ∈ f): is_flag f → graded.grade a < graded.grade b → a < b := 
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

-- If one attempts to extend a flag `f` by an element `e` which is comparable to
-- all other faces of the flag, we obtain a contradiction. 
lemma flag_extend (e : α) : is_flag f → e ∉ f → ¬(∀ a ∈ f, a ≠ e → a < e ∨ e < a) :=
begin
  -- We define `f' = f ∪ {e}`.
  intros ff e_nmem_f h,
  let f' := f ∪ {e},
  have hf' : ∀ a ∈ f', a ∈ f ∨ a = e := by simp,
  apply ff.right,
  use f',
    
  -- `f` is not equal to `f'`.
  have f_ne_f' : f ≠ f' := begin
    intro f_eq_f',
    rw f_eq_f' at e_nmem_f,
    exact e_nmem_f (set.mem_union_right f rfl),
  end,
  
  -- We prove that `f'` is a super chain of `f`, a contradiction!
  split, {
    intros a a_mem_f' b b_mem_f' a_ne_b,

    -- Cases depending on whether `a` or `b` equal `e`. 
    cases hf' a a_mem_f' with a_mem_f a_eq_t, {
      cases hf' b b_mem_f' with b_mem_f b_eq_t, {
        exact ff.left a a_mem_f b b_mem_f a_ne_b,
      },
      rw b_eq_t at *,
      exact h a a_mem_f a_ne_b,
    },
    cases hf' b b_mem_f' with b_mem_f b_eq_t, {
      rw a_eq_t at *,
      exact or.swap (h b b_mem_f (ne.symm a_ne_b)),   
    },
    rw b_eq_t at *,
    exact false.elim (a_ne_b a_eq_t),
  },

  exact set.ssubset_iff_subset_ne.mpr ⟨set.subset_union_left f {e}, f_ne_f'⟩,
end

-- Any flag contains the bottom face `⊥`.
theorem bot_in_flag : is_flag f → ⊥ ∈ f :=
begin
  -- We use the `flag_extend` lemma.
  intro ff,
  by_contra bot_nmem_f,
  apply flag_extend f ⊥ ff bot_nmem_f,

  -- The bottom face is less or equal to any other.
  intros a a_mem_f a_ne_bot,
  exact or.inr (lt_of_le_of_ne bot_le (ne.symm a_ne_bot)),
end

-- Any flag contains the top face `⊤`.
theorem top_in_flag : is_flag f → ⊤ ∈ f :=
begin
  -- We use the `flag_extend` lemma.
  intro ff,
  by_contra bot_nmem_f,
  apply flag_extend f ⊤ ff bot_nmem_f,

  -- The top face is greater or equal to any other.
  intros a a_mem_f a_ne_bot,
  exact or.inl (lt_of_le_of_ne le_top (a_ne_bot)),
end

-- The set of grades of a flag.
def flag_grades : set ℕ := {n | ∃ a ∈ f, grade a = n}

-- If a flag contains `a` and `c` but no elements in between, `grade a + 1 = grade c`.
-- This strengthens `eq_p1_of_covers`.
lemma flag_eq_p1_of_covers (a c : α) (a_mem_f : a ∈ f) (c_mem_f : c ∈ f) : is_flag f → a < c → (¬ ∃ b ∈ f, a < b ∧ b < c) → grade a + 1 = grade c :=
begin
  -- It suffices to prove that `a` covers `c`.
  intros ff a_lt_c hne,
  apply graded.eq_p1_of_cover,  
  use flag_grade_lt_of_lt a_mem_f c_mem_f ff (graded.lt_grade_of_lt a_lt_c),
  
  -- To do this, we prove that any element between `a` and `c` must be in `f`.
  by_contra he,
  cases he with b a_mem_ibc,
  apply hne,
  use b,
  split, {
    -- To use the `flag_extend` lemma, we must prove that any `x ∈ f` is
    -- comparable to `b`.
    by_contra b_nmem_f,
    apply flag_extend f b ff b_nmem_f,
    intros x x_mem_f _,

    -- We use that flags are total orders.
    have nle_of_lt : ∀ a b ∈ f, ¬ b ≤ a → a < b := begin
      intros a b a_mem_f b_mem_f h,

      have a_ne_b : a ≠ b := begin
        intro a_eq_b,
        rw a_eq_b at h,
        exact h rfl.ge,
      end,

      have a_nge_b : ¬ a > b := begin
        intro a_gt_b,
        exact h (le_of_lt a_gt_b),
      end,

      cases ff.left a a_mem_f b b_mem_f a_ne_b with ra rb, {
        exact ra,
      },
      exact false.elim (a_nge_b rb),
    end,

    -- `x` must be below `a` or above `c` (since there's no elements in between).
    have x_le_a_or_c_le_x : x ≤ a ∨ c ≤ x := begin
      by_cases x_le_a : x ≤ a, {
        exact or.inl x_le_a,
      },
      by_cases c_le_x : c ≤ x, {
        exact or.inr c_le_x,
      },
      
      by_contra,
      have a_lt_x := nle_of_lt a x a_mem_f x_mem_f x_le_a,
      have x_lt_c := nle_of_lt x c x_mem_f c_mem_f c_le_x,
      exact hne ⟨x, x_mem_f, a_lt_x, x_lt_c⟩,
    end,

    -- We finish by transitivity.
    cases x_le_a_or_c_le_x with x_le_a c_le_x, {
      exact or.inl (lt_of_le_of_lt x_le_a a_mem_ibc.left),
    },
    exact or.inr (lt_of_lt_of_le a_mem_ibc.right c_le_x),
  }, 

  exact a_mem_ibc,  
end

-- A flag contains faces of each grade up to the grade of its topmost face.
theorem flag_grades_Iic : is_flag f → flag_grades f = set.Iic (grade (⊤ : α)) :=
begin
  intro ff,
  let G := flag_grades f,
  let N := grade (⊤ : α),
  let I := set.Iic N,

  -- Every flag grade is between `0` and `N`.
  have G_in_I : G ⊆ I := begin
    intros _ g_mem_G,
    cases g_mem_G with a ha, 
    cases ha with a_in_f ga_eq_f,
    have ga_lt_N : grade a ≤ N := graded.le_grade_of_le le_top,
    rw ga_eq_f at ga_lt_N,
    exact ga_lt_N,
  end,

  -- Every number between `0` and `N` is a flag grade.
  have I_in_G : I ⊆ G := begin
    -- We suppose, by contradiction, that we're missing a number `n`.
    intros n n_mem_I,
    by_contra n_nmem_G,

    -- We build the intersection `[0, n] ∩ G` and prove that it's finite and non-empty.
    let Sm := (set.Iic n) ∩ G,
    let Sm_finite : Sm.finite := set.finite.inf_of_left (set.finite_le_nat n) G,
    let Sm_finset := set.finite.to_finset Sm_finite,
    have Sm_finset_non : Sm_finset.nonempty := begin
      use 0,
      rw set.finite.mem_to_finset,
      exact ⟨zero_le n, ⟨⊥, bot_in_flag f ff, graded.grade_bot_eq_zero⟩⟩,
    end,

    -- We build the largest grade in `G` that's lesser than `n`.
    let m := Sm_finset.max' Sm_finset_non,
    have m_mem_Sm := (set.finite.mem_to_finset Sm_finite).mp (Sm_finset.max'_mem Sm_finset_non),
    cases m_mem_Sm with m_le_n m_mem_G,
    have m_lt_n : m < n := begin
      apply lt_of_le_of_ne,
      apply m_le_n,
      by_contra m_eq_n,
      have h : m = n ↔ ¬ m ≠ n := not_not.symm,
      rw ←h at m_eq_n,
      rw ←m_eq_n at n_nmem_G,
      exact n_nmem_G m_mem_G,
    end,

    -- We prove that no grades in `(m, n)` may appear in `G`.
    have hm : ∀ k : ℕ, k ∈ set.Ioo m n → k ∉ G := begin
      intros k k_mem_i,
      by_contra k_mem_G,
      have k_le_m : k ≤ m := begin
        apply finset.le_max',
        apply set.mem_to_finset.mpr,
        exact set.mem_sep (set.mem_Iic.mpr (le_of_lt k_mem_i.right)) k_mem_G,
      end,
      exact false.elim (not_lt.mpr k_le_m k_mem_i.left),
    end,

    -- We build the intersection `[n, ∞] ∩ G`.
    let SM := (set.Ici n) ∩ G,
    have SM_non : SM.nonempty := ⟨N, set.mem_inter n_mem_I ⟨⊤, top_in_flag f ff, rfl⟩⟩,

    -- We build the smallest grade in `G` that's greater than `N`.
    let M : ℕ := well_founded.min nat.lt_wf SM SM_non,
    have M_mem_SM := nat.lt_wf.min_mem SM SM_non,
    cases M_mem_SM with n_le_M M_mem_G,
    have n_lt_M : n < M := begin
      apply lt_of_le_of_ne,
      apply n_le_M,
      by_contra n_eq_M,
      have h : n = M ↔ ¬ n ≠ M := not_not.symm,
      rw ←h at n_eq_M,
      rw n_eq_M at n_nmem_G,
      exact n_nmem_G M_mem_G,
    end,

    -- We prove that no grades in `[n, M)` may appear in `G`.
    have hM : ∀ k : ℕ, k ∈ set.Ico n M → k ∉ G := begin
      intros k k_mem_i,
      by_contra k_mem_G,
      have k_ge_m : k ≥ M := begin
        apply le_of_not_lt,
        apply well_founded.not_lt_min nat.lt_wf SM SM_non,
        exact set.mem_sep (set.mem_Ici.mpr k_mem_i.left) k_mem_G,
      end,
      exact false.elim (not_lt.mpr k_ge_m k_mem_i.right),
    end,

    -- `m < M`, obviously.
    have m_lt_M : m < M := lt_trans m_lt_n n_lt_M,
    
    -- We build faces `a` and `c` in the flag with grades `m` and `M`.
    cases m_mem_G with a ea,
    cases M_mem_G with c ec,
    cases ea with a_mem_f ga_eq_m,
    cases ec with c_mem_f gc_eq_M,

    -- `a` must be less than `c`.
    have ga_eq_m : grade a = m := ga_eq_m,
    have gc_eq_M : grade c = M := gc_eq_M,
    have a_lt_c : a < c := begin
      rw ←ga_eq_m at m_lt_M,
      rw ←gc_eq_M at m_lt_M,
      exact flag_grade_lt_of_lt a_mem_f c_mem_f ff m_lt_M,
    end,

    -- There can't exist any face in the flag that's between `a` and `c`.
    have h : ¬ ∃ b ∈ f, a < b ∧ b < c := begin
      intro he,
      cases he with b he,
      cases he with b_mem_f a_lt_b_and_b_lt_c,
      cases a_lt_b_and_b_lt_c with a_lt_b b_lt_c,

      let g := grade b,
      have m_lt_g : m < g := begin
        rw ←ga_eq_m,
        exact graded.lt_grade_of_lt a_lt_b,
      end,
      have g_lt_M : g < M := begin
        rw ←gc_eq_M,
        exact graded.lt_grade_of_lt b_lt_c,
      end,
      have g_mem_G : g ∈ G := ⟨b, b_mem_f, rfl⟩,
      by_cases g_lt_n : g < n, {
        exact hm g (set.mem_inter m_lt_g g_lt_n) g_mem_G,
      },
      exact hM g (set.mem_inter (le_of_not_gt g_lt_n) g_lt_M) g_mem_G,
    end,

    -- As a consequence, `m + 1 = M`.
    have ga_p1_eq_gc : grade a + 1 = grade c := flag_eq_p1_of_covers f a c a_mem_f c_mem_f ff a_lt_c h,
    have m_p1_eq_M : m + 1 = M := begin
      rw ga_eq_m at ga_p1_eq_gc,
      rw gc_eq_M at ga_p1_eq_gc,
      exact ga_p1_eq_gc,
    end,

    -- But then, the existence of `n` such that `m < n < M` is impossible!
    linarith,
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

#lint