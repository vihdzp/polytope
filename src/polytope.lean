import tactic set_theory.ordinal order.bounded_lattice order.zorn data.set.intervals.ord_connected order.rel_iso data.finset.preimage

open_locale cardinal

set_option old_structure_cmd true

/-- A partial order with a least and greatest element. -/
class bounded_partial_order (α : Type*) extends order_top α, order_bot α

namespace bounded_partial_order
section

  parameters {α : Type*} [bl : bounded_lattice α]

  -- A bounded lattice is a bounded partial order.
  instance of_top_bot : bounded_partial_order α :=
  { ..bl }

end
end bounded_partial_order

/-- A face `c` covers `a` whenever `a < c` and no face `b` exists such that `a < b < c`. -/
def covers {α : Type*} [preorder α] (a c : α) : Prop :=
a < c ∧ ¬ ∃ b, a < b ∧ b < c

/-- A graded poset has a function from elements to naturals that's compatible
    with the ordering, and consistent with the covering relation. -/
class graded (α : Type*) extends order_bot α :=
(grade : α → ℕ)
(grade_bot_eq_zero : grade ⊥ = 0)
(lt_grade_of_lt : ∀ {a b : α}, a < b → grade a < grade b)
(eq_p1_of_cover : ∀ {a b : α}, covers a b → grade a + 1 = grade b)

namespace graded
section

  parameters {α : Type*} [graded α]

  /-- If `a ≤ b`, then `grade a ≤ grade b`. -/
  theorem le_grade_of_le : ∀ {a b : α}, a ≤ b → graded.grade a ≤ graded.grade b :=
  begin
    intros a b a_le_b,
    cases lt_or_eq_of_le a_le_b with a_lt_b a_eq_b, {
      exact le_of_lt (graded.lt_grade_of_lt a_lt_b),
    },
    exact (congr_arg grade (eq.symm a_eq_b)).ge,
  end

  /-- If `grade a = 0`, then `a = ⊥`. -/
  theorem eq_bot_of_grade_eq_zero {a : α} : grade a = 0 → a = ⊥ :=
  begin
    contrapose,
    intro a_ne_bot,
    have h : grade a > grade (⊥ : α) :=  lt_grade_of_lt (lt_of_le_of_ne (bot_le a) (ne.symm a_ne_bot)),
    rw grade_bot_eq_zero at h,
    exact ne_of_gt h,
  end

end
end graded

/-- A graded, bounded partial order. -/
class graded_bounded_partial_order (α : Type*) extends bounded_partial_order α, graded α

namespace graded_bounded_partial_order
section

  parameters {α : Type*} [graded_bounded_partial_order α] (a : α)

  /-- If `grade a = grade ⊤`, then `a = ⊤`. -/
  theorem eq_top_of_grade_eq_grade_top : graded.grade a = graded.grade (⊤ : α) → a = ⊤ :=
  begin
    contrapose,
    intro a_ne_bot,
    exact ne_of_lt ( lt_grade_of_lt (lt_of_le_of_ne (le_top a) a_ne_bot)),
  end

  /-- The grade of any element is in the interval `[0, grade ⊤]`. -/
  theorem grade_mem_Iic : graded.grade a ∈ set.Iic (graded.grade (⊤ : α)) :=
  graded.le_grade_of_le (le_top a)

end
end graded_bounded_partial_order

namespace flag
section

  variables {α : Type*} [graded_bounded_partial_order α] {f f' : set α}

  /-- A flag is a maximal chain. -/
  def is_flag (c : set α) : Prop :=
  @zorn.is_max_chain _ (<) c

  /-- Two flags are adjacent when they differ by exactly one element. -/
  def flag_adj (f f' : set α) : Prop :=
  is_flag f → is_flag f' → #(set.diff f f') = 1

  /-- If one attempts to extend a flag `f` by an element `e` which is comparable to
  --  all other faces of the flag, we obtain a contradiction. -/
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

    -- We prove that `f'` is a superchain of `f`, a contradiction!
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
    apply flag_extend ⊥ ff bot_nmem_f,

    -- The bottom face is less or equal to any other.
    intros a a_mem_f a_ne_bot,
    exact or.inr (lt_of_le_of_ne bot_le (ne.symm a_ne_bot)),
  end

  -- Any flag contains the top face `⊤`.
  theorem top_in_flag : is_flag f → ⊤ ∈ f :=
  begin
    -- We use the `flag_extend` lemma.
    intro ff,
    by_contra top_nmem_f,
    apply flag_extend ⊤ ff top_nmem_f,

    -- The top face is greater or equal to any other.
    intros a a_mem_f a_ne_bot,
    exact or.inl (lt_of_le_of_ne le_top (a_ne_bot)),
  end

end
end flag

-- The faces of a flag are merely its elements.
def flag_faces {α : Type*} [graded_bounded_partial_order α] {f : set α} (ff : flag.is_flag f) : Type* := f

namespace flag_faces
section

  parameters {α : Type*} [graded_bounded_partial_order α] {f : set α} {ff : flag.is_flag f} (a b : flag_faces ff)

  -- Subtyping preserves equality and viceversa.
  @[simp] lemma eq_iff_subtype : a = b ↔ a.val = b.val := subtype.ext_iff_val

  -- Subtyping preserves inequality and viceversa.
  lemma ne_iff_subtype : a ≠ b ↔ a.val ≠ b.val := by simp

  -- Flag faces form a partial order.
  instance of_partial_order : partial_order (flag_faces ff) :=
  {
    le := λ a b, a.val ≤ b.val,
    le_refl := λ a, le_refl a.val,
    le_trans := λ _ _ _ a_le_b b_le_c, le_trans a_le_b b_le_c,
    le_antisymm := λ _ _ a_le_b b_le_a, subtype.eq (le_antisymm a_le_b b_le_a),
  }

  -- Subtyping preserves order and viceversa.
  @[simp] lemma lt_iff_subtype : a < b ↔ a.val < b.val := iff.symm lt_iff_le_not_le

  -- Flag faces form a linear order.
  noncomputable instance of_linear_order : linear_order (flag_faces ff) :=
  {
    le_total := begin
      intros a b,

      -- `a = b` is trivial.
      by_cases a_eq_b : a = b, {
        exact or.inl (eq.symm a_eq_b).ge,
      },

      -- If `a ≠ b`, then either `a < b`...
      cases ff.left a.val (subtype.mem a) b.val (subtype.mem b) ((ne_iff_subtype a b).mp a_eq_b) with av_lt_bv bv_lt_av, {
        exact or.inl (le_of_lt ((lt_iff_subtype a b).mpr av_lt_bv)),
      },

      -- ...or `b < a`.
      exact or.inr (le_of_lt ((lt_iff_subtype b a).mpr bv_lt_av)),
    end,

    decidable_le := classical.dec_rel _,

    ..of_partial_order
  }

  -- Flag faces form a graded bounded partial order.
  instance of_graded_bounded_partial_order : graded_bounded_partial_order (flag_faces ff) :=
  {
    bot := ⟨⊥, flag.bot_in_flag ff⟩,
    bot_le := λ _, bot_le,

    top := ⟨⊤, flag.top_in_flag ff⟩,
    le_top := λ _, @le_top α _ _,

    grade := λ a, graded.grade a.val,
    grade_bot_eq_zero := graded.grade_bot_eq_zero,

    lt_grade_of_lt := begin
      intros _ _ a_lt_b,
      exact graded.lt_grade_of_lt ((lt_iff_subtype _ _).mp a_lt_b),
    end,

    eq_p1_of_cover := begin
      -- It suffices to prove that `a` covers `c`.
      rintros a c ⟨a_lt_c, hne⟩,
      apply graded.eq_p1_of_cover,
      use (lt_iff_subtype a c).mp a_lt_c,

      -- To do this, we prove that any element between `a` and `c` must be in `f`.
      by_contra he,
      cases he with bv a_mem_ibc,
      cases a_mem_ibc with av_lt_bv bv_lt_cv,
      apply hne,

      -- To use the `flag_extend` lemma, we must prove that any `x ∈ f` is comparable to `b`.
      have bv_mem_f : bv ∈ f := begin
        by_contra b_nmem_f,
        apply flag.flag_extend bv ff b_nmem_f,
        intros xv x_mem_f _,
        let x : flag_faces ff := ⟨xv, x_mem_f⟩,

        -- `x` must be below `a` or above `c` (since there's no elements in between).
        have x_le_a_or_c_le_x : x ≤ a ∨ c ≤ x := begin
          by_cases x_le_a : x ≤ a, {
            exact or.inl x_le_a,
          },
          by_cases c_le_x : c ≤ x, {
            exact or.inr c_le_x,
          },
          exfalso,
          exact hne ⟨x, not_le.mp x_le_a, not_le.mp c_le_x⟩,
        end,

        -- We finish by transitivity.
        cases x_le_a_or_c_le_x with x_le_a c_le_x, {
          exact or.inl (lt_of_le_of_lt x_le_a av_lt_bv),
        },
        exact or.inr (lt_of_lt_of_le bv_lt_cv c_le_x),
      end,

      let b : flag_faces ff := ⟨bv, bv_mem_f⟩,
      exact ⟨b, (lt_iff_subtype a b).mpr av_lt_bv, (lt_iff_subtype b c).mpr bv_lt_cv⟩,
    end,

    ..of_partial_order,
  }

end
end flag_faces

namespace flag
section

  variables {α : Type*} [graded_bounded_partial_order α] {f f' : set α}

  /-- Casts a flag into a set of its own faces. -/
  def to_flag_faces (ff : is_flag f) : set (flag_faces ff) := subtype.val ⁻¹' f

  /-- Every set of faces in a flag is a subset of the entire set. -/
  lemma ssubset_flag_faces {ff : is_flag f} (s : set (flag_faces ff)) : s ⊆ to_flag_faces ff :=
  λ s _, subtype.mem s

  /-- If `s` contains all faces of a flag, it must be the set of all faces. -/
  lemma eq_of_ssubset_flag_faces (ff : is_flag f) (s : set (flag_faces ff)) : to_flag_faces ff ⊆ s → s = to_flag_faces ff :=
  begin
    intro ff_subset_s,
    refine set.eq_of_subset_of_subset _ ff_subset_s,
    exact ssubset_flag_faces s,
  end 

  /-- Applying `to_flag_faces` to a flag does not change the fact that it is a flag. -/
  theorem to_flag_faces_is_flag (ff : is_flag f) : is_flag (to_flag_faces ff) :=
  begin
    split, {
      intros _ _ _ _ a_ne_b,
      exact ne.lt_or_lt a_ne_b,
    },
    by_contra h,
    cases h with ch hch,
    cases hch with _ sch,
    rw set.ssubset_def at sch,
    exact sch.right (ssubset_flag_faces ch),
  end

  /-- The subtypes of all elements of a flag form the original set. -/
  lemma subtype_of_flag_faces_eq_flag (ff : is_flag f) : subtype.val '' to_flag_faces ff = f :=
  begin
    apply set.ext,
    intro x,
    split, {
      intro h,
      cases h with a ha,
      cases ha with a_mem_ff av_eq_x,
      exact set.mem_of_eq_of_mem (eq.symm av_eq_x) a_mem_ff,
    },
    intro x_mem_f,
    let x' : flag_faces ff := ⟨x, x_mem_f⟩, 
    use x', 
    use x_mem_f,
  end

  /-- The set of grades of a flag. -/
  def flag_grades (f : set α): set ℕ := {n | ∃ a ∈ f, graded.grade a = n}
  
  /-- In a flag, `grade a < grade b` implies `a < b`. -/
  theorem grade_lt_of_lt {ff : is_flag f} {a b : flag_faces ff} : graded.grade a < graded.grade b → a < b :=
  begin
    rintros ga_lt_gb,
    cases lt_trichotomy a b with a_lt_b a_nlt_b, {
      exact a_lt_b,
    },
    cases a_nlt_b with a_eq_b a_gt_b, {
      rw a_eq_b at ga_lt_gb,
      exact false.elim (nat.lt_asymm ga_lt_gb ga_lt_gb),
    },
    exact false.elim (nat.lt_asymm ga_lt_gb (graded.lt_grade_of_lt a_gt_b)),
  end

  /-- No two elements in a flag have the same grade. -/
  theorem grade_eq_of_eq {ff : is_flag f} {a b : flag_faces ff} : graded.grade a = graded.grade b → a = b :=
  begin
    rintros ga_eq_gb,
    cases lt_trichotomy a b with a_lt_b a_nlt_b, {
      exact false.elim (ne_of_lt (graded.lt_grade_of_lt a_lt_b) ga_eq_gb),
    },
    cases a_nlt_b with a_eq_b a_gt_b, {
      exact a_eq_b,
    },
    exact false.elim (ne_of_gt (graded.lt_grade_of_lt a_gt_b) ga_eq_gb),
  end

  /-- Flag grades on a flag are sent to the interval `[0, grade ⊤]`. -/
  theorem flag_grades_maps_to (ff : is_flag f) : set.maps_to graded.grade f (set.Iic (graded.grade (⊤ : α))) :=
  λ _ _,  graded.le_grade_of_le le_top

  /-- Flag grades are injective on a flag. -/
  theorem flag_grades_inj_on (ff : is_flag f) : set.inj_on graded.grade f :=
  begin
    intros a a_mem_f b b_mem_f ga_eq_gb,
    apply (flag_faces.eq_iff_subtype ⟨a, a_mem_f⟩ ⟨b, b_mem_f⟩).mp,
    apply grade_eq_of_eq,
    exact ga_eq_gb,
    exact ff,
  end

  /-- Flag grades are injective on a flag. -/
  theorem flag_grades_inj_on' (ff : is_flag f) : set.inj_on graded.grade (to_flag_faces ff) :=
  begin
    apply flag_grades_inj_on,
    exact to_flag_faces_is_flag ff,
  end  

  /-- The faces of a flag have a fintype, i.e. every flag is finite. -/
  noncomputable theorem flag_fintype (ff : is_flag f) : fintype (flag_faces ff) := begin
    -- We define the interval `[0, grade ⊤]` and its inverse image under `grade`, onto `f`.
    let I := set.Iic (graded.grade (⊤ : α)),
    let I_fin := set.finite_le_nat (graded.grade (⊤ : α)),
    let f' : set (flag_faces ff) := graded.grade ⁻¹' I,
    have f'_eq_to_flag_faces_ff : f' = to_flag_faces ff := begin
      apply eq_of_ssubset_flag_faces,
      intros a _,
      exact graded_bounded_partial_order.grade_mem_Iic a,
    end,

    -- The `grade` function is injective on the flag.
    have flag_grades_inj_on_ff : @set.inj_on (flag_faces ff) ℕ graded.grade f' := begin
      rw f'_eq_to_flag_faces_ff,
      apply flag_grades_inj_on',
    end,

    -- Since `I` is finite, so are `f'` and `f`.
    have f'_fin : f'.finite := @set.finite.preimage (flag_faces ff) ℕ I graded.grade flag_grades_inj_on_ff I_fin,
    rw f'_eq_to_flag_faces_ff at f'_fin,
    have f_fin : f.finite := begin
      have h := set.finite.image subtype.val f'_fin,
      rw subtype_of_flag_faces_eq_flag at h,
      exact h,
    end,
    exact set.finite.fintype f_fin,
  end

  /-- The assertion that a flag is finite. -/
  def flag_finite (ff : is_flag f) : f.finite :=
  ⟨flag_fintype ff⟩

  /-- A flag contains faces of each grade up to the grade of its topmost face. -/
  theorem flag_grades_Iic (ff : is_flag f) : flag_grades f = set.Iic (graded.grade (⊤ : α)) :=
  begin
    let G := flag_grades f,
    let N := graded.grade (⊤ : α),
    let I := set.Iic N,

    -- Every flag grade is between `0` and `N`.
    have G_in_I : G ⊆ I := begin
      rintros _ ⟨_, a_mem_f, ga_eq_f⟩,
      rw ←ga_eq_f,
      exact flag_grades_maps_to ff a_mem_f,
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
        exact ⟨zero_le n, ⟨⊥, bot_in_flag ff, graded.grade_bot_eq_zero⟩⟩,
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
      have SM_non : SM.nonempty := ⟨N, set.mem_inter n_mem_I ⟨⊤, top_in_flag ff, rfl⟩⟩,

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
      let a : flag_faces ff := ⟨a, a_mem_f⟩,
      let c : flag_faces ff := ⟨c, c_mem_f⟩,

      -- `a` must be less than `c`.
      have ga_eq_m : graded.grade a = m := ga_eq_m,
      have gc_eq_M : graded.grade c = M := gc_eq_M,
      have a_lt_c : a < c := begin
        rw ←ga_eq_m at m_lt_M,
        rw ←gc_eq_M at m_lt_M,
        exact grade_lt_of_lt m_lt_M,
      end,

      -- There can't exist any face in the flag that's between `a` and `c`.
      have C : ¬ ∃ b, a < b ∧ b < c := begin
        intro he,
        cases he with b he,
        cases he with a_lt_b b_lt_c,

        let g := graded.grade b,
        have m_lt_g : m < g := begin
          rw ←ga_eq_m,
          exact graded.lt_grade_of_lt a_lt_b,
        end,
        have g_lt_M : g < M := begin
          rw ←gc_eq_M,
          exact graded.lt_grade_of_lt b_lt_c,
        end,
        have g_mem_G : g ∈ G := ⟨b.val, subtype.mem b, rfl⟩,
        by_cases g_lt_n : g < n, {
          exact hm g (set.mem_inter m_lt_g g_lt_n) g_mem_G,
        },
        exact hM g (set.mem_inter (le_of_not_gt g_lt_n) g_lt_M) g_mem_G,
      end,

      -- As a consequence, `m + 1 = M`.
      have ga_p1_eq_gc : graded.grade a + 1 = graded.grade c := graded.eq_p1_of_cover ⟨a_lt_c, C⟩,
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

  /-- Flag grades are surjective from a flag onto `[0, grade ⊤]`. -/
  theorem flag_grades_surj_on (ff : is_flag f) : set.surj_on graded.grade f (set.Iic (graded.grade (⊤ : α))) :=
  begin
    intros n n_mem_Iic,
    have h : graded.grade '' f = flag_grades f := set.image_eq graded.grade f,
    rw h,
    rw flag_grades_Iic ff,
    exact n_mem_Iic,
  end

  /-- Flag grades are surjective from a flag onto `[0, grade ⊤]`. -/
  theorem flag_grades_surj_on' (ff : is_flag f) : set.surj_on graded.grade (to_flag_faces ff) (set.Iic (graded.grade (⊤ : α))) :=
  begin
    apply flag_grades_surj_on,
    exact to_flag_faces_is_flag ff,
  end

  /-- Flag grades are bijective from a flag onto `[0, grade ⊤]`. -/
  theorem flag_grades_bij_on (ff : is_flag f) : set.bij_on graded.grade f (set.Iic (graded.grade (⊤ : α))) :=
  ⟨flag_grades_maps_to ff, flag_grades_inj_on ff, flag_grades_surj_on ff⟩

  /-- Flag grades are bijective from a flag onto `[0, grade ⊤]`. -/
  theorem flag_grades_bij_on' (ff : is_flag f) : set.bij_on graded.grade (to_flag_faces ff) (set.Iic (graded.grade (⊤ : α))) :=
  begin
    apply flag_grades_bij_on,
    exact to_flag_faces_is_flag ff,
  end

  -- Any flag's cardinality equals the rank of the top element, plus one.
  theorem flag_card : #f = graded.grade (⊤ : α) + 1 :=
  sorry

end
end flag

namespace flag_faces
section

  parameters {α : Type*} [graded_bounded_partial_order α] {f : set α} {ff : flag.is_flag f}

  instance of_well_order : @is_well_order (flag_faces ff) (<) :=
  {
    wf := begin
      apply well_founded.intro,
      have h : ∀ {n : ℕ} (a : flag_faces ff), graded.grade a ≤ n → acc (<) a := begin
        intro n,
        induction n with n hn, {
          intros a ga_le_zero,
          apply acc.intro,
          intros y y_lt_a,
          rw (graded.eq_bot_of_grade_eq_zero (nat.le_zero_iff.mp ga_le_zero)) at y_lt_a,
          have bot_le_y : ⊥ ≤ y := bot_le,
          exact false.elim ((not_lt.mpr bot_le_y) y_lt_a),
        },
        intros a ga_le_ns,
        apply acc.intro,
        intros y y_lt_a,
        exact hn y (nat.lt_succ_iff.mp (lt_of_lt_of_le (graded.lt_grade_of_lt y_lt_a) ga_le_ns)),
      end,
      intro a,
      exact h a rfl.ge,
    end
  }

end
end flag_faces

set_option old_structure_cmd false

class abstract_polytope (α : Type*) extends (graded_bounded_partial_order α) :=
(diamond : ∀ {a b : α}, grade a + 2 = grade b → #(set.Ioo a b) = 2)

set_option old_structure_cmd true

namespace abstract_polytope

  variables {α : Type*} [abstract_polytope α] (f f' : set α)

  def grade : α → ℕ := graded.grade

  theorem all_flags_same_card {f f' : set α} (ff : flag.is_flag f): #f = #f' :=
  begin
    sorry,
  end

  -- Flag adjacency in an abstract polytope is commutative.
  theorem flag_adj_comm : flag.is_flag f → flag.is_flag f' → flag.flag_adj f f' → flag.flag_adj f' f :=
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