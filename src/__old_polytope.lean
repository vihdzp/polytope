import order.bounded_lattice set_theory.cardinal data.subtype

open_locale cardinal
universe u

section
parameters {α : Type u} [partial_order α]

-- A chain is a subset of faces where every pair of elements is related.
def is_chain (faces chain : set α) : Prop :=
chain ⊆ faces ∧ ∀ face₀ face₁ ∈ chain, face₀ ≤ face₁ ∨ face₁ ≤ face₀

namespace is_chain
-- The empty set is a chain.
lemma empty_chain (faces : set α) : is_chain faces ∅ :=
⟨set.empty_subset faces, λ _ _ h, absurd h $ set.not_mem_empty _⟩

-- A single face forms a chain.
lemma chain_single (faces : set α) (face ∈ faces) : is_chain faces {face} :=
⟨set.singleton_subset_iff.mpr ‹_›, λ _ _ (h₀ : _ = _) (h₁ : _ = _), by rw [h₀, h₁]; tauto⟩

-- A chain from the empty set is the empty set.
lemma no_faces (chain : set α) : is_chain ∅ chain ↔ chain = ∅ :=
⟨λ h, eq_bot_iff.mpr h.left, λ h, by rw h; apply empty_chain⟩

end is_chain

-- A flag is a maximal chain.
def is_flag (faces chain : set α) : Prop :=
is_chain faces chain ∧ ¬ ∃ chain', is_chain faces chain' → chain ⊂ chain'

-- A section is a set of faces bounded by two others.
def section_of {faces : set α} (face₀ face₁ ∈ faces) : face₀ ≤ face₁ → set α :=
λ _, {face ∈ faces | face₀ ≤ face ∧ face ≤ face₁}

section section_of
lemma section_single (faces : set α) (face ∈ faces) : section_of face face ‹_› ‹_› (le_refl _) = {face} :=
set.ext 
  (λ face', 
    ⟨(λ hf, begin 
      cases hf with _ _,
      finish,
    end),
    (λ h, begin
      induction h,
      fconstructor, 
      exact H, 
      tauto,
    end)⟩)

#check set.Ioo
-- add lemmas about section_of {x} _ _ = {x}

end section_of

theorem is_flag.imp_is_chain {faces chain : set α} : is_flag faces chain → is_chain faces chain :=
and.left

def chains (faces : set α) : set (set α) :=
{chain | is_chain faces chain}

def flags (faces : set α) : set (set α) :=
{chain | is_flag faces chain}

theorem flags_sub_chains (faces : set α) : flags faces ⊆ chains faces :=
λ _, is_flag.imp_is_chain

def is_rank_of_face {faces : set α} (face ∈ faces) (c : cardinal) : Prop :=
∀ chain ∈ chains faces, face ∈ chain → (∀ face' ∈ chain, face' ≤ face) → # chain = c + 1

def proper_faces (faces : set α) : set α :=
{face ∈ faces | ∃ face₀ face₁ ∈ faces, face₀ < face ∧ face < face₁}

def connected (faces : set α) : Prop :=
∀ face₀ face₁ ∈ proper_faces faces, ∃ chain ∈ chains faces, face₀ ∈ chain ∧ face₁ ∈ chain

def strongly_connected (faces : set α) : Prop :=
∀ face₀ face₁ ∈ faces, face₀ ≤ face₁ → connected (section_of face₀ face₁ ‹_› ‹_› ‹_›)

end

structure abstract_polytope (α : Type u) [partial_order α] :=
(faces : set α)
(has_bot : ∃ face ∈ faces, ∀ face' ∈ faces, face ≤ face')
(has_top : ∃ face ∈ faces, ∀ face' ∈ faces, face' ≤ face)
(flags_same_card : ∃ c, ∀ flag ∈ flags faces, # (flag : set α) = c)
(is_scon : strongly_connected faces)
(diamond : ∀ (face₀ face₁ ∈ faces) c, face₀ < face₁ → is_rank_of_face face₀ ‹_› c → is_rank_of_face face₁ ‹_› (c + 2) →
  ∃ d₀ d₁ ∈ faces, d₀ ≠ d₁ ∧ {face ∈ faces | face₀ < face ∧ face < face₁} = {d₀, d₁})

namespace abstract_polytope

def nullitope (α : Type u) [partial_order α] [inhabited α] : abstract_polytope α :=
let x := arbitrary α in
⟨
  {x},
  ⟨x, rfl, λ _ h, le_of_eq $ eq.symm h⟩,
  ⟨x, rfl, λ _ h, ge_of_eq $ eq.symm h⟩,
  ⟨1, λ chain (h : _ ∧ _), begin
    rcases h with ⟨⟨hll, _⟩, h⟩,
    rw set.subset_singleton_iff at hll,
    push_neg at h,
    sorry,
  end⟩,
  begin
    rintros _ _ h₀ h₁ hle _ _ hf₀,
    rw set.mem_singleton_iff at h₀ h₁,
    cases h₀, cases h₁,
    rcases hf₀ with ⟨_, _, _, _, _, ⟨hltl, htlr⟩⟩,
    sorry,
  end,
  begin
    intros _ _ h₀ h₁ c hlt,
    rw set.mem_singleton_iff at h₀ h₁,
    rw [h₀, h₁] at hlt,
    exact absurd hlt (asymm hlt)
  end,
⟩

end abstract_polytope
