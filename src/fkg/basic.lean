import algebra.big_operators.basic

/-!
# The four functions theorem and FKG inequality

-/

open_locale big_operators

variables {α β : Type*}

section lattice
variables [lattice α] [has_mul β] [has_le β]

def log_super_modular (f : α → β) : Prop := ∀ a b, f a * f b ≤ f (a ⊔ b) * f (a ⊓ b)

end lattice

protected lemma linear_order.log_super_modular [linear_order α] [comm_semigroup β] [preorder β]
  (f : α → β) :
  log_super_modular f :=
λ a b, by cases le_total a b; simp [h, mul_comm]

section finset
variables [decidable_eq α] [ordered_semiring β] {f f₁ f₂ f₃ f₄ g μ : finset α → β}

/-- The **four functions theorem** -/
lemma four_functions_theorem' {u : finset α}  (h₁ : ∀ s ⊆ u, 0 ≤ f₁ s) (h₂ : ∀ s ⊆ u, 0 ≤ f₂ s)
  (h₃ : ∀ s ⊆ u, 0 ≤ f₃ s) (h₄ : ∀ s ⊆ u, 0 ≤ f₄ s)
  (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)) {s t : finset (finset α)} (hs : s ⊆ u.powerset) (ht : t ⊆ u.powerset) :
  (∑ a in s, f₁ a) * (∑ b in t, f₂ b) ≤ (∑ a in s ∪ t, f₃ a) * (∑ b in s ∩ t, f₄ b) :=
begin
  induction u using finset.induction generalizing f₁ f₂ f₃ f₄,
  {
    have h1: (∅:finset α).powerset = {∅},
    exact finset.powerset_empty,
    rw h1 at hs ht,
    have h2: s = ∅ ∨ s = {∅},
    exact finset.subset_singleton_iff.mp hs,
    have h3: t = ∅ ∨ t = {∅},
    exact finset.subset_singleton_iff.mp ht,
    cases h2,
    {
    cases h3,
      {
      rw h2,
      rw h3,
      have h4: (∑ (a : finset α) in ∅, f₁ a) = 0,
      refl,
      have h5: ∑ (b : finset α) in ∅, f₂ b = 0,
      refl,
      have h6: (∑ (a : finset α) in ∅ ∪ ∅, f₃ a) = 0,
      refl, 
      have h7: ∑ (b : finset α) in ∅ ∩ ∅, f₄ b = 0,
      refl,
      rw h4,
      rw h5,
      rw h6,
      rw h7,
      },

      { 
        rw h2,
        rw h3,
        have h4: (∑ (a : finset α) in ∅, f₁ a) = 0,
        refl,
        have h5: ∑ (b : finset α) in {∅}, f₂ b = f₂ ∅,
        simp,
        have h6: (∑ (a : finset α) in ∅ ∪ {∅}, f₃ a) = f₃ ∅,
        simp,
        have h7: ∑ (b : finset α) in ∅ ∩ {∅}, f₄ b = 0,
        simp,
        rw h4,
        rw h5,
        rw h6,
        rw h7,
        simp,
      },
    },

    {
      cases h3,
      {
        simp,
        rw h2,
        rw h3,
        simp,
      },
      {
        simp,
        rw h2,
        rw h3,
        simp,
        specialize h ∅ ∅,
        simp at h,
        exact h,
      }
    },
  },

  {
    
  }
end

end finset

variables [distrib_lattice α] [decidable_eq α] [ordered_semiring β]
  {f f₁ f₂ f₃ f₄ g μ : α → β}

/-- The **four functions theorem** -/
lemma four_functions_theorem {s t u : finset α} (h₁ : ∀ a ∈ u, 0 ≤ f₁ a) (h₂ : ∀ a ∈ u,  0 ≤ f₂)
  (h₃ : ∀ a ∈ u,  0 ≤ f₃) (h₄ : ∀ a ∈ u,  0 ≤ f₄)
  (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)) (hs : s ⊆ u) (ht : t ⊆ u) :
  (∑ a in s, f₁ a) * (∑ b in t, f₂ b) ≤ (∑ a in s ∪ t, f₃ a) * (∑ b in s ∩ t, f₄ b) :=
begin
  sorry,
end

protected lemma log_super_modular.sum (hf : 0 ≤ f) :
  log_super_modular f → log_super_modular (λ s, ∑ a in s, f a) :=
four_functions_theorem hf hf hf hf

lemma fkg (hμ : 0 ≤ μ) (hf : monotone f) (hg : monotone g) :
  (∑ a, f a * μ a) * (∑ a, g a * μ a) ≤ (∑ a, f a * g a * μ a) * (∑ a, μ a) :=
begin
  sorry
end