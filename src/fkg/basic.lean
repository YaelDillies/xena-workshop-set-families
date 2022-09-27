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

variables [distrib_lattice α] [decidable_eq α] [ordered_semiring β]
  {f f₁ f₂ f₃ f₄ g μ : α → β}

/-- The **four functions theorem** -/
lemma four_functions_theorem (h₁ : ∀ a ∈ u, 0 ≤ f₁ a) (h₂ : ∀ a ∈ u,  0 ≤ f₂)
  (h₃ : ∀ a ∈ u,  0 ≤ f₃) (h₄ : ∀ a ∈ u,  0 ≤ f₄)
  (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊔ b) * f₄ (a ⊓ b)) {s t u : finset α} (hs : s ⊆ u) (ht : t ⊆ u) :
  (∑ a in s, f₁ a) * (∑ b in t, f₂ b) ≤ (∑ a in s ∪ t, f₃ a) * (∑ b in s ∩ t, f₄ b) :=
begin
  sorry
end

protected lemma log_super_modular.sum (hf : 0 ≤ f) :
  log_super_modular f → log_super_modular (λ s, ∑ a in s, f a) :=
four_functions_theorem hf hf hf hf

lemma fkg (hμ : 0 ≤ μ) (hf : monotone f) (hg : monotone g) :
  (∑ a, f a * μ a) * (∑ a, g a * μ a) ≤ (∑ a, f a * g a * μ a) * (∑ a, μ a) :=
begin
  sorry
end