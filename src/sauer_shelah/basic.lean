/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import combinatorics.set_family.compression.down
import data.nat.interval
import order.upper_lower
import tactic

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `finset.shatter`: The shattering property.
* `finset.shatterer`: The set family of sets shattered by a set family.
* `finset.vc_dimension`: The Vapnik-Chervonenkis dimension.
-/

namespace finset
variables {α : Type*} [decidable_eq α]

lemma insert_inter_distrib (a : α) (s t : finset α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
coe_injective $ by { push_cast, exact set.insert_inter_distrib _ _ _ }

end finset

open_locale big_operators finset_family

namespace finset
variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s t : finset α} {a : α} {n : ℕ}

/-- A set family shatters a set `s` if all subsets of `s` can be obtained as the intersection of `s`
and some element of the set family. We also say that `s` is traced by `𝒜`. -/
def shatter (𝒜 : finset (finset α)) (s : finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t

instance : decidable_pred 𝒜.shatter := λ s, finset.decidable_forall_of_decidable_subsets

lemma shatter.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : 𝒜.shatter s) : ℬ.shatter s :=
λ t ht, let ⟨u, hu, hut⟩ := h𝒜 ht in ⟨u, h hu, hut⟩

lemma shatter.mono_right (h : t ⊆ s) (hs : 𝒜.shatter s) : 𝒜.shatter t :=
λ u hu, by { obtain ⟨v, hv, rfl⟩ := hs (hu.trans h),
  exact ⟨v, hv, inf_congr_right hu $ inf_le_of_left_le h⟩ }

lemma shatter.exists_superset (h : 𝒜.shatter s) : ∃ t ∈ 𝒜, s ⊆ t :=
Exists₂.imp (λ t _, (inter_eq_left_iff_subset _ _).1) (h subset.rfl)

lemma shatter_of_forall_subset (h : ∀ t ⊆ s, t ∈ 𝒜) : 𝒜.shatter s :=
λ t ht, ⟨t, h _ ht, (inter_eq_right_iff_subset _ _).2 ht⟩

protected lemma shatter.nonempty (h : 𝒜.shatter s) : 𝒜.nonempty :=
let ⟨t, ht, _⟩ := h subset.rfl in ⟨t, ht⟩

@[simp] lemma shatter_empty : 𝒜.shatter ∅ ↔ 𝒜.nonempty :=
⟨shatter.nonempty, λ ⟨s, hs⟩ t ht, ⟨s, hs, by rwa [empty_inter, eq_comm, ←subset_empty]⟩⟩

protected lemma shatter.iff (h : 𝒜.shatter s) : t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t :=
⟨λ ht, h ht, by { rintro ⟨u, hu, rfl⟩, exact inter_subset_left _ _ }⟩

lemma shatter_iff : 𝒜.shatter s ↔ 𝒜.image (λ t, s ∩ t) = s.powerset :=
⟨λ h, by { ext t, rw [mem_image, mem_powerset, h.iff] },
  λ h t ht, by rwa [←mem_powerset, ←h, mem_image] at ht⟩

lemma univ_shatter [fintype α] : univ.shatter s := shatter_of_forall_subset $ λ _ _, mem_univ _

@[simp] lemma shatter_univ [fintype α] : 𝒜.shatter univ ↔ 𝒜 = univ :=
by { rw [shatter_iff, powerset_univ], simp_rw [univ_inter, image_id'] }

/-- The set family of sets that are shattered by `𝒜`. -/
def shatterer (𝒜 : finset (finset α)) : finset (finset α) := (𝒜.bUnion powerset).filter 𝒜.shatter

@[simp] lemma mem_shatterer : s ∈ 𝒜.shatterer ↔ 𝒜.shatter s :=
begin
  refine mem_filter.trans (and_iff_right_of_imp $ λ h, _),
  simp_rw [mem_bUnion, mem_powerset],
  exact h.exists_superset,
end

lemma shatterer_mono (h : 𝒜 ⊆ ℬ) : 𝒜.shatterer ⊆ ℬ.shatterer :=
λ _, by simpa using shatter.mono_left h

lemma subset_shatterer (h : is_lower_set (𝒜 : set (finset α))) : 𝒜 ⊆ 𝒜.shatterer :=
λ s hs, mem_shatterer.2 $ λ t ht, ⟨t, h ht hs, (inter_eq_right_iff_subset _ _).2 ht⟩

@[simp] lemma is_lower_set_shatterer (𝒜 : finset (finset α)) :
  is_lower_set (𝒜.shatterer : set (finset α)) :=
λ s t, by simpa using shatter.mono_right

@[simp] lemma shatterer_eq : 𝒜.shatterer = 𝒜 ↔ is_lower_set (𝒜 : set (finset α)) :=
begin
  refine ⟨λ h, _, λ h, subset.antisymm (λ s hs, _) $ subset_shatterer h⟩,
  { rw ←h,
    exact is_lower_set_shatterer _ },
  { obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset,
    exact h hst ht }
end

@[simp] lemma shatterer_idem : 𝒜.shatterer.shatterer = 𝒜.shatterer := by simp

@[simp] lemma shatter_shatterer : 𝒜.shatterer.shatter s ↔ 𝒜.shatter s :=
by simp_rw [←mem_shatterer, shatterer_idem]

alias shatter_shatterer ↔ _ shatter.shatterer

attribute [protected] shatter.shatterer

section order
variables [linear_order α]

def order_shatter : finset (finset α) → list α → Prop
| 𝒜 [] := 𝒜.nonempty
| 𝒜 (a :: l) := (𝒜.non_member_subfamily a).order_shatter l ∧ (𝒜.member_subfamily a).order_shatter l
    ∧ ∀ ⦃s : finset α⦄, s ∈ 𝒜.non_member_subfamily a → ∀ ⦃t⦄, t ∈ 𝒜.member_subfamily a →
      s.filter (λ b, a < b) = t.filter (λ b, a < b)

instance : decidable_pred 𝒜.order_shatter := 
  begin 
    sorry,
  end

def order_shatterer (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.bUnion powerset).filter $ λ s, 𝒜.order_shatter $ s.sort (≤)

end order

def strongly_shatter (𝒜 : finset (finset α)) (s : finset α) : Prop :=
∃ t, ∀ ⦃u⦄, u ⊆ s → ∃ v ∈ 𝒜, s ∩ v = u ∧ v \ s = t

@[elab_as_eliminator]
lemma family_induction (p : finset (finset α) → Prop) (hemp : p ∅)
  (h : ∀ a s (𝒜 : finset (finset α)), (∀ t ∈ 𝒜, t ⊆ insert a s) →
    p (𝒜.member_subfamily a) → p (𝒜.non_member_subfamily a) → p 𝒜) (𝒜 : finset (finset α)) : p 𝒜 :=
sorry

lemma aux {s : set α} {𝒜 : finset (finset α)} (h : ∀ t ∈ 𝒜, ↑t ⊆ s) : ∀ t ∈ 𝒜.shatterer, ↑t ⊆ s := 
begin
  intros t h0,
  rw mem_shatterer at h0,
  have h1: t ⊆ t,
  {
    simp,
  },
  specialize h0 h1,
  cases h0 with u h0,
  cases h0 with hu h0,
  have h2 := h u hu,
  have h3: t ⊆ u,
  exact (inter_eq_left_iff_subset t u).mp h0,
  exact (coe_subset.2 h3).trans (h u hu),
end

lemma insert_inj_non_mem (a : α) : {s : finset α | a ∉ s}.inj_on (λ s, insert a s) :=
λ s hs t ht (h : insert a s = _), by rw [←erase_insert hs, ←erase_insert ht, h]

/-- Pajor's variant of the **Sauer-Shelah lemma**. -/
lemma le_card_shatterer (𝒜 : finset (finset α)) : 𝒜.card ≤ 𝒜.shatterer.card :=
begin
  refine finset.family_induction _ _ _ 𝒜,
  { simp },
  intros a s t h1 h2 h3,

  have h4:  (member_subfamily a t).card + (non_member_subfamily a t).card = t.card,
  {
    exact card_member_subfamily_add_card_non_member_subfamily a t,
  },

  rw ← h4,

  have h5: (member_subfamily a t).shatterer ∪ (non_member_subfamily a t).shatterer ⊆ t.shatterer,
  {
    have h51: (member_subfamily a t).shatterer ⊆ t.shatterer,
    {
      intro S,
      simp,
      intro hy1,
      intros E hy2,
      have hy1_origin := hy1,
      specialize hy1 hy2,
      cases hy1 with f1 hy1,
      cases hy1 with hu hy1,
      simp at hu,
      cases hu with hu1 hu2,
      use (insert a f1),
      split,
      exact hu1,

      have hy3: ¬ a ∈ S,
      {
        by_contra hn,
        have hy4: {a} ⊆ S,{exact singleton_subset_iff.mpr hn,},
        specialize hy1_origin hy4,
        cases hy1_origin with f12 hy5,
        cases hy5 with hf12 hy5,
        simp at hf12,
        cases hf12 with ha hb,
        apply hb,
        have hy6: a ∈ S ∩ f12 ,
        {
          rw hy5,
          simp,
        },
        rw mem_inter at hy6,
        exact hy6.right,
      },
      rw ← hy1,
      ext x,
      split,
      {
        intro h,
        rw mem_inter at h ⊢,
        split,
        exact h.left,
        cases h with ha hb,
        have hy4: x ≠ a,
        {
          by_contra hy5,
          apply hy3,
          rwa hy5 at ha,
        },
        rw mem_insert at hb,
        cases hb with hb1 hb2,
        exfalso,
        exact hy4 hb1,
        exact hb2,
      },
      {
        intro h,
        rw mem_inter at h ⊢,
        cases h with ha hb,
        split,
        exact ha,
        rw mem_insert,
        right,
        exact hb,
      },
    },
    have h52: (non_member_subfamily a t).shatterer ⊆ t.shatterer,
    {
      have h: (non_member_subfamily a t) ⊆ t,
      {
        intro a,
        simp,
        intros h0 h00,
        exact h0,
      },
      exact shatterer_mono h,
    },
    exact union_subset h51 h52,
  },

  have h8: ((member_subfamily a t).shatterer ∪ (non_member_subfamily a t).shatterer).card + ((member_subfamily a t).shatterer ∩ (non_member_subfamily a t).shatterer).card = (member_subfamily a t).shatterer.card + (non_member_subfamily a t).shatterer.card,
  {
    apply finset.card_union_add_card_inter,
  },
  have h7:  ((member_subfamily a t).shatterer ∪ (non_member_subfamily a t).shatterer).card + ((member_subfamily a t).shatterer ∩ (non_member_subfamily a t).shatterer).card ≤ t.shatterer.card,
  {
    set S': (finset (finset α)) := ((member_subfamily a t).shatterer ∩ (non_member_subfamily a t).shatterer).image (insert a),
    have hs': S' = ((member_subfamily a t).shatterer ∩ (non_member_subfamily a t).shatterer).image (insert a),
    {
      refl,
    },
    have hy1: ((member_subfamily a t).shatterer ∩ (non_member_subfamily a t).shatterer).card = S'.card,
    {
      rw hs',
      refine (finset.card_image_of_inj_on _).symm,
      intros z1 hz1 z2 hz2 h,
      have h₁: ¬ a ∈ z1,
      {
        rw coe_inter at hz1,
        have hz11 := hz1.left,
        have hy₁: ∀ (m: finset α) , m ∈ (member_subfamily a t) → (m:set α) ⊆ {a}ᶜ,
        {
          intros m hm,
          rw mem_member_subfamily at hm,
          have hm2 := hm.right,
          simp,
          assumption,
        },
        have hy₃: (z1:set α) ⊆ {a}ᶜ,
        {
          apply aux hy₁,
          exact hz11,
        },
        simp at hy₃,
        exact hy₃,
      },
      have h₂: ¬ a ∈ z2,
      {
        rw coe_inter at hz2,
        have hz22 := hz2.left,
        have hy₂: ∀ (m: finset α) , m ∈ (member_subfamily a t) → (m:set α) ⊆ {a}ᶜ,
        {
          intros m hm,
          rw mem_member_subfamily at hm,
          have hm2 := hm.right,
          simp,
          assumption,
        },
        have hy₃: (z2:set α) ⊆ {a}ᶜ,
        {
          apply aux hy₂,
          exact hz22,
        },
        simp at hy₃,
        exact hy₃,
      },
      apply insert_inj_non_mem a,
      apply h₁,
      apply h₂,
      apply h,
    },
    have hy2: disjoint ((member_subfamily a t).shatterer ∪ (non_member_subfamily a t).shatterer) S',
    {
      rw finset.disjoint_left,
      intros x hx,
      rw mem_union at hx,
      cases hx with hx1 hx2,
      {
        have hx3: a ∉ x,
        {
          have hy₁: ∀ (m: finset α) , m ∈ (member_subfamily a t) → (m:set α) ⊆ {a}ᶜ,
          {
          intros m hm,
          rw mem_member_subfamily at hm,
          have hm2 := hm.right,
          simp,
          assumption,
          },
          have hy₃: (x:set α) ⊆ {a}ᶜ,
        {
          apply aux hy₁,
          exact hx1,
        },
        simp at hy₃,
        exact hy₃,
        },
        have hS': ∀ y ∈ S', a∈y,
        {
          intros z hz,
          rw hs' at hz,
          rw mem_image at hz,
          cases hz with z0 hz,
          cases hz with hz0 hz,
          rw ← hz,
          exact mem_insert_self a z0,
        },
        by_contra hn,
        have hnn:= hS' x hn,
        exact hx3 hnn,
      },
      {
        have hx3: a ∉ x,
        {
          have hy₁: ∀ (m: finset α) , m ∈ (non_member_subfamily a t) → (m:set α) ⊆ {a}ᶜ,
          {
          intros m hm,
          rw mem_non_member_subfamily at hm,
          have hm2 := hm.right,
          simp,
          assumption,
          },
          have hy₃: (x:set α) ⊆ {a}ᶜ,
          {
            apply aux hy₁,
            exact hx2,
          },
        simp at hy₃,
        exact hy₃,
        },
        have hS': ∀ y ∈ S', a∈y,
        {
          intros z hz,
          rw hs' at hz,
          rw mem_image at hz,
          cases hz with z0 hz,
          cases hz with hz0 hz,
          rw ← hz,
          exact mem_insert_self a z0,
        },
        by_contra hn,
        have hnn:= hS' x hn,
        exact hx3 hnn,
      },
    },
    rw hy1,
    have hy3: S' ⊆ t.shatterer,
    {
      intros x h,
      rw hs' at h,
      rw finset.mem_image at h,
      cases h with y h,
      cases h with hy h,
      rw mem_inter at hy,
      cases hy with hy₁ hy₂,
      rw ← h,
      simp,
      intros y₀ hy₀,
      simp at hy₁,
      have h₁: erase y₀ a ⊆ y,
      {
        exact subset_insert_iff.mp hy₀,
      },
      specialize hy₁ h₁,
      cases hy₁ with u hy₁,
      cases hy₁ with hu hy₁,
      by_cases ha: a ∈ y₀ ,
      {
      use insert a u,
      split;
      rw mem_member_subfamily at hu,
      exact hu.left,
      rwa [←insert_inter_distrib, hy₁, insert_erase],
      },
      { 
        simp at hy₂,
        have hemp : y₀ ⊆ y,
        {
          exact (subset_insert_iff_of_not_mem ha).mp hy₀,
        },
        specialize hy₂ hemp,
        cases hy₂ with u₀ hy₂,
        cases hy₂ with hu₀ hy₂,
        have hu₀t: u₀ ∈ t,
        {
          rw mem_non_member_subfamily at hu₀,
          exact hu₀.left,
        },
        use u₀,
        split,
        exact hu₀t,
        have hy₃: ¬ a ∈ u₀,
        {
          rw mem_non_member_subfamily at hu₀,
          exact hu₀.right,
        },
        rw ← hy₂,
        exact finset.insert_inter_of_not_mem hy₃,
      },
    },
    have hy4: ((member_subfamily a t).shatterer ∪ (non_member_subfamily a t).shatterer ∪ S') ⊆ t.shatterer,
    {
      exact union_subset h5 hy3,
    },
    rw ←  finset.card_disjoint_union hy2,
    apply finset.card_le_of_subset hy4,
  },
  suffices h: (member_subfamily a t).shatterer.card + (non_member_subfamily a t).shatterer.card ≤ t.shatterer.card,
  linarith,
  rw ← h8,
  assumption,
end

variables [fintype α]

/-- The Vapnik-Chervonenkis dimension of a set family is the maximal size of a set it shatters. -/
def vc_dimension (𝒜 : finset (finset α)) : ℕ := (univ.filter 𝒜.shatter).sup card

lemma shatter.card_le_vc_dimension (h : 𝒜.shatter s) : s.card ≤ 𝒜.vc_dimension :=
finset.le_sup $ mem_filter.2 ⟨mem_univ _, h⟩

/-- Down-compressing decreases the VC-dimension. -/
lemma vc_dimension_compress_le (a : α) (𝒜 : finset (finset α)) :
  (𝓓 a 𝒜).vc_dimension ≤ 𝒜.vc_dimension :=
begin 
  sorry,
end

/-- The **Sauer-Shelah lemma**. -/
lemma card_shatterer_le_sum_vc_dimension :
  𝒜.shatterer.card ≤ ∑ k in Iic 𝒜.vc_dimension, (fintype.card α).choose k :=
begin
  simp_rw [←card_univ, ←card_powerset_len],
  refine ((card_le_of_subset $ λ s hs, mem_bUnion.2 ⟨card s, _⟩).trans $ card_bUnion_le),
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vc_dimension, mem_powerset_len_univ_iff.2 rfl⟩,
end

end finset