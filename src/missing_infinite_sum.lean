import topology.algebra.infinite_sum


#check tendsto_nhds_top_mono'
-- section
-- variables {α β γ : Type*} [add_comm_monoid β]

-- open_locale big_operators

-- lemma finset.sum_sum_elim' [decidable_eq (α ⊕ γ)]
--   (s : finset (α ⊕ γ)) (f : α → β) (g : γ → β) :
--   (∑ x in s, sum.elim f g x) =
--     (∑ x in s.preimage sum.inl sorry, f x) + (∑ x in s.preimage sum.inr sorry, g x) :=
-- begin
--   classical,
--   convert finset.sum_sum_elim (s.preimage function.embedding.inl sorry) (s.preimage function.embedding.inr sorry) f g,
--   simp [finset.map_eq_image],
--   rw finset.image_preimage function.embedding.inl,
--   rw finset.image_preimage function.embedding.inr,
-- end
-- end

-- variables {α : Type*} {β : Type*} [topological_space α] [add_comm_monoid α] 
-- #check filter.tendsto_map'_iff
-- lemma has_sum_option (f : option β → α) (a : α) : 
--   has_sum f (a + f none) ↔ has_sum (λ x, f (some x)) (a) :=
-- begin
--   unfold has_sum,
--   split,
--   { intro h,
--     have : filter.tendsto (insert none) filter.at_top filter.at_top := sorry,
--     have := filter.tendsto.comp h this,
--     simp [(∘)] at this,
--     -- have := filter.tendsto.add_const,

--   },
--   { intro h,
--     have : filter.tendsto (insert : finset β) filter.at_top filter.at_top := sorry,
--     have := filter.tendsto.comp h this,


--   }
  
--   -- unfold has_sum,
--   -- have := @filter.tendsto_map'_iff _ _ _ (λ (s : finset (option β)), s.sum (λ (b : option β), f b))
--   -- (finset.map ⟨option.some, _⟩),
--   -- have := @filter.tendsto_map'_iff _ _ _ (λ (s : finset β), s.sum (λ (b : β), f (some b))),
-- end





-- #check equiv.set.univ

-- #check equiv.set.image _ set.univ sum.inl_injective


-- lemma tsum_sum' (f : β ⊕ γ → α) (hf : summable f) : 
--   ∑' (x : β ⊕ γ), f x = ∑' (x : β), f (sum.inl x) +  ∑' (x : γ), f (sum.inr x) :=
-- begin

--   have e₁ : _ := equiv.set.univ (β ⊕ γ),
--   have e₂ : _ := equiv.set.of_eq set.range_inl_union_range_inr,
--   rw ←equiv.tsum_eq (e₂.trans e₁),
--   have eβ : _ := equiv.set.image (sum.inl : β → β ⊕ γ) set.univ sum.inl_injective,
--   have eβ' : _ := equiv.set.univ β,
--   have eγ : _ := equiv.set.image (sum.inr : γ → β ⊕ γ) set.univ sum.inr_injective,
--   have eγ' : _ := equiv.set.univ γ,
--   rw ←equiv.tsum_eq (eβ.symm.trans eβ'),
--   rw ←equiv.tsum_eq (eγ.symm.trans eγ'),
--   have hdisjoint : disjoint (set.range sum.inl) (set.range sum.inr) := sorry,
--   --have hsummable : summable ((λ x : β ⊕ γ, f ((e₂.trans e₁) ((x : set.range sum.inl ∪ set.range sum.inr): β ⊕ γ))) ∘ coe) := sorry,
--   convert @tsum_union_disjoint _ _ _ _ _ (λ (x : β ⊕ γ), f ((e₂.trans e₁) ⟨x, _⟩)) _ (set.range sum.inl) (set.range sum.inr) hdisjoint _ _,
--   simp only [subtype.coe_eta],
--   simp only [set.image_univ],
--   simp only [set.image_univ],
--   ext,
--   simp only [set.image_univ],
--   simp,
--   ext,
--   have := set.range_inl_union_range_inr,
--   rw ← this,
--   -- have := equiv.tsum_eq (equiv.set.univ (option β)).symm,
-- end


-- lemma tsum_bool' (f : bool → α) : ∑' i : bool, f i = f ff + f tt :=
-- tsum_bool _


-- lemma tsum_sum' (f : β ⊕ γ → α) (hf : summable f) : 
--   ∑' (x : β ⊕ γ), f x = ∑' (x : β), f (sum.inl x) +  ∑' (x : γ), f (sum.inr x) :=
-- calc ∑' (x : β ⊕ γ), f x =
--   ∑' (c : Σ (b : bool), cond b β γ), f (((equiv.sum_equiv_sigma_bool β γ).symm) c) : 
--   begin
--      rw ←equiv.tsum_eq (equiv.sum_equiv_sigma_bool β γ).symm,
--      apply_instance,
--   end
--   ... = ∑' (b : bool) (x : cond b β γ), f (((equiv.sum_equiv_sigma_bool β γ).symm) ⟨b, x⟩) 
--   : @tsum_sigma α bool _ _ _ _ _ (λ b, cond b β γ) 
--   (λ x, f (((equiv.sum_equiv_sigma_bool β γ).symm) x)) 
--   ((equiv.summable_iff (equiv.sum_equiv_sigma_bool β γ).symm).2 hf)
--   ... = ∑' (x : β), f (sum.inl x) +  ∑' (x : γ), f (sum.inr x) : 
--   begin
--     rw add_comm,
--     rw tsum_bool',
--     refl
--   end

section 

universe variables u
variables {α β γ : Type u} {δ : Type*}
variables [add_comm_monoid α] [topological_space α]


lemma tsum_option (f : option β → α) (hf : summable f) : 
  ∑' (x : option β), f x = ∑' (x : β), f (some x) + f none :=
-- begin
--   rw ←equiv.tsum_eq (equiv.option_equiv_sum_punit β).symm,
--   rw tsum_sum',
--   congr,
--   simp only [tsum_fintype, fintype.univ_punit, finset.sum_const, equiv.option_equiv_sum_punit_symm_inr, one_nsmul,
--   finset.card_singleton],
--   exact ((equiv.summable_iff (equiv.option_equiv_sum_punit β).symm).2 hf),
--   apply_instance
-- end
sorry
end

section 



-- noncomputable theory
-- open finset filter function classical
-- open_locale topological_space classical big_operators nnreal
-- universe variables u
-- variables {α β γ : Type u} {δ : Type*}
-- variables [semiring α] [topological_space α] [topological_semiring α]
-- {f g : β → α} {a a₁ a₂ : α}

-- lemma tsum_mul_left' [t2_space α] (hf : summable f) : (∑' x, a * f x) = a * ∑' x, f x :=
-- hf.tsum_mul_left a

end