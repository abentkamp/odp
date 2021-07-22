import measure_theory.prod
import measure_theory.giry_monad
import measure_theory.measurable_space_def
import .dp
import .missing_integration

--TODO: move
@[measurability]
protected theorem measurable_prod_swap (α β : Type*) [measurable_space α] [measurable_space β] : 
  measurable (@prod.swap α β) :=
by unfold prod.swap; measurability

open measure_theory ennreal

variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂]

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) [hP₁ : probability_measure P₁] [hP₂ : probability_measure P₂]

local infix ` ⊗ `:50  := measure.prod

section part1

variables (V W : set (Ω₁ × Ω₂)) (ε δ : ennreal) {hV : measurable_set V} {hW : measurable_set W}

-- lemma zero_outside_fst_V : 
--   ∀ ω₁ ∉ prod.fst '' V, P₂ (prod.mk ω₁ ⁻¹' W) = 0 :=
-- begin
--   intros ω₁ hω₁,
--   convert measure_empty,
--   rw set.eq_empty_iff_forall_not_mem,
--   intros ω₂ hω₂,
--   rw set.mem_image at hω₁,
--   refine hω₁ ⟨_, hω₂, _⟩,
--   refl
-- end

include hP₁ hP₂ hV hW

lemma part1_step1 
  (V₁ : set Ω₁) (hV₁V : V₁ = prod.fst '' V) (hV₁W : V₁ = prod.fst '' W)
  (hV₁V0 : ∀ (x : Ω₁), x ∉ V₁ → P₂ (prod.mk x ⁻¹' V) = 0)
  (hV₁W0 : ∀ (x : Ω₁), x ∉ V₁ → P₂ (prod.mk x ⁻¹' W) = 0)
  (h : ∀ ω₁ : Ω₁, P₂ (prod.mk ω₁ ⁻¹' V) ≤ ε * P₂ (prod.mk ω₁ ⁻¹' W) + δ) :
  (P₁ ⊗ P₂) V ≤
    ε * (P₁ ⊗ P₂) W + δ * P₁ (prod.fst '' V)  := 
calc 
  (P₁ ⊗ P₂) V = ∫⁻ (ω₁ : Ω₁) in V₁, P₂ (prod.mk ω₁ ⁻¹' V) ∂P₁ : 
  begin
    rw measure.prod_apply hV,
    apply set_lintegral_nonzero,
    sorry, --measurability
    exact hV₁V0,
    apply_instance
  end
  ... ≤ ∫⁻ (ω₁ : Ω₁) in V₁, ε * P₂ (prod.mk ω₁ ⁻¹' W) + δ ∂P₁ : 
  begin
    apply lintegral_mono,
    apply h,
  end
  ... = ε * ∫⁻ (ω₁ : Ω₁) in V₁, P₂ (prod.mk ω₁ ⁻¹' W) ∂P₁ + δ * P₁ V₁ : 
  begin
    have : measurable (λ (ω : Ω₁), P₂ (prod.mk ω ⁻¹' W)) := sorry,
    rw lintegral_add,
    rw lintegral_const,
    rw [measure.restrict_apply_univ],
    rw lintegral_const_mul,
    measurability,
  end
  ... = 
    ε * (P₁ ⊗ P₂) W + δ * P₁ V₁ :
  begin
    rw measure.prod_apply hW,
    rw ←set_lintegral_nonzero,
    sorry, --measurability
    apply hV₁W0,
    apply_instance
  end

lemma part1_step2 
  (h : ∀ ω₂ : Ω₂, P₁ ((λ ω₁, prod.mk ω₁ ω₂) ⁻¹' V) 
    ≤ ε * P₁ ((λ ω₁, prod.mk ω₁ ω₂) ⁻¹' W) + δ) :
  (P₁ ⊗ P₂) V ≤
    ε * (P₁ ⊗ P₂) W + δ := 
begin
  rw [← measure.prod_swap, measure.map_apply, measure.map_apply],
  apply part1_step1,
  measurability!
end

end part1

-- Type of possible databases:
variables {X : Type} [database_type X] (x₀ x₁ : X) (hx : database_type.neighboring x₀ x₁)

-- Possible outputs:
variables {O₁ O₂ : Type} [hO₁ : measurable_space O₁] [hO₂ : measurable_space O₂]

section part2

-- Mechanisms:
variables (M₁ : X → Ω₁ → O₁) [hM₁ : ∀ x : X, measurable (M₁ x)] 
          (M₂ : O₁ → X → Ω₂ → O₂) [hM₂ : ∀ (o₁ : O₁) (x : X), measurable (M₂ o₁ x)]

-- Set of views:
variables (𝒱 : set (O₁ × O₂))

variables (ε₁ ε₂ δ₁ δ₂ : ennreal)

include x₁ ε₂ δ₂ hP₁ hP₂ hO₁ hO₂ hx

lemma part2_step1 (hdp₂ : ∀ o₁, diff_private P₂ (M₂ o₁) ε₂ δ₂):
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱} ≤
    exp ε₂ * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₁ ω.2) ∈ 𝒱} + δ₂ := 
begin
  apply part1_step1,
  sorry, -- measurability
  sorry, -- measurability
  exact λ ω₁, hdp₂ (M₁ x₀ ω₁) x₀ x₁ {o₂ : O₂ | (M₁ x₀ ω₁, o₂) ∈ 𝒱} hx,
end

lemma part2_step2 (hdp₁ : diff_private P₁ M₁ ε₁ δ₁):
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₁ ω.2) ∈ 𝒱} ≤
    exp ε₁ * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂ (M₁ x₁ ω.1) x₁ ω.2) ∈ 𝒱} + δ₁ := 
begin
  apply part1_step2,
  sorry, -- measurability
  sorry, -- measurability
  exact λ ω₁, hdp₁ x₀ x₁ {o₁ : O₁ | (o₁, M₂ o₁ x₁ ω₁) ∈ 𝒱} hx
end

end part2

section part3

variables (𝒱 : ℕ → set (O₁ × O₂))

variables (I₂ : Type) [fintype I₂] -- only finite! not countable as in the paper.

-- Mechanisms:
variables (M₁ : X → Ω₁ → O₁) [hM₁ : ∀ x : X, measurable (M₁ x)] 
          (M₂ : I₂ → O₁ → X → Ω₂ → O₂) [hM₂ : ∀ (k : I₂) (o₁ : O₁) (x : X), measurable (M₂ k o₁ x)]

variables (ε₁ ε₂ δ₁ : ennreal) (δ₂ : I₂ → ennreal)

variables (K : O₁ → I₂)

open_locale big_operators

lemma part3 : (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (K (M₁ x₀ ω.1)) (M₁ x₀ ω.1) x₀ ω.2) ∈ ⋃ k, 𝒱 k}
  ≤ (ε₁ + ε₂) * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂ (K (M₁ x₁ ω.1)) (M₁ x₁ ω.1) x₁ ω.2) ∈ ⋃ k, 𝒱 k} + δ₁ + ∑ k, δ₂ k

end part3