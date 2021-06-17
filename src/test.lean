import measure_theory.prod
import .dp
import .missing_integration

open measure_theory ennreal

-- Underlying probablity spaces:
variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂]

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) {hP₁ : sigma_finite P₁} {hP₂ : sigma_finite P₂}

-- Type of possible databases:
variables {X : Type} [database_type X] (x₀ x₁ : X) (hx : database_type.neighboring x₀ x₁)

-- Possible outputs:
variables {O₁ O₂ : Type} [hO₁ : measurable_space O₁] [hO₂ : measurable_space O₂]

-- Mechanisms:
variables (M₁ : X → Ω₁ → O₁) [hM₁ : ∀ x : X, measurable (M₁ x)] 
          (M₂ : O₁ → X → Ω₂ → O₂) [hM₂ : ∀ (o₁ : O₁) (x : X), measurable (M₂ o₁ x)]

-- Set of views:
variables (𝒱' : set (O₁ × O₂))

variables (ε₁ ε₂ δ₁ δ₂ : ennreal)

variables (hdp₁ : diff_private P₁ M₁ ε₁ δ₁)
variables (hdp₂ : ∀ o₁, diff_private P₂ (M₂ o₁) ε₂ δ₂)


lemma zero_outside_Ω₁' : 
  let Ω₁' := M₁ x₀ ⁻¹' (prod.fst '' 𝒱') in
  ∀ ω ∉ Ω₁', P₂ {a : Ω₂ | (M₁ x₀ ω, M₂ (M₁ x₀ ω) x₁ a) ∈ 𝒱'} = 0 :=
begin
  intros Ω₁' ω₁ hω₁,
  convert measure_empty,
  rw set.eq_empty_iff_forall_not_mem,
  intros ω₂ hω₂,
  dsimp [Ω₁'] at hω₁,
  rw set.mem_preimage at hω₁,
  rw set.mem_image at hω₁,
  refine hω₁ ⟨_, hω₂, _⟩,
  refl
end


local infix ` ⊗ `:50  := measure.prod

include x₁ ε₂ δ₂ hP₂ hdp₂ hO₂ hx
example :
  let Ω₁' := M₁ x₀ ⁻¹' (prod.fst '' 𝒱') in
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱'} ≤
    exp ε₂ * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₁ ω.2) ∈ 𝒱'} +
           δ₂ * P₁ Ω₁' := 
begin
  let Ω₁' := M₁ x₀ ⁻¹' (prod.fst '' 𝒱'),
  calc 
    (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱'} 
      = ∫⁻ (ω₁ : Ω₁) in Ω₁', P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₀ ω₂) ∈ 𝒱'} ∂P₁ : 
    begin
      rw measure.prod_apply sorry, --measurability
      simp only [set.preimage_set_of_eq], 
      apply set_lintegral_nonzero,
      sorry, --measurability
      exact zero_outside_Ω₁' P₂ x₀ x₀ M₁ M₂ 𝒱',
      exact hP₂ 
    end
   ... ≤ ∫⁻ (ω₁ : Ω₁) in Ω₁', exp ε₂ * P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₁ ω₂) ∈ 𝒱'} + δ₂ ∂P₁ : 
    begin
      apply lintegral_mono,
      intro ω₁,
      apply hdp₂ (M₁ x₀ ω₁) x₀ x₁ {o₂ : O₂ | (M₁ x₀ ω₁, o₂) ∈ 𝒱'} hx,
    end
   ... = ∫⁻ (ω₁ : Ω₁) in Ω₁', exp ε₂ * P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₁ ω₂) ∈ 𝒱'} ∂P₁ +
           δ₂ * P₁ Ω₁' :
    begin
      rw lintegral_add,
      rw set_lintegral_const,
      measurability,
      sorry -- measurability
    end
  ... = exp ε₂ * ∫⁻ (ω₁ : Ω₁) in Ω₁', P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₁ ω₂) ∈ 𝒱'} ∂P₁ +
           δ₂ * P₁ Ω₁' :
    begin
      rw lintegral_const_mul,
      sorry, -- measurability
    end
  ... = exp ε₂ * ∫⁻ (ω₁ : Ω₁), P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₁ ω₂) ∈ 𝒱'} ∂P₁ +
           δ₂ * P₁ Ω₁' :
    begin
      rw ←set_lintegral_nonzero,
      sorry, --measurability
      exact zero_outside_Ω₁' P₂ x₀ x₁ M₁ M₂ 𝒱'
    end
  ... = exp ε₂ * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₁ ω.2) ∈ 𝒱'} +
           δ₂ * P₁ Ω₁' : 
    begin
      rw measure.prod_apply sorry,
      simp only [set.preimage_set_of_eq], 
      exact hP₂ 
    end
end