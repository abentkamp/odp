/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import .diff_private .missing_measure .missing_matrix
/-
This file defines the role of the adversary and the ODP algorithm.
-/

open measure_theory ennreal database_type matrix
open_locale ennreal
open_locale matrix

/- `Ω` is a sample space with an associated probability measure `P`. -/
variables {Ω : Type} [measurable_space Ω] (P : measure Ω) [probability_measure P]

/- `Ωₐ` is a sample space with an associated probability measure `Pₐ`.
   They are used for randomization of the adversary's decisions. -/
variables (Ωₐ : Type) [measurable_space Ωₐ] (Pₐ : measure Ωₐ) [probability_measure Pₐ]

/- `O` is the type of outputs of meachanisms. -/
variables (O : Type) [measurable_space O]

/- `X` is a type of databases. -/
variables (X : Type) [database_type X] [measurable_space X]

/-- At each iteration of the algorithm, the adversary can choose an ODP
mechanism and two neighboring databases. The ODP mechanism must not exceed the
remaining ε-δ-budget. -/
structure adversary_choice (ε δ : ℝ≥0∞) :=
(M : X → Ω → O)
(odp_partition : odp_partition P M)
(hδ : odp_partition.δ ≤ δ)
(hε_for : ∀ i, odp_partition.ε_for i ≤ ε)
(x : fin 2 → X)
(hx : neighboring (x 0) (x 1))

/-- The structure `adversary_n` represents an adversary after `n` iterations.
Given `n` outputs and the remaining ε-δ-budget, the adversary must make a
choice. There a couple of measurability requirements on the adversary
as a function from previous outputs and budget to the adversary's choice. -/
structure adversary_n (n : ℕ) :=
(choose : Π (ωₐ : Ωₐ) (outputs : fin n → O) (ε δ : ℝ≥0∞), adversary_choice P O X ε δ)
(measurable_M :
  ∀ {α : Type} [measurable_space α] {ωₐ : α → Ωₐ} {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞} {x : α → X} {ω : α → Ω},
  measurable ωₐ → measurable os → measurable ε → measurable δ → measurable x → measurable ω →
  measurable (λ (a : α), (choose (ωₐ a) (os a) (ε a) (δ a) ).M (x a) (ω a)))
(measurable_x :
  ∀ (bit : fin 2)  {α : Type} [measurable_space α] {ωₐ : α → Ωₐ} {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable ωₐ → measurable os → measurable ε → measurable δ →
  measurable (λ (a : α), (choose (ωₐ a) (os a) (ε a) (δ a)).x bit))
(measurable_ε :
  ∀ {α : Type} [measurable_space α] {ωₐ : α → Ωₐ} {os : α → (fin n → O)} {o : α → O} {ε δ : α → ℝ≥0∞},
  measurable ωₐ → measurable os → measurable o → measurable ε →  measurable δ →
  measurable (λ (a : α), εusage (choose (ωₐ a) (os a) (ε a) (δ a)).odp_partition (o a)))
(measurable_δ :
  ∀ {α : Type} [measurable_space α] {ωₐ : α → Ωₐ} {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable ωₐ → measurable os → measurable ε → measurable δ →
  measurable (λ (a : α), (choose (ωₐ a) (os a) (ε a) (δ a)).odp_partition.δ))

/-- An adversary is a collection of `adversary_n` structures for each number of
iterations `n`. -/
def adversary := Π (n : ℕ), adversary_n P Ωₐ O X n

variables {P} {Ωₐ} {O} {X} (𝒜 : adversary P Ωₐ O X)

/-- We can produce an adversary for `n` previous outputs from an adversary for
`n + 1` previous outputs by informing them about a new output. -/
def inform_n {n : ℕ} (𝒜 : adversary_n P Ωₐ O X (n+1)) (o : O) : adversary_n P Ωₐ O X n :=
⟨λ ωₐ os, 𝒜.choose ωₐ (vec_cons o os),
begin
  intros,
  apply 𝒜.measurable_M _ (measurable.fin_cons _ _),
  measurability
end,
begin
  intros,
  apply 𝒜.measurable_x _ _ (measurable.fin_cons _ _),
  measurability
end,
begin
  intros,
  apply 𝒜.measurable_ε _ (measurable.fin_cons _ _),
  measurability
end,
begin
  intros,
  apply 𝒜.measurable_δ _ (measurable.fin_cons _ _),
  measurability
end⟩

/-- The adversary `inform 𝒜 o` is `𝒜` after having been informed about a new
output `o`. -/
def inform (𝒜 : adversary P Ωₐ O X) (o : O) : adversary P Ωₐ O X :=
λ n, inform_n (𝒜 (n+1)) o

/-- The adversary `inform_vec 𝒜 m os` is `𝒜` after having been informed about
`m` new outputs `os`. -/
def inform_vec : adversary P Ωₐ O X → Π (m : ℕ), (fin m → O) → adversary P Ωₐ O X
| 𝒜 0 os := 𝒜
| 𝒜 (m+1) os := inform (inform_vec 𝒜 m (vec_butlast os)) (vec_last os)

lemma inform_inform_vec_comm (𝒜 : adversary P Ωₐ O X) {m : ℕ} (os : fin m.succ → O) :
inform (inform_vec 𝒜 m (vec_butlast os)) (vec_last os)
= inform_vec (inform 𝒜 (vec_head os)) m (vec_tail os)
:= begin
  induction m with m ih,
  { refl },
  { unfold inform_vec,
  rw ih,
  rw [head_butlast, last_tail, butlast_tail], }
end

lemma inform_vec_choose (𝒜 : adversary P Ωₐ O X) {m : ℕ} (os : fin m → O) (ωₐ : Ωₐ) :
(inform_vec 𝒜 m os 0).choose ωₐ ![] = (𝒜 m).choose ωₐ os :=
begin
  induction m with m ih generalizing os 𝒜,
  { unfold inform_vec, congr' },
  { unfold inform_vec,
    rw inform_inform_vec_comm,
    rw ih,
    unfold inform,
    unfold inform_n,
    unfold adversary_n.choose,
    simp, }
end

lemma inform_inform_vec (𝒜 : adversary P Ωₐ O X) (m : ℕ) (o : O) (os : fin m → O) :
  inform (inform_vec 𝒜 m os) o = inform_vec 𝒜 (m+1) (vec_snoc os o) :=
by rw [inform_vec, butlast_snoc, last_snoc]

/-- This is the main algorithm. -/
noncomputable def odp_composition : 
  Π (𝒜 : adversary P Ωₐ O X) (n : ℕ) (bit : fin 2) (ωₐ : Ωₐ) (ε δ : ℝ≥0∞) (ωs : fin n → Ω), fin n → O
| 𝒜 0 bit ωₐ ε δ ωs := ![]
| 𝒜 (n+1) bit ωₐ ε δ ωs :=
-- At each iteration:
  -- The adversary makes a choice, possibly based on the random sampling `ωₐ`.
  let 𝒜_choice := (𝒜 0).choose ωₐ ![] ε δ in
  -- We sample the chosen meachanism.
  let o := 𝒜_choice.M (𝒜_choice.x bit) (vec_head ωs) in
  -- We calculate the remaining `ε`-budget.
  let ε' := ε - εusage 𝒜_choice.odp_partition o in
  -- We calculate the remaining `δ`-budget.
  let δ' := δ - 𝒜_choice.odp_partition.δ in
  -- We inform the adversary about the new output.
  let 𝒜' := inform 𝒜 o in
  -- We return the output and enter the next iteration for the remaining outputs.
  vec_cons o (odp_composition 𝒜' n bit ωₐ ε' δ' (vec_tail ωs))


/-- This auxiliary definition is a fragment of the `odp_composition` algortithm,
but assumes that the current output `o` has already been sampled. -/
noncomputable def odp_composition₀ (o : O) (n : ℕ) (bit : fin 2) (ωₐ : Ωₐ) (ε δ : ℝ≥0∞) (ω : fin n → Ω) :=
  let 𝒜_choice : adversary_choice P O X ε δ := (𝒜 0).choose ωₐ ![] ε δ in
  let ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o in
  let δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ in
  let 𝒜' := inform 𝒜 o in
  odp_composition 𝒜' n bit ωₐ ε' δ' ω

/-- The algorithm `odp_composition` is measurable.

Note: I haven't been able to prove this using an adversary that gets fed a list instead of a vector
because lists are currently not instantiated as a measurable space.
-/
lemma measurable_odp_composition (bit : fin 2) {n : ℕ} {α : Type} [measurable_space α]
  (m : ℕ) (ωₐ : α → Ωₐ) (os : α → (fin m → O)) (ε δ : α → ℝ≥0∞) (ω : α → (fin n → Ω))
  (hωₐ : measurable ωₐ) (hos : measurable os) (hε : measurable ε) (hδ : measurable δ) (hω : measurable ω) :
  measurable (λ a : α, odp_composition (inform_vec 𝒜 m (os a)) n bit (ωₐ a) (ε a) (δ a) (ω a)) :=
begin
  induction n with n ih generalizing m ωₐ ε δ os,
  case zero { show measurable (λ ω, ![]), by apply measurable_const },
  case succ { show measurable (λ a, odp_composition (inform_vec 𝒜 m (os a)) (n+1) bit (ωₐ a) (ε a) (δ a) (ω a)),
    suffices : measurable (λ a, odp_composition (inform_vec 𝒜 m (os a)) (n+1) bit (ωₐ a) (ε a) (δ a) (vec_cons (vec_head (ω a)) (vec_tail (ω a)))),
      by simpa only [cons_head_tail] using this,
    unfold odp_composition,
    apply measurable.fin_cons,
    { simp_rw [cons_head_tail, inform_vec_choose 𝒜],
      apply (𝒜 m).measurable_M hωₐ hos hε hδ _ (measurable.comp measurable.vec_head hω),
      apply (𝒜 m).measurable_x bit hωₐ hos hε hδ, },
    { simp_rw [inform_inform_vec, matrix.cons_head_tail, inform_vec_choose 𝒜],
      apply ih (λ a, vec_tail (ω a)) _ (m+1),
      exact hωₐ,
      apply measurable.vec_snoc,
      exact hos,
      apply (𝒜 m).measurable_M hωₐ hos hε hδ _ (measurable.comp measurable.vec_head hω),
      apply (𝒜 m).measurable_x bit hωₐ hos hε hδ,
      { apply measurable.sub hε, --TODO: why can't I rewrite inform_vec_choose here?
        suffices : measurable (λ (a : α),
          εusage (( 𝒜 m ).choose (ωₐ a) (os a) (ε a) (δ a)).odp_partition
            (((𝒜 m).choose (ωₐ a) (os a) (ε a) (δ a)).M (((𝒜 m).choose (ωₐ a) (os a) (ε a) (δ a)).x bit) (vec_head (ω a)))),
        { convert this, apply funext, intro i,
          rw inform_vec_choose 𝒜 (os i) },
        refine (𝒜 m).measurable_ε hωₐ hos _ hε hδ,
        apply (𝒜 m).measurable_M hωₐ hos hε hδ _ (measurable.comp measurable.vec_head hω),
        apply (𝒜 m).measurable_x bit hωₐ hos hε hδ, },
      { apply measurable.sub hδ,
        suffices : measurable (λ (a : α),
          ((𝒜 m).choose (ωₐ a) (os a) (ε a) (δ a)).odp_partition.δ),
        { convert this, apply funext, intro i,
          rw inform_vec_choose 𝒜 (os i) },
        exact (𝒜 m).measurable_δ hωₐ hos hε hδ },
      exact measurable.comp measurable.vec_tail hω } }
end

/-- The algorithm `odp_composition` with a deterministic adversary is
measurable. This is a special case of `measurable_odp_composition` above. -/
lemma measurable_odp_composition_det (bit : fin 2) (ωₐ : Ωₐ) (ε δ : ℝ≥0∞) {n : ℕ}:
  measurable (odp_composition 𝒜 n bit ωₐ ε δ) :=
begin
  apply measurable_odp_composition
    𝒜 bit 0 (λ_, ωₐ) (λ_, ![]) (λ_, ε) (λ_, δ) (λ ω, ω),
  measurability,
end

/-- The algorithm `odp_composition` with a nondeterministic adversary is
measurable. This is a special case of `measurable_odp_composition` above. -/
lemma measurable_odp_composition_nondet (bit : fin 2) (ε δ : ℝ≥0∞) {n : ℕ}:
  measurable (λ (ω : Ωₐ × (fin n → Ω)), odp_composition 𝒜 n bit ω.1 ε δ ω.2) :=
begin
  apply measurable_odp_composition
    𝒜 bit 0 (λ (ω : Ωₐ × (fin n → Ω)), ω.1) (λ_, ![]) (λ_, ε) (λ_, δ) (λ ω, ω.2),
  measurability,
end

lemma measurable_odp_composition₀ (bit : fin 2) (ωₐ : Ωₐ) (ε δ : ℝ≥0∞) {n : ℕ} :
  measurable (λ (oω : O × (fin n → Ω)), odp_composition₀ 𝒜 oω.1 n bit ωₐ ε δ oω.2) :=
begin
  apply measurable_odp_composition 𝒜 bit 1 
    (λ _, ωₐ)
    (λ oω : O × (fin n → Ω), ![oω.1])
    (λ oω : O × (fin n → Ω), ε - εusage ((𝒜 0).choose ωₐ vec_empty ε δ).odp_partition oω.fst)
    (λ oω : O × (fin n → Ω), δ - ((𝒜 0).choose ωₐ vec_empty ε δ).odp_partition.δ)
    (λ oω : O × (fin n → Ω), oω.2),
  { measurability },
  apply measurable.vec_cons,
  measurability
end