import .dp .missing .missing_measure .missing_matrix

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) (O : Type) [measurable_space O]

variables (X : Type) [database_type X] [measurable_space X] -- TODO: What does it mean for X to be measurable?

structure adversary_choice (ε δ : ℝ≥0∞) :=
(M : X → Ω → O)
(odp_partition : odp_partition P M)
(hε : odp_partition.ε ≤ ε)
(hδ : odp_partition.δ ≤ δ)
(hε_for : ∀ i, odp_partition.ε_for i ≤ ε)
(x : fin 2 → X)
(hx : neighboring (x 0) (x 1))

structure adversary_n (n : ℕ) :=
(choose : Π (outputs : fin n → O) (ε δ : ℝ≥0∞), adversary_choice P O X ε δ)
(measurable_M : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞} {x : α → X} {ω : α → Ω},
  measurable os → measurable ε → measurable δ → measurable x → measurable ω →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).M (x a) (ω a)))
(measurable_x : 
  ∀ (bit : fin 2) {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable os → measurable ε → measurable δ →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).x bit))
(measurable_ε : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {o : α → O} {ε δ : α → ℝ≥0∞},
  measurable os → measurable o → measurable ε →  measurable δ →
  measurable (λ (a : α), εusage (choose (os a) (ε a) (δ a)).odp_partition (o a)))
(measurable_δ : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable os → measurable ε →  measurable δ →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).odp_partition.δ))

def adversary := Π (n : ℕ), adversary_n P O X n

lemma εusage_for_le_ε {ε δ : ℝ≥0∞} (𝒜_choice : adversary_choice P O X ε δ) (i : option 𝒜_choice.odp_partition.index) : 
  εusage_for 𝒜_choice.odp_partition i ≤ ε := 
begin 
  cases i,
  apply 𝒜_choice.hε,
  apply 𝒜_choice.hε_for
end

variables {P} {O} {X} (𝒜 : adversary P O X)

open_locale matrix
open matrix

-- noncomputable def odp_composition₀_aux (bit : fin 2) : 
--   Π (acc : list O) (ε δ : ℝ≥0∞) (ω : list Ω), list O
-- | acc ε δ [] := acc
-- | acc ε δ (ω :: ωs) := 
--   let 𝒜_choice := 𝒜 acc ε δ in 
--   let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
--   let acc := acc ++ [o] in
--   let ε := ε - εusage 𝒜_choice.odp_partition o in
--   let δ := δ - 𝒜_choice.odp_partition.δ in
--   odp_composition₀_aux acc ε δ ωs

-- noncomputable def odp_composition₀ (bit : fin 2) : Π (ε δ : ℝ≥0∞) (ωs : list Ω), list O := 
-- odp_composition₀_aux 𝒜 bit []

-- variables (bit : fin 2) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

-- lemma append_odp_composition₀_aux : 
--   acc₁ ++ (odp_composition₀_aux (λ os, 𝒜 (acc₁ ++ os)) bit acc₂ ε δ ωs)
--   = odp_composition₀_aux 𝒜 bit (acc₁ ++ acc₂) ε δ ωs :=
-- begin
--   induction ωs generalizing acc₂ ε δ,
--   { simp [odp_composition₀_aux] },
--   { unfold odp_composition₀_aux,
--     simp [ωs_ih] }
-- end

-- lemma append_odp_composition₀_aux' : 
--   acc ++ (odp_composition₀_aux (λ os, 𝒜 (acc ++ os)) bit [] ε δ ωs) 
--     = odp_composition₀_aux 𝒜 bit acc ε δ ωs :=
-- by simp [append_odp_composition₀_aux 𝒜 bit acc [] ε δ ωs]

-- lemma cons_odp_composition₀_aux : 
--   o :: (odp_composition₀_aux (λ os, 𝒜 (o :: os)) bit [] ε δ ωs) 
--     = odp_composition₀_aux 𝒜 bit [o] ε δ ωs :=
-- by {rw ←append_odp_composition₀_aux' 𝒜 bit [o] ε δ ωs, simp}

-- lemma odp_composition₀_nil : 
--   odp_composition₀ 𝒜 bit ε δ [] = [] := rfl

-- lemma odp_composition₀_cons : 
--   odp_composition₀ 𝒜 bit ε δ (ω :: ωs) = 
--   let 𝒜_choice := 𝒜 [] ε δ in 
--   let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
--   let ε' := ε - εusage 𝒜_choice.odp_partition o in
--   let δ' := δ - 𝒜_choice.odp_partition.δ in
--   let 𝒜' := (λ os, 𝒜 (o :: os)) in
--   o :: odp_composition₀ 𝒜' bit ε' δ' ωs := 
-- by simp [odp_composition₀, odp_composition₀_aux, cons_odp_composition₀_aux]

-- @[simp]
-- lemma length_odp_composition₀ : 
--   (odp_composition₀ 𝒜 bit ε δ ωs).length = ωs.length :=
-- begin
--   induction ωs generalizing 𝒜 ε δ,
--   { refl },
--   { simp [odp_composition₀_cons, ωs_ih] }
-- end


def inform_n {n : ℕ} (𝒜 : adversary_n P O X (n+1)) (o : O) : adversary_n P O X n :=
⟨λ os, 𝒜.choose (vec_cons o os),
begin 
  intros,
  apply 𝒜.measurable_M,
  apply measurable.fin_cons,
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_x,
  apply measurable.fin_cons,
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_ε,
  apply measurable.fin_cons,
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_δ,
  apply measurable.fin_cons,
  measurability
end⟩

def inform (𝒜 : adversary P O X) (o : O) : adversary P O X :=
λ n, inform_n (𝒜 (n+1)) o

def inform_vec : adversary P O X → Π (m : ℕ), (fin m → O) → adversary P O X
| 𝒜 0 os := 𝒜
| 𝒜 (m+1) os := inform (inform_vec 𝒜 m (vec_butlast os)) (vec_last os)


lemma inform_inform_vec_comm (𝒜 : adversary P O X) {m : ℕ} (os : fin m.succ → O) : 
inform (inform_vec 𝒜 m (vec_butlast os)) (vec_last os) 
= inform_vec (inform 𝒜 (vec_head os)) m (vec_tail os)
:= begin
  induction m with m ih,
  { refl },
  { unfold inform_vec, 
  rw ih,
  rw [head_butlast, last_tail, butlast_tail], }
end

lemma inform_vec_choose (𝒜 : adversary P O X) {m : ℕ} (os : fin m → O) : 
(inform_vec 𝒜 m os 0).choose ![] = (𝒜 m).choose os :=
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

lemma inform_inform_vec (𝒜 : adversary P O X) (m : ℕ) (o : O) (os : fin m → O) : 
  inform (inform_vec 𝒜 m os) o = inform_vec 𝒜 (m+1) (vec_snoc os o) :=
by rw [inform_vec, butlast_snoc, last_snoc]

-- set_option pp.beta true
-- lemma inform_vec_choose₀ (𝒜 : adversary P O X) {m n : ℕ} (os : fin m → O) (os' : fin n → O) : 
--   (inform_vec 𝒜 m os n).choose os' = (𝒜 (n + m)).choose (fin.append (add_comm _ _) os os') :=
-- begin
--   induction m with m ih generalizing n,
--   { congr', simp [fin.append], },
--   {unfold inform_vec, unfold inform, unfold inform_n,
-- change (inform_vec
--      (λ (n : ℕ),
--         {choose := λ (os_1 : fin n → O), (𝒜 (n + 1)).choose (vec_cons (vec_head os) os_1),
--          measurable_M := _,
--          measurable_x := _,
--          measurable_ε := _,
--          measurable_δ := _})
--      m
--      (vec_tail os)
--      n).choose
--     os' =
--   (𝒜 (n + m.succ)).choose (fin.append _ os os'),

--   simp_rw [cons_head_tail],}
-- end


noncomputable def odp_composition : Π (𝒜 : adversary P O X) (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ωs : fin n → Ω), fin n → O
| 𝒜 0 bit ε δ ωs := ![]
| 𝒜 (n+1) bit ε δ ωs :=
  let 𝒜_choice := (𝒜 0).choose ![] ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) (vec_head ωs) in
  let ε' := ε - εusage 𝒜_choice.odp_partition o in
  let δ' := δ - 𝒜_choice.odp_partition.δ in
  let 𝒜' := inform 𝒜 o in
  vec_cons o (odp_composition 𝒜' n bit ε' δ' (vec_tail ωs))

-- lemma odp_composition_zero (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ωs : fin n → Ω) : 
--   odp_composition 𝒜 0 bit ε δ ![] = ![] := rfl

-- lemma odp_composition_succ (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ω : Ω) (ωs : fin n → Ω) : 
--   odp_composition 𝒜 n.succ bit ε δ (vec_cons ω ωs) = 
--   let 𝒜_choice := 𝒜 [] ε δ in 
--   let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
--   let ε' := ε - εusage 𝒜_choice.odp_partition o in
--   let δ' := δ - 𝒜_choice.odp_partition.δ in
--   let 𝒜' := (λ os, 𝒜 (o :: os)) in
--   vec_cons o (odp_composition 𝒜' n bit ε' δ' ωs) :=
-- begin
--   dunfold odp_composition,
--   have := odp_composition₀_cons 𝒜 bit ε δ ω (fin.to_list ωs),
--   rw [←fin.to_list_cons ω ωs] at this,
--   refine eq.trans _ (cast_vec_cons (by rw [length_odp_composition₀, fin.length_to_list]) _ _),
--   rw list.vec_cons_to_fin,
--   congr',
--   rw [length_odp_composition₀, fin.length_to_list],
--   rw [length_odp_composition₀, fin.length_to_list]
-- end
