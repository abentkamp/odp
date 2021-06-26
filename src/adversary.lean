import .dp
import measure_theory.pi
import measure_theory.giry_monad

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) (O : Type) [measurable_space O]

variables (X : Type) [database_type X] 

structure adversary_choice (ε δ : ℝ≥0∞) :=
(M : X → Ω → O)
(odp_partition : odp_partition P M)
(hε : odp_partition.ε ≤ ε)
(hδ : odp_partition.δ ≤ δ)
(hε_for : ∀ i, odp_partition.ε_for i ≤ ε)
(x : bool → X)
(hx : neighboring (x ff) (x tt))

def adversary := Π (outputs : list O) (ε δ : ℝ≥0∞), adversary_choice P O X ε δ

variables {P} {O} {X} (𝒜 : adversary P O X)

open_locale matrix
open matrix

noncomputable def odp_composition₀_aux (bit : bool) : 
  Π (acc : list O) (ε δ : ℝ≥0∞) (ω : list Ω), list O
| acc ε δ [] := acc
| acc ε δ (ω :: ωs) := 
  let 𝒜_choice := 𝒜 acc ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
  let acc := acc ++ [o] in
  let ε := ε - εusage 𝒜_choice.odp_partition o in
  let δ := δ - δusage 𝒜_choice.odp_partition o in
  odp_composition₀_aux acc ε δ ωs

noncomputable def odp_composition₀ (bit : bool) : Π (ε δ : ℝ≥0∞) (ωs : list Ω), list O := 
odp_composition₀_aux 𝒜 bit []

variables (bit : bool) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

lemma append_odp_composition₀_aux : 
  acc₁ ++ (odp_composition₀_aux (λ os, 𝒜 (acc₁ ++ os)) bit acc₂ ε δ ωs)
  = odp_composition₀_aux 𝒜 bit (acc₁ ++ acc₂) ε δ ωs :=
begin
  induction ωs generalizing acc₂ ε δ,
  { simp [odp_composition₀_aux] },
  { unfold odp_composition₀_aux,
    simp [ωs_ih] }
end

lemma append_odp_composition₀_aux' : 
  acc ++ (odp_composition₀_aux (λ os, 𝒜 (acc ++ os)) bit [] ε δ ωs) 
    = odp_composition₀_aux 𝒜 bit acc ε δ ωs :=
by simp [append_odp_composition₀_aux 𝒜 bit acc [] ε δ ωs]

lemma cons_odp_composition₀_aux : 
  o :: (odp_composition₀_aux (λ os, 𝒜 (o :: os)) bit [] ε δ ωs) 
    = odp_composition₀_aux 𝒜 bit [o] ε δ ωs :=
by {rw ←append_odp_composition₀_aux' 𝒜 bit [o] ε δ ωs, simp}

lemma odp_composition₀_nil : 
  odp_composition₀ 𝒜 bit ε δ [] = [] := rfl

lemma odp_composition₀_cons : 
  odp_composition₀ 𝒜 bit ε δ (ω :: ωs) = 
  let 𝒜_choice := 𝒜 [] ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
  let ε' := ε - εusage 𝒜_choice.odp_partition o in
  let δ' := δ - δusage 𝒜_choice.odp_partition o in
  let 𝒜' := (λ os, 𝒜 (o :: os)) in
  o :: odp_composition₀ 𝒜' bit ε' δ' ωs := 
by simp [odp_composition₀, odp_composition₀_aux, cons_odp_composition₀_aux]

@[simp]
lemma length_odp_composition₀ : 
  (odp_composition₀ 𝒜 bit ε δ ωs).length = ωs.length :=
begin
  induction ωs generalizing 𝒜 ε δ,
  { refl },
  { simp [odp_composition₀_cons, ωs_ih] }
end

-- TODO: move
def fin.to_list {α : Type*} : Π {n : ℕ} (a : fin n → α), list α
| 0 a := []
| (n + 1) a := vec_head a :: fin.to_list (vec_tail a)

-- TODO: move
def list.to_fin {α : Type*} : Π (l : list α), fin (l.length) → α
| [] := ![]
| (x :: xs) := vec_cons x (xs.to_fin)

-- TODO: move
@[simp]
lemma fin.length_to_list {α : Type*} : ∀ {n : ℕ} (a : fin n → α),
  (fin.to_list a).length = n
| 0 a := rfl
| (n + 1) a := by simp [fin.to_list, fin.length_to_list]

noncomputable def odp_composition (n : ℕ) (bit : bool) (ε δ : ℝ≥0∞) (ωs : fin n → Ω) : fin n → O := 
cast (by rw [length_odp_composition₀, fin.length_to_list]) 
  (odp_composition₀ 𝒜 bit ε δ (fin.to_list ωs)).to_fin

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ), 
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

-- TODO: move
lemma measure.pi_eq_pi' {ι : Type*} {α : ι → Type*} [fintype ι] [encodable ι]
  [∀ (i : ι), measurable_space (α i)] (μ : Π (i : ι), measure (α i)) [∀ (i : ι), sigma_finite (μ i)] : 
  measure.pi μ = measure.pi' μ :=
begin
  apply measure.pi_eq,
  apply measure.pi'_pi,
end

open finset

-- TODO: move?
lemma measure.pi_succ {n : ℕ} (α : fin n.succ → Type) [∀ i, measurable_space (α i)] 
  (μ : Π (i : fin n.succ), measure (α i)) [∀ i, sigma_finite (μ i)] : 
  measure.pi (λ i, μ i) = 
    measure.map (λ x : α 0 × Π (i : fin n), α i.succ, fin.cons x.1 x.2)
        ((μ 0).prod (measure.pi (λ i : fin n, μ i.succ))) := 
begin
  apply measure.pi_eq,
  intros s hs,
  rw measure.map_apply,
  have : (λ (x : α 0 × Π (i : fin n), α (fin.succ i)), fin.cons x.fst x.snd) ⁻¹' set.pi set.univ s
    = (s 0).prod (set.pi set.univ (λ i, s (fin.succ i))),
  { ext,
    rw set.mem_prod,
    rw set.mem_preimage,
    rw set.mem_univ_pi,
    rw set.mem_univ_pi,
    split,
    { intro h,
      refine ⟨h 0, _⟩,
      intro i,
      have := h i.succ,
      rwa ←fin.cons_succ _ x.snd i },
    { intros h i,
      rcases i with ⟨i, hi⟩,
      cases h with h₁ h₂,
      cases i,
      { exact (fin.cons_zero x.fst x.snd).symm ▸ h₁ },
      { exact (fin.cons_succ x.fst x.snd ⟨i, nat.succ_lt_succ_iff.1 hi⟩).symm 
          ▸ h₂ ⟨i, nat.succ_lt_succ_iff.1 hi⟩} } },
  rw this,
  rw [measure.prod_prod, measure.pi_pi],

  calc (μ 0) (s 0) * finset.univ.prod (λ (i : fin n), (μ i.succ) (s i.succ)) 
      = (μ 0) (s 0) * (finset.univ.erase 0).prod (λ (i : fin n.succ), (μ i) (s i)) :
    begin
      congr' 1,
      convert (finset.prod_map finset.univ ⟨fin.succ, fin.succ_injective n⟩ (λ i, (μ i) (s i))).symm,
      ext i,
      split,
      { intro h,
        rw mem_map,
        use fin.pred i (finset.mem_erase.1 h).1,
        refine ⟨mem_univ _, _⟩,
        simp only [fin.succ_pred, function.embedding.coe_fn_mk] },
      { intro hi, 
        apply finset.mem_erase.2,
        obtain ⟨i', _, hi'⟩ : ∃ i' _, fin.succ i' = i := mem_map.1 hi,
        simp [hi'.symm, fin.succ_ne_zero], }
    end
  ... = (insert (0 : fin n.succ) (finset.univ.erase 0)).prod (λ (i : fin n.succ), (μ i) (s i)) :
    begin
      rw finset.prod_insert,
      apply finset.not_mem_erase
    end
  ... = finset.univ.prod (λ (i : fin n.succ), (μ i) (s i)) : 
    begin 
      rw finset.insert_erase, 
      apply finset.mem_univ
    end,
  { intro h, apply hs },
  { exact hs 0 },
  { apply measurable_set.univ_pi_fintype,
    intro h, apply hs },
  { unfold measurable,
    intros t ht, sorry},
  { apply measurable_set.univ_pi_fintype, intro h, apply hs },
end

theorem main (n : ℕ) :
diff_private_aux (P ^^ n)
  (odp_composition 𝒜 n ff ε δ)
  (odp_composition 𝒜 n tt ε δ) ε δ :=
begin
  cases n,
  { sorry },
  { simp only,
    rw [measure.pi_succ (λ i, Ω) (λ i, P)],
    unfold diff_private_aux,
    intro s,
    rw [measure.map_apply, measure.map_apply],
    rw [set.preimage_set_of_eq, set.preimage_set_of_eq],
    revert s,
    change diff_private_aux (P ⊗ P ^^ n)
      (λ x, odp_composition 𝒜 n.succ ff ε δ (fin.cons x.fst x.snd))
      (λ x, odp_composition 𝒜 n.succ tt ε δ (fin.cons x.fst x.snd)) ε δ,

 -- TODO: use `cons_odp_composition₀_aux` to make `induction_step` from `test4` applicable
    }
end