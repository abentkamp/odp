
import measure_theory.pi
import measure_theory.giry_monad
import data.matrix.notation
import .missing_matrix

open measure_theory 

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ), 
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

lemma measure.pi_eq_pi' {ι : Type*} {α : ι → Type*} [fintype ι] [encodable ι]
  [∀ (i : ι), measurable_space (α i)] (μ : Π (i : ι), measure (α i)) [∀ (i : ι), sigma_finite (μ i)] : 
  measure.pi μ = measure.pi' μ :=
begin
  apply measure.pi_eq,
  apply measure.pi'_pi,
end

open finset

@[measurability] lemma measurable.pi_fin {n : ℕ}
  {α : fin n.succ → Type} [∀ i, measurable_space (α i)] {β : Type} [measurable_space β] {f : β → Πi, α i}
  (hf₁ : measurable (λ a : β, (f a) 0))
  (hf₂ : measurable (λ a, fin.tail (f a))) :
  measurable f :=
begin
  rw measurable_pi_iff,
  rintro ⟨k, hk⟩,
  cases k,
  exact hf₁,
  rw measurable_pi_iff at hf₂,
  exact hf₂ ⟨k, nat.lt_of_succ_lt_succ hk⟩
end 

-- TODO: move
def fin.cases_last {n : ℕ}
  {C : fin (n.succ) → Sort*} 
  (Hi : Π i : fin n, C ⟨i.1, nat.lt_succ_of_lt i.2⟩) 
  (Hn : C ⟨n, n.lt_succ_self⟩) :
  Π (i : fin (n.succ)), C i :=
begin
  intro i,
  by_cases hin : i < ⟨n, n.lt_succ_self⟩,
  { convert Hi ⟨i.1, hin⟩,
    ext, refl },
  { have : i = ⟨n, n.lt_succ_self⟩,
    { ext,
      apply nat.eq_of_lt_succ_of_not_lt i.2 hin },
    rw this,
    apply Hn }
end

@[measurability] lemma measurable.pi_fin' {n : ℕ}
  {α : fin n.succ → Type} [∀ i, measurable_space (α i)] {β : Type} [measurable_space β] {f : β → Πi, α i}
  (hf₁ : measurable (λ a, fin.init (f a)))
  (hf₂ : measurable (λ a : β, (f a) ⟨n, n.lt_succ_self⟩)) :
  measurable f :=
begin
  rw measurable_pi_iff,
  refine fin.cases_last _ _,
  { rwa measurable_pi_iff at hf₁ },
  { apply hf₂ },
end 

@[measurability]
lemma measurable.fin_cons {n : ℕ} {α : fin n.succ → Type} {β : Type} [∀ i, measurable_space (α i)] [measurable_space β]
  {f : β → α 0} {g : β → Π (i : fin n), α i.succ}
  (hf : measurable f) (hg : measurable g) :
  measurable (λ (x : β), fin.cons (f x) (g x)) :=
begin
  apply measurable.pi_fin,
  apply hf,
  simp_rw fin.tail_cons,
  apply hg,
end

@[measurability]
lemma measurable.fin_snoc {n : ℕ} {α : fin n.succ → Type} {β : Type} 
  [∀ i, measurable_space (α i)] [measurable_space β]
  {f : β → Π (i : fin n), α i.cast_succ} {g : β → α (fin.last n)}
  (hf : measurable f) (hg : measurable g) :
  measurable (λ (x : β), fin.snoc (f x) (g x)) :=
begin
  apply measurable.pi_fin',
  simp_rw fin.init_snoc,
  apply hf,
  change measurable (λ (a : β), fin.snoc (f a) (g a) (fin.last _)),
  simp_rw fin.snoc_last,
  apply hg,
end

@[measurability]
lemma measurable.vec_cons {n : ℕ} {α β : Type} [measurable_space α] [measurable_space β]
  {f : β → α} {g : β → fin n → α}
  (hf : measurable f) (hg : measurable g) :
  measurable (λ x, matrix.vec_cons (f x) (g x)) :=
measurable.fin_cons hf hg

@[measurability]
lemma measurable.vec_snoc {n : ℕ} {α β : Type} [measurable_space α] [measurable_space β]
  {f : β → fin n → α} {g : β → α}
  (hf : measurable f) (hg : measurable g) :
  measurable (λ x, matrix.vec_snoc (f x) (g x)) := sorry

@[measurability]
lemma measurable.vec_head {n : ℕ} {α : Type*} [measurable_space α] :
  measurable (λ (x : fin (n + 1) → α), matrix.vec_head x) :=
begin
  unfold matrix.vec_head,
  measurability,
end

@[measurability]
lemma measurable.vec_tail {n : ℕ} {α : Type*} [measurable_space α] :
  measurable (λ (x : fin (n + 1) → α), matrix.vec_tail x) :=
begin
  unfold matrix.vec_tail,
  measurability,
end

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
  { apply measurable.fin_cons, -- TODO: Why does measurability not work here?
    measurability },
  { apply measurable_set.univ_pi_fintype, intro h, apply hs },
end

lemma measure_theory.finite_measure.map {α β : Type*} [measurable_space α] [measurable_space β] (μ : measure α) [finite_measure μ]
  {f : α → β} (hf : measurable f) : finite_measure (measure.map f μ) := 
⟨begin 
  rw measure.map_apply hf, 
  apply measure_lt_top, 
  measurability 
end⟩ 

lemma measure_theory.finite_measure.smul {α : Type*} [measurable_space α] (μ : measure α) [finite_measure μ]
  {a : ennreal} (ha : a < ⊤): finite_measure (a • μ) := 
⟨begin 
  rw measure.smul_apply, 
  apply ennreal.mul_lt_top ha,
  apply measure_lt_top,
end⟩ 

instance pi.probability_measure {α : Type*} [measurable_space α] (P : measure α) (n : ℕ) [probability_measure P] : 
  probability_measure (P ^^ n) :=
⟨begin 
  rw [←set.pi_univ, measure.pi_pi, finset.prod_eq_one], 
  simp [probability_measure.measure_univ], 
  measurability, 
end⟩