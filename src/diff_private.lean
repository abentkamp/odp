/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import measure_theory.constructions.prod
import .missing_ennreal .missing_matrix .missing_measure
/-
This file defines differential privacy and output differential privacy.
-/

noncomputable theory
open measure_theory ennreal
open_locale ennreal
open_locale classical

/-- For our purposes, the type of databases is arbitrary, but it must have some
notion of neighboring databases. -/
class database_type (X : Type*) :=
(neighboring : X → X → Prop)
open database_type

/- `Ω` is a sample space with a probability measure `P` on it. -/
variables {Ω : Type} [measurable_space Ω] (P : measure Ω)

/- `O` is the type of outputs of mechanisms. -/
variables {O : Type} {O' : Type} [measurable_space O] [measurable_space O']

/- `X` is the type of databases. -/
variables {X : Type} [database_type X]

/- `M` is a mechanism, i.e., a randomized function from databases to outputs. -/
variables (M : X → Ω → O)

/- When considering compositions of mechanisms, the adversary can choose pairs
of databases at each iteration. The output of the mechanism then depends no longer
on a single database. For compositions we therefore use two random variables
`M₀` and `M₁`. -/
variables (M₀ : Ω → O) (M₁ : Ω → O)

/- `ε` and `δ` are parameters of the notion of differential privacy. -/
variables (ε δ : ℝ≥0∞)

/-- Differential privacy for a single mechanism -/
def diff_private :=
  ∀ (x y : X) (s : set O), measurable_set s → neighboring x y →
  P {ω : Ω | M x ω ∈ s} ≤ exp ε * P {ω : Ω | M y ω ∈ s} + δ

/-- Differential privacy for compositions M₀, M₁ of mechanisms -/
def diff_private_composition :=
  ∀ (s : set O) (hs : measurable_set s),
  P {ω : Ω | M₀ ω ∈ s} ≤ exp ε * P {ω : Ω | M₁ ω ∈ s} + δ

/-- Subset differential privacy -/
def subset_diff_private (r : set O) :=
  ∀ (x y : X) (s : set O), s ⊆ r → measurable_set s → neighboring x y →
  P {ω : Ω | M x ω ∈ s} ≤ exp ε * P {ω : Ω | M y ω ∈ s} + δ

/-- An ODP partition is a partition of the set of outputs `O` of a mechanism
into measurable subsets such that the `odp` inequality below is fulfilled.

The partition is realized by a function `partition` that assigns to every
possible output an index `i`. -/
structure odp_partition :=
(δ : ℝ≥0∞)
(index : Type)
[encodable : encodable index]
(partition : O → index)
(measurable_partition : ∀ i, measurable_set {o : O | partition o = i})
(ε_for : index → ℝ≥0∞)
(ε_for_lt_infty : ∀ i, ε_for i < ∞)
(odp : ∀ (x y : X) (s : set O), measurable_set s → neighboring x y →
  P {ω : Ω | M x ω ∈ s} 
    ≤ δ + ∑' i : index, exp (ε_for i) * P {ω : Ω | M y ω ∈ s ∩ {o : O | partition o = i}})

variables {P} {M}

/-- The ε-usage for a certain output id the ε associated with its partition. -/
def εusage (p : odp_partition P M) (o : O) := p.ε_for (p.partition o)

/-- The set of outputs associated with an index `i` -/
def odp_set_for (p : odp_partition P M) : p.index → set O :=
λ i, {o : O | p.partition o = i}

lemma partition_eq_of_mem_odp_set_for {p : odp_partition P M} {i : p.index}
  {o : O} (ho: o ∈ odp_set_for p i) :
  p.partition o = i := ho

lemma pairwise_disjoint_on_odp_set_for {p : odp_partition P M} :
  pairwise (disjoint on odp_set_for p) :=
begin
  rintros i j hij a ⟨ha₁, ha₂⟩,
  change p.partition a = i at ha₁,
  change p.partition a = j at ha₂,
  rw [←ha₁, ←ha₂] at hij,
  contradiction,
end

lemma εusage_eq_ε_for {p : odp_partition P M} {i : p.index}
  {o : O} (ho : o ∈ odp_set_for p i) :
  εusage p o = p.ε_for i :=
begin
  rw ← partition_eq_of_mem_odp_set_for ho,
  refl,
end

lemma mem_odp_set_for_odp_index (p : odp_partition P M) (o : O) :
  o ∈ odp_set_for p (p.partition o) :=
by simp [odp_set_for]

@[measurability]
lemma measurable_set_odp_set_for (p : odp_partition P M) (i : p.index) :
  measurable_set (odp_set_for p i) :=
p.measurable_partition i

/-- Since the type of indices is countable, we can assume that all its subsets
are measurable. -/
instance (p : odp_partition P M) : measurable_space p.index := ⊤

@[measurability]
lemma measurable_partition (p : odp_partition P M) :
  measurable (p.partition) :=
begin
  haveI : encodable p.index := p.encodable,
  intros s hs,
  rw ←set.bUnion_preimage_singleton,
  change measurable_set (⋃ i ∈ s, odp_set_for p i),
  measurability
end

lemma union_odp_set_for_eq_univ (p : odp_partition P M) : 
  (⋃ i, odp_set_for p i) = set.univ :=
begin
  apply set.eq_univ_of_forall,
  intros o,
  apply set.mem_Union.2,
  use p.partition o,
  apply mem_odp_set_for_odp_index
end

lemma split_set (p : odp_partition P M) (s : set (O × O')) :
  s = ⋃ (i : p.index), s ∩ (odp_set_for p i).prod set.univ :=
calc s = s ∩ (set.prod set.univ set.univ) : by simp
... = s ∩ ((set.Union (λ i, odp_set_for p i)).prod set.univ) :
  by rw ←union_odp_set_for_eq_univ _
... = s ∩ (⋃ (i : p.index), (odp_set_for p i).prod set.univ) : 
  by rw set.Union_prod_const
... = ⋃ (i : p.index), s ∩ (odp_set_for p i).prod set.univ : 
  by rw set.inter_Union

open matrix

lemma diff_private_composition_map_vec_head_vec_tail {Ω : Type} [measurable_space Ω]
  (P : measure Ω) {n : ℕ} (M₀ M₁ : Ω → fin n.succ → O) :
  let f := (λ o : fin n.succ → O, (vec_head o, vec_tail o)) in
  diff_private_composition P (λ ω, f (M₀ ω)) (λ ω, f (M₁ ω)) ε δ → diff_private_composition P M₀ M₁ ε δ :=
begin
  intros f h s hs,
  rw [←set.preimage_image_eq s (injective_head_tail n)],
  refine h (f '' s) _,
  have : measurable_set ((λ x : _ × _, vec_cons x.1 x.2) ⁻¹' s),
  { apply measurable.fin_cons,
    apply measurable_fst,
    apply measurable_snd,
    exact hs },
  convert this,
  exact equiv.image_eq_preimage (vec_cons.equiv n).symm s,
end

/-- If a mechanism is subset differential private on each element of a parition,
this partition is an ODP partition when summing up the deltas. (Lemma 6) -/
lemma odp_partition_of_subset_dp {ι : Type} [encodable ι]
  (p : O → ι) (hp : ∀ i, measurable_set {o | p o = i}) 
  (ε : ι → ℝ≥0∞) (δ : ι → ℝ≥0∞) (hε : ∀ i, ε i < ∞)
  (hM : ∀ x, measurable (M x))
  (h : ∀ i, subset_diff_private P M (ε i) (δ i) {o | p o = i}) :
  odp_partition P M :=
{ index := ι,
  partition := p,
  measurable_partition := hp,
  ε_for := ε,
  ε_for_lt_infty := hε,
  δ := ∑' i, δ i,
  odp := begin
    intros x y s hs hxy,
    calc P {ω : Ω | M x ω ∈ s} 
        = ∑' (i : ι), P ((λ ω : Ω, M x ω) ⁻¹' (s ∩ p ⁻¹' {i})) :
          begin 
            rw [← measure_Union, ← set.preimage_Union, ← set.inter_Union, ← set.bUnion_univ,
              set.bUnion_preimage_singleton, set.preimage_univ, set.inter_univ],
            refl,
            { rintros i j hij ω ⟨hω₁, hω₂⟩,
              have h₁ : p (M x ω) ∈ {i} := @set.mem_of_mem_inter_right _ (M x ω) s (p ⁻¹' {i}) hω₁,
              have h₂ : p (M x ω) ∈ {j} := @set.mem_of_mem_inter_right _ (M x ω) s (p ⁻¹' {j}) hω₂,
              rw set.mem_singleton_iff at *,
              rw [←h₁, ←h₂] at hij,
              contradiction },
            { measurability }
          end
    ... ≤ ∑' (i : ι), ((ε i).exp * P {ω : Ω | M y ω ∈ s ∩ {o : O | p o = i}} + δ i) :
          begin
            refine tsum_mono ennreal.summable ennreal.summable _,
            intro i,
            apply h,
            apply set.inter_subset_right,
            { measurability },
            exact hxy
          end
    ... = ∑' (i : ι), δ i + ∑' (i : ι), (ε i).exp * P {ω : Ω | M y ω ∈ s ∩ {o : O | p o = i}} :
          begin
            rw [tsum_add ennreal.summable ennreal.summable, add_comm]
          end
  end}