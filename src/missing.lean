import data.set.basic
import data.matrix.notation

instance is_empty_fin_zero : is_empty (fin 0) :=
is_empty.mk (λ x, nat.not_lt_zero x.1 x.2)

instance subsingleton_fun_is_empty (α β : Type*) [is_empty α] : 
  subsingleton (α → β) :=
begin
  apply subsingleton.intro,
  intros a b,
  ext x,
  apply is_empty.elim _ x,
  apply_instance,
end

lemma set.eq_empty_of_subsingleton_of_not_univ {α : Type*} [subsingleton α]
  (s : set α) (hs : s ≠ set.univ) : s = ∅ :=
begin
  apply set.eq_empty_of_subset_empty,
  intros a ha,
  apply hs,
  apply set.eq_univ_iff_forall.2,
  intro b,
  rw subsingleton.elim b a,
  apply ha
end

section
open matrix

lemma matrix.injective_head_tail {α : Type} (n : ℕ) : 
  function.injective (λ (x : fin n.succ → α), (vec_head x, vec_tail x)) :=
λ x y hxy, by rw [←cons_head_tail x, ←cons_head_tail y, (prod.mk.inj hxy).1, (prod.mk.inj hxy).2]

end