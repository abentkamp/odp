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

def fin.to_list {α : Type*} : Π {n : ℕ} (a : fin n → α), list α
| 0 a := []
| (n + 1) a := vec_head a :: fin.to_list (vec_tail a)

lemma fin.to_list_nil {α : Type*} : 
  fin.to_list ![] = ([] : list α) := rfl

lemma fin.to_list_cons {α : Type*} {n : ℕ} (a : α) (as : fin n → α) : 
  fin.to_list (vec_cons a as) = a :: fin.to_list as :=
by induction n; simp [fin.to_list]

def list.to_fin {α : Type*} : Π (l : list α), fin (l.length) → α
| [] := ![]
| (x :: xs) := vec_cons x (xs.to_fin)

lemma list.vec_cons_to_fin {α : Type*} (a : α) (l : list α) :
  vec_cons a l.to_fin = (a :: l).to_fin := rfl

@[simp]
lemma fin.length_to_list {α : Type*} : ∀ {n : ℕ} (a : fin n → α),
  (fin.to_list a).length = n
| 0 a := rfl
| (n + 1) a := by simp [fin.to_list, fin.length_to_list]

lemma cast_vec_cons {α : Type*} {m n : ℕ} (h : m = n) (a : α) (as : fin m → α) :
cast (by rw h) (vec_cons a as) = vec_cons a (cast (by rw h) as) :=
begin
  subst h,
  refl,
end

end

