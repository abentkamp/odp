/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

namespace matrix

universe u
variables {α : Type u}
variables {m n : ℕ}

/-- `vec_last v` gives the last entry of the vector `v` -/
def vec_last {n : ℕ} (v : fin n.succ → α) : α :=
v ⟨n, n.lt_succ_self⟩

/-- `vec_butlast v` gives a vector consisting of all entries of `v` except the last -/
def vec_butlast {n : ℕ} (v : fin n.succ → α) : fin n → α :=
fin.init v

@[simp]
lemma head_butlast {n : ℕ} (v : fin n.succ.succ → α) :
  vec_head (vec_butlast v) = vec_head v := rfl

@[simp]
lemma last_tail {n : ℕ} (v : fin n.succ.succ → α) :
  vec_last (vec_tail v) = vec_last v := rfl

@[simp]
lemma butlast_tail {n : ℕ} (v : fin n.succ.succ → α) :
  vec_butlast (vec_tail v) = vec_tail (vec_butlast v) :=
begin
  ext i,
  simp [vec_butlast, vec_tail, fin.init, fin.cast_succ,
    fin.cast_add, fin.cast_le, fin.cast_lt]
end

/-- `vec_snoc t h` appends an entry `h` to a vector `t`.
The inverse functions are `vec_butlast` and `vec_last`. -/
def vec_snoc {n : ℕ} (t : fin n → α) (h : α) : fin n.succ → α :=
fin.snoc t h

@[simp] lemma last_snoc (x : α) (u : fin m → α) :
  vec_last (vec_snoc u x) = x :=
by apply fin.snoc_last

@[simp] lemma butlast_snoc (x : α) (u : fin m → α) :
  vec_butlast (vec_snoc u x) = u :=
by apply fin.init_snoc

def vec_cons.equiv {α : Type*} (n : ℕ) : α × (fin n → α) ≃ (fin n.succ → α) :=
⟨λ x, vec_cons x.1 x.2,
 λ x, (vec_head x, vec_tail x),
 begin intro x, simp end,
 begin intro x, simp end⟩

end matrix