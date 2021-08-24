import data.matrix.notation


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

The inverse functions are `vec_butlast` and `vec_last`.
-/
def vec_snoc {n : ℕ} (t : fin n → α) (h : α) : fin n.succ → α :=
fin.snoc t h

@[simp] lemma last_snoc (x : α) (u : fin m → α) :
  vec_last (vec_snoc u x) = x :=
by apply fin.snoc_last

@[simp] lemma butlast_snoc (x : α) (u : fin m → α) :
  vec_butlast (vec_snoc u x) = u :=
by apply fin.init_snoc

end matrix