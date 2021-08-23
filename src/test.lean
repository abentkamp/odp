import .missing .missing_measure
open measure_theory ennreal
open_locale ennreal


variables {Ω : Type} (P : list Ω) (O : Type)

variables (X : Type) 

structure odp_partition  {O : Type} (M : list O) :=
(dp : M = M)


structure adversary_choice :=
(M : list O)
(odp_partition : odp_partition M)

constant ch (O : Type) : adversary_choice O
constant ch' (O : Type) : adversary_choice O

structure adversary :=
(choose :  adversary_choice O)

constant iv : adversary O → adversary O

lemma my_lemma : ch O = ch' O := sorry

example {α : Type} (𝒜 : adversary O) (m : ℕ)
: 
 (λ (a : α), adversary_choice.odp_partition (ch O ))
=  (λ (a : α), adversary_choice.odp_partition  (ch O ))
:=
begin
simp_rw [my_lemma],
end