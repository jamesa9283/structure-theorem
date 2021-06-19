import ring_theory.principal_ideal_domain ring_theory.ideal.basic
import order.zorn

variables {V M : Type*} [integral_domain V] [is_principal_ideal_ring V] 
   [add_comm_group M] [field V] -- I added field here, it *may* break things
   [module V M]

open module
open ideal zorn

variables (I : set(ideal V)) (Iₙ : ℕ → (set I)) (hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j) (n : ℕ)

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
class is_maximal_set (S : set (ideal V)) : Prop := (out : is_coatom S)

#check ⋃ n, Iₙ n
#check zorn.chain (≤) I

lemma first (I : set (ideal V)) (hI : I.nonempty) {Iₙ : ℕ → (set I)} 
  {hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j} : Iₙ 0 ⊆ Iₙ n :=
begin
  induction n with h₁ h₂,
  { refl},
  { 
    sorry
  },
end

example : n.succ = n + 1 := rfl

lemma exists_maximal_in_set (I : set (ideal V)) (hI : I.nonempty) {Iₙ : ℕ → (set I)} 
  {hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j} : ∃ s : I, is_maximal_set I :=
begin
  let J := ⋃ n, Iₙ n,
  have h₁ : J.nonempty,
  { rw set.nonempty_def,
    
    sorry},

  sorry
end

#exit 


#check set (ideal V)
variables (S : set(ideal V)) (T : set(set(ideal V))) (a b : S)
#check a ≤ b
#check S.nonempty
#check ideal.exists_maximal V 

lemma test (hS : zorn.chain (≤) T) : ∃ ub, ∀ a ∈ T, a ≤ ub := sorry

#check zorn.exists_maximal_of_chains_bounded test _

lemma ideals_nonempty (S : set (ideal V)) : S.nonempty := -- not necessarily true
begin
  rw set.nonempty_def,
  use 0,
  -- apply ideal.zero_mem,
  sorry
end