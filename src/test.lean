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


lemma first_sub_all (I : set (ideal V)) (Iₙ : ℕ → (set I))
  {hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j} (n : ℕ) : Iₙ 0 ⊆ Iₙ n :=
begin
  induction n with m h₂,
  { refl},
  { -- have H : Iₙ n = Iₙ (n + 1),
    have H := hIₙ m (m + 1) (show m < m + 1, by linarith),
    tauto
  },
end

lemma second (I : set (ideal V)) {Iₙ : ℕ → (set I)} 
  {hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j} (n : ℕ) (a : I) : a ∈ Iₙ 0 → a ∈ Iₙ n := 
begin
  have H := first_sub_all I Iₙ n,
  rw set.subset_def at H,
  exact H a,
  exact hIₙ,
end

/-
begin
  induction n with m hm, 
  { intro x, exact x},
  { intro a_in_I_zero,
    specialize hm a_in_I_zero,
    have H := hIₙ m (m + 1) (show m < m + 1, by linarith),
    rw set.subset_def at H, 
    exact H a hm, 
  },
end
-/

lemma third (I : set (ideal V)) {Iₙ : ℕ → (set I)} 
  {hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j} (a : I) : a ∈ Iₙ 0 → a ∈ ⋃ n, Iₙ n :=
begin
  intros ha,
  rw set.mem_Union,
  use 0,
  exact ha,
end 

#check ⋃ n, Iₙ n
#check zorn.chain (≤) I

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