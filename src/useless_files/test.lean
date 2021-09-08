import ring_theory.principal_ideal_domain ring_theory.ideal.basic
import order.zorn data.real.basic

variables {V M : Type*} [integral_domain V] [is_principal_ideal_ring V] 
   [add_comm_group M] -- I added field here, it *may* break things
   [module V M]

open module
open ideal zorn

variables (Iₙ : ℕ → (set (ideal V))) (hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j) (n : ℕ)

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

lemma third (Iₙ : ℕ → (set (ideal V)))
  (hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j) (a : ideal V) : a ∈ Iₙ 0 → a ∈ ⋃ n, Iₙ n :=
begin
  intros ha,
  rw set.mem_Union,
  use 0,
  exact ha,
end 

#check ⋃ n, Iₙ n
variables (J : set (⋃ n, Iₙ n)) (x : ideal V) (hx : x ∈ Iₙ 0) 
#check zorn.chain (≤) (Iₙ 0)
#check nonempty J
#check J.nonempty

#check third Iₙ hIₙ x hx
open set

lemma big_union_nonempty {Iₙ : ℕ → set(ideal V)} (hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j) : 
  (Iₙ 0).nonempty → (⋃ n, Iₙ n).nonempty :=
begin
  intros hIₙ, 
  rw set.nonempty_def at hIₙ,
  cases hIₙ with x hx,
  rw set.nonempty_def,
  use x,
  exact third Iₙ hIₙ x hx,
end

example (I : set (ideal V)) : zorn.chain (≤) I :=
begin
  rw [zorn.chain, pairwise_on],
  intros i hi j hj hij,
  by_cases (i < j),
  { rw le_iff_lt_or_eq,
    left, left,
    exact h,
  },
  { right,
    rw le_iff_lt_or_eq,
    left,
    -- rw lt_or_eq_of_le,
    -- rw not_lt at h, -- why are you like this.
    sorry},
end




-- ∃ (m : ?m_1) (H : m ∈ ?m_2), ∀ (z : ?m_1), z ∈ ?m_2 → m ≤ z → z = m
lemma exists_maximal_in_set (I : set (ideal V)) (H : zorn.chain (≤) I) (hI : I.nonempty)
  {Iₙ : ℕ → set(ideal V)} {hIₙ : ∀ i j, i < j → Iₙ i ⊆ Iₙ j}
  : ∃ s ∈ I, ∀ t ∈ I, s ≤ t → t = s:=
begin
  apply zorn.zorn_partial_order₀,
  intros X hXI XChain,
  -- use (⨆ n, Iₙ n),
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