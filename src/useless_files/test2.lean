import ring_theory.principal_ideal_domain ring_theory.ideal.basic
import order.zorn data.real.basic

variables {V M : Type*} [integral_domain V] [is_principal_ideal_ring V] 
   [add_comm_group M] -- I added field here, it *may* break things
   [module V M]

open module
open ideal zorn

lemma zero_in (I : set(ideal V)) (hI : I.nonempty) 
  : (0 : V) ∈ (⋃ i ∈ I, (i : set V)) :=
begin
  rw set.mem_bUnion_iff,
  cases hI with a ha,
  use a,
  exact ⟨ ha, a.zero_mem ⟩,
end

lemma add_mem' 
  {I : set (ideal V)}
  (hchain : chain (≤) I) :
  ∀ {a b : V},
    (a ∈ (⋃ i ∈ I, (i : set V))) →
    (b ∈ (⋃ i ∈ I, (i : set V))) →
    (a + b ∈ (⋃ i ∈ I, (i : set V))) :=
begin
  intros a b ha hb,
  rw set.mem_bUnion_iff at ha hb ⊢,
  rcases ha with ⟨J₁, hJ₁, gJ₁⟩,
  rcases hb with ⟨J₂, hJ₂, gJ₂⟩,
  rw chain at hchain,
  specialize hchain J₁ hJ₁ J₂ hJ₂,
  by_cases HJ₁J₂ : J₁ = J₂, 
  {exact ⟨ J₂, hJ₂, J₂.add_mem (HJ₁J₂ ▸ gJ₁) gJ₂ ⟩,},
  { specialize hchain HJ₁J₂,
    cases hchain with HJ₁J₂ HJ₂J₁,
    { exact ⟨ J₂, hJ₂, J₂.add_mem (HJ₁J₂ gJ₁) (gJ₂) ⟩,},
    { exact ⟨ J₁, hJ₁, J₁.add_mem (gJ₁) (HJ₂J₁ gJ₂) ⟩,},
  }
end

lemma smul_mem'
  {I : set (ideal V)} :
  ∀ (c : V) {x : V},
    (x ∈ (⋃ i ∈ I, (i : set V))) →
    (c • x ∈ (⋃ i ∈ I, (i : set V))) :=
begin
  intros a b hb,
  rw set.mem_bUnion_iff at hb ⊢,
  rcases hb with ⟨X, hXI, hbX⟩,
  exact ⟨X, hXI, X.smul_mem a hbX⟩,
end

def Union_ideal {I : set(ideal V)} (hI : I.nonempty) (hchain : chain (≤) I) : ideal V := { 
  carrier := (⋃ i ∈ I, (i : set V)),
  zero_mem' := zero_in _ hI,
  add_mem' := λ a b, add_mem' hchain,
  smul_mem' := smul_mem' }


lemma Union_in_Ideal {I : set(ideal V)} (hI : I.nonempty) (hchain : chain (≤) I) :
  Union_ideal hI hchain ∈ I :=
begin
  
  sorry
end
  
variables (I : set(ideal V)) (hI : I.nonempty)
#check set_has_maximal_iff_noetherian 

lemma exists_maximal_in_set (I : set (ideal V)) (H : zorn.chain (≤) I) (hI : I.nonempty)
  : ∃ s ∈ I, ∀ t ∈ I, s ≤ t → t = s:=
begin
  -- apply principal_ideal_ring.is_noetherian_ring,
  have H := set_has_maximal_iff_noetherian,
  apply zorn.zorn_partial_order₀,
  intros X hXI XChain,
  -- use 
  sorry
end

