import linear_algebra.free_module linear_algebra.std_basis data.real.basic
import ring_theory.principal_ideal_domain

localized "notation `vector_space` := module" in vectorSpace
open_locale vectorSpace

-- we need that a free finitely generated module is isomorphic to ℝⁿ.

variables {V M : Type*} [integral_domain V] [is_principal_ideal_ring V] 
   [add_comm_group M] [field V] -- I added field here, it *may* break things
   [module V M]

open module

/- I want to get an isomorphism from a free module to ℝⁿ
   so find a basis for M\tM and then prove that it's card is n 
-/

variables [module.finite V M] [no_zero_smul_divisors V M]
/- This defines that our module is finitely generated and torsion free, hence like a 
   'vector space'.
-/

variables {ι : Type*} [fintype ι] (v : ι → V)
/- I need to create an orderng, this is done by inputting an element of type ι and then 
   getting out the element of type V (our 'vector space')
-/

variable (n : ℕ)
#check fin n → V -- this means Vⁿ

variables (b : basis ι V M) (i : ι)
#check b
#check M ≃ₗ[V] (ι →₀ V)

open module

-- #check finite_dimensional.finrank V M

-- I'm missing something along the lines of, if a module is finitely generated
-- and free, then it has a finite basis

-- The way to create a free module is to just define a basis over the module

/-
How are product modules written in Lean?
-/

/-

/- Now it's time to state that M is isomorphic to Vⁿ -/
noncomputable def M_iso_Vn (b : basis ι V M) (i : ι) 
  (hn : n = finrank V M) : V ≃ₗ[V] (fin n → V) := { 
  to_fun := _,  -- M → Vⁿ
  /- the `to_fun` should be this, letting M = ⟨x₁, ..., xₙ⟩
     (a₁, ..., aₙ) ↦ a₁x₁ + ... + aₙxₙ
     no, this is already what I have in `inv_fun`, bugger

     So maybe this is the following,
     (0, ..., 1, ..., 0) ↦ 
  -/
  inv_fun := _, -- use the basis to prove this
  map_smul' := _,
  map_add' := _,
  left_inv := _,
  right_inv := _, }
 -- this isn't needed


-/

-- M → fin n → V



#exit

variables (f : fin n → M) (g : fin n →₀ V) (h₁ : V → fin n) (h₂ : M → fin n) (h₃ : ι → V )
#check (finsupp.total (fin n) M V f) -- (fin n →₀ V) →ₗ[V] M
#check (finsupp.lmap_domain V V g) -- (fin n →₀ V) →ₗ[V] V →₀ V
#check (finsupp.total (fin n) M V f).comp $ (finsupp.lmap_domain V V h₁) -- (V →₀ V) →ₗ[V] M


/- Bhavik's comment

hint: you'll want some restrictions on `n` or to change n to be the size of `b` 
   -> `n` is now the size of `b`, i.e. the dimension of `V`
also look at the basis api there might be helpful things there 
iirc there's constructions which look very much like this

-/