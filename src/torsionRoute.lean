import linear_algebra.free_module linear_algebra.std_basis data.real.basic

-- we need that a free finitely generated module is isomorphic to ℝⁿ.

variables {R M : Type*} [integral_domain R] [is_principal_ideal_ring R] 
   [add_comm_group M] [field R] -- I added field here, it *may* break things
   [module R M]

open module

/- I want to get an isomorphism from a free module to ℝⁿ
   so find a basis for M\tM and then prove that it's card is n 
-/



variables [module.finite R M] [no_zero_smul_divisors R M]
/- This defines that our module is finitely generated and torsion free, hence like a 
   'vector space'.
-/

variables {ι : Type*} [fintype ι] (v : ι → R)
/- I need to create an orderng, this is done by inputting an element of type ι and then 
   getting out the element of type R (our 'vector space')
-/

variable (n : ℕ)
#check fin n → R -- this means Rⁿ

variables (b : basis ι R M) (i : ι)
#check b
#check M ≃ₗ[R] (ι →₀ R)

open module

#check finite_dimensional.finrank R M

-- I'm missing something along the lines of, if a module is finitely generated
-- and free, then it has a finite basis

-- The way to create a free module is to just define a basis over the module

/- Now it's time to state that M is isomorphic to Rⁿ -/
noncomputable def M_iso_Rn (b : basis ι R M) (i : ι) (hn : n = finite_dimensional.finrank R M) -- n must be the size of b
  : M ≃ₗ[R] (fin n → R) := { 
  to_fun := _, 
  inv_fun := λ x, b i, -- use the basis to prove this
  map_smul' := _,
  map_add' := _,
  left_inv := _,
  right_inv := _, }


#exit

#check basis.equiv_fun _ _ _

#check [finite R M]
#check basis _ R M

#check free_of_finite_type_torsion_free' 