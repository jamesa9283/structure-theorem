import linear_algebra.free_module linear_algebra.std_basis data.real.basic

-- we need that a free finitely generated module is isomorphic to ℝⁿ.

variables {R M : Type*} [integral_domain R] [is_principal_ideal_ring R] [add_comm_group M] [module R M]

open module

/- I want to get an isomorphism from a free module to ℝⁿ
   so find a basis for M\tM and then prove that it's card is n 
-/

variables [module.finite R M] [no_zero_smul_divisors R M]
/- This defines that our module is finitely generated and torsion free, hence like a 
   'vector space'.
-/

variables {ι : Type*} (v : ι → R)
/- I need to create an orderng, this is done by inputting an element of type ι and then 
   getting out the element of type R (our 'vector space')
-/

variable (b : basis ι R M)
#check (ι →₀ R)
#check ι →₀ ℝ
#check M ≃ₗ[R] (ι →₀ R)

example : M ≃ₗ[R] (ι →₀ R) := sorry

#exit

#check basis.equiv_fun _ _ _

#check [finite R M]
#check basis _ R M

#check free_of_finite_type_torsion_free' 