import linear_algebra.free_module

-- we need that a free finitely generated module is isomorphic to ℝⁿ.

variables {R M : Type*} [integral_domain R] [is_principal_ideal_ring R] [add_comm_group M] [module R M]

open module

#check [finite R M]
#check basis _ R M

#check free_of_finite_type_torsion_free' 