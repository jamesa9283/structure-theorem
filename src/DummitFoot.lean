import ring_theory.principal_ideal_domain ring_theory.ideal.basic linear_algebra.basis 
import algebra.direct_sum.module

variables {R M ι : Type*} 
-- let R be a P.I.D. and M a finitely generated R module.
variables [integral_domain R] [is_principal_ideal_ring R] 
variables [add_comm_group M] [module R M] [fintype ι] (b : basis ι R M)

variables (x : M)

#check (M)


--  nonzero elements a₁, a₂, ••• , aₘ of R which are not units in R and which satisfy 
-- the divisibility relations
variables {ι₂ : Type*} [fintype ι₂] (a : ι₂ → R) (hι₂ : ∀ i : ι₂, a i ≠ (0 : R))
variables (hι₂₂ : ∀ i j : ι₂, a i ∣ a j)

-- two problems, what does `R / (aᵢ)` even mean? How do I formalise it.
-- How do direct sum?

-- #check direct_sum.module M _ 
