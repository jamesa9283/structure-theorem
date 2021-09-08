import ring_theory.principal_ideal_domain algebra.euclidean_domain

variables {V : Type*} [integral_domain V] [is_principal_ideal_ring V] 


lemma test (a b: V) (gcd_a a b : V) : a * (euclidean_domain.gcd_a a b) + b * (euclidean_domain.gcd_b a b) := sorry 