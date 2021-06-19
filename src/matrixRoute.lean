import ring_theory.principal_ideal_domain ring_theory.matrix_algebra
import tactic

open_locale matrix

variables {m n o p R : Type*} [fintype m] [fintype n] [fintype o] [fintype p]

/-- A matrix with added rows is still a matrix over the same type.  -/
def matrix.reindex_or_zero [has_zero R] (A : matrix m n R) (fm : m ↪ o) (fn : n ↪ p) 
  : matrix o p R := sorry

-- call this something different
/-- A smith normal form is a diagonal that doesn't have to be square and can have diagonal zeroes -/
def smith_normal [has_zero R] {r : ℕ} (a : fin r → R)
  (fm : fin r ↪ m) (fn : fin r ↪ n) : matrix m n R :=
(matrix.diagonal a).reindex_or_zero fm fn

variables [integral_domain R] [is_principal_ideal_ring R]

/-- Every matrix over a pid has a smith normal form. Lemma 3.8 -/
lemma pid_matrix_has_smith [decidable_eq n] [decidable_eq m] (A : matrix m n R) : 
  ∃ (S : units (matrix m m R)) (T : units (matrix n n R))
    {r : ℕ} (a : fin r → R) (ha : sorry) -- the dvd condition
    (fm : fin r ↪ m)
    (fn : fin r ↪ n),
      ((S : matrix m m R) ⬝ A ⬝ (T : matrix n n R)) = smith_normal a fm fn :=
begin
  sorry
end

variables (r : ℕ) (i j : fin r) (a : fin r → R)

#exit

#check i ≤ j → (a i | a j) 

