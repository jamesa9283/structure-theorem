import ring_theory.principal_ideal_domain ring_theory.matrix_algebra
import tactic

open_locale matrix

variables {m n o p R : Type*} [integral_domain R] [is_principal_ideal_ring R] [fintype m] [fintype n] [fintype o] [fintype p]

def matrix.reindex_or_zero [has_zero R] (A : matrix m n R) (fm : m ↪ o) (fn : n ↪ p) : matrix o p R := sorry

def smith_normal [has_zero R] {r : ℕ} (a : fin r → R)
  (fm : fin r ↪ m) (fn : fin r ↪ n) : matrix m n R :=
(matrix.diagonal a).reindex_or_zero fm fn

lemma smith_statement [decidable_eq n] [decidable_eq m] [comm_ring R] (A : matrix m n R) : 
  ∃ (S : units (matrix m m R)) (T : units (matrix n n R))
    {r : ℕ} (a : fin r → R) (ha : sorry) -- the dvd condition
    (fm : fin r ↪ m)
    (fn : fin r ↪ n),
      ((S : matrix m m R) ⬝ A ⬝ (T : matrix n n R)) = smith_normal a fm fn :=
begin
  
  sorry
end


