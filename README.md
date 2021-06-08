# Formalisation of Structure Theorem for Finitely Generated Modules over a Principal Ideal Domains

This is a project for my summer research project into formalising Jordan Normal Form. This project is mentioned in [this mathlib issue](https://github.com/leanprover-community/mathlib/issues/4971) There are currently two routes that I can use to achieve structure theorem;

* Defining the Smith Form and then using the fact that a finitely generated module over a p.i.d. is Noetherian, then using representations and using a smith normal form and **wavey handey maths**

* Finding the torsion submodule for my module, then removing those elements from my module. This leaves a torsion free module, which is isomorphic to R^n and this can be embedded into my original module as a submodule such that it splits the projection map, hence lift the generators and then M = tM \oplus R^n. From there construct some other modules and then direct sum them and they are cyclic **handy handy wavey wavey**

## Current Progress

I am currently in the infrancy of the project and deciding which route to take. The current goal is to formalise Theorem 3.8 of Jacobson's Basic Algebra I, i.e. every matrix over a p.i.d. has a smith form. This is currently stated in `matrixRoute.lean`.

## End Goal

To provide mathlib with Jordan Normal Form, then the Structure Theorem for finitely generated albelian groups.