# Automated-theorem-prover

A first order theorem prover written in prolog.

Usage:

test(prop, depth).

will return whether it is possible to prove prop using at most n=depth gamma rules. Gamma rules are substitutions of variables into a proposition starting with for-all.
