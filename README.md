# Semantics
Tucker and Zucker [2001] gave an algebraic "operational semantics" for WhileCC-programs. Here we work with "denotational semantics" for WhileCC-programs.
In order to represent the denotational semantics, we need to
  - define a ($\omega$-complete partial order) with bottom $\bot$.
  - show the semantic operators are $\omega$-Scott continuous
    + Monotonicity
    + Scott-continuity
Then knowing that F is Scott-continuous on a $\omega$-complete partial order with $\bot$, then:  
  lfp(F) = ⊔ {Fⁿ($\bot$) | n $\in$ ℕ}  
exists, and is the least fixed point of F.
This gives us the denotation of our recursive function.  

# References
[1] J. V. Tucker and J. I. Zucker. Computable functions and semicomputable sets on many-sorted algebras. Handbook of logic in computer science, 5:317–523, 2001. 3, 4, 5, 11
