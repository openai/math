# Exact square and rectangular matrix multiplication exponents over every field

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Complex Matrix Multiplication Below 2.258 and Rectangular Bounds](../../preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf)
- [Staggered extraction for exact matrix multiplication over every field](../../preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf)
- [The matrix multiplication exponent is nine fourths](../../preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf)
- [Euclidean geometry in the asymptotic spectrum of tensors](../../preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf)

## Scope

Over every field $F$, the square matrix multiplication exponent is $\omega(F;1,1,1)=9/4$. The dual exponent, the supremum of $t\in[0,1]$ with $\omega(F;1,1,t)=2$, is $\alpha(F)=1/2$. The model counts additions, subtractions, and multiplications in division-free programs and requires formal polynomial identities even over finite fields.

Write the positive weights $a,b,c$ in decreasing order as $x\ge y\ge z>0$. Then

```math
\omega(F;a,b,c)=x+y+\frac{\left[\max\left(0,(x+y)z-xy\right)\right]^2}{4xyz}.
```

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Exact square exponent | [Square exponent statement](../ComparatorChallenges/MatrixExponent.lean#L106-L107) |
| Exact dual exponent | [Dual exponent definition and statement](../ComparatorChallenges/MatrixExponent.lean#L110-L118) |
| Exact rectangular exponent | [Rectangular exponent formula](../ComparatorChallenges/MatrixExponent.lean#L121-L131) |
