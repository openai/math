# Euclidean tensor geometry and its applications to complexity and combinatorics

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Euclidean geometry in the asymptotic spectrum of tensors](../../preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf)
- [Paths, trees and grids separate Valiant’s hierarchy](../../preprints/Paths-trees-and-grids-separate-Valiants-hierarchy-November-24-2026/paper.pdf)
- [Circuit lower bounds for Hamiltonian cycle and the permanent](../../preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/paper.pdf)
- [The logarithmic exponent of finite Fourier transforms](../../preprints/The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026/paper.pdf)
- [The logarithmic exponent of integer multiplication on tapes](../../preprints/The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026/paper.pdf)
- [The matrix multiplication exponent is nine fourths](../../preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf)
- [An exponential bound for sunflowers](../../preprints/An-exponential-bound-for-sunflowers-November-24-2026/paper.pdf)

## Scope

### Euclidean tensor geometry

Over every field, Lean constructs prices for tensors whose indices lie at sites in Euclidean space of any finite dimension. A bit shared by two sites costs their distance. On a finite-dimensional convex Euclidean chart in a CAT(0) space with jointly convex diagonal prices, Lean proves that a bit shared among a nonempty finite set of sites costs the normalized mean width of their convex hull. For three sites this is half the perimeter of their triangle. The paper’s extension to infinite-dimensional real Hilbert spaces remains unformalized.

### Valiant’s arithmetic hierarchy

Over every field $F$,

$$
\mathrm{VF}(F)\subsetneq\mathrm{VBP}(F)\subsetneq\mathrm{VP}(F)\subsetneq\mathrm{VNP}(F).
$$

In all four classes, the number of variables and the total degree are polynomially bounded in the family index. VF, VBP, and VP use polynomial-size arithmetic formulas, branching programs with affine-linear edge labels, and exact circuits, respectively. VNP sums VP verifiers over Boolean witnesses.

Lean proves the three separations using state sums on paths, complete binary trees, and square grids, respectively. For the square-grid family, Lean rules out polynomial-size degree-component border circuits. The paper’s explicit $n^{\Omega((\log n)^{1/12})}$ lower bound for the $n\times n$ grid remains unformalized. The hierarchy Comparator states the three strict inclusions for the exact classes.

The $n$th polynomial of an explicit VNP-complete family is homogeneous of degree $n$ and multilinear in $2n$ variables. Its exact circuit size exceeds $n^C$ for every fixed $C\ge1$ and all sufficiently large $n$, uniformly in each characteristic. Gates are binary additions, subtractions, and multiplications.

### Hamiltonian cycle and the permanent

Lean proves that for every exponent $C$ and characteristic $q$, there is a common threshold beyond which directed Hamiltonian cycle requires more than $N^C$ exact arithmetic gates over every field of characteristic $q$. The threshold also applies to the permanent when $q\ne 2$.

The paper’s stronger $\exp(c(\log N)^2/(\log\log N)^2)$ lower bound for circuits approximating only the degree-$N$ coefficients of these polynomials remains unformalized. In that bound $c>0$ is absolute and the threshold depends only on the characteristic.

For the signed path-count polynomial $P_n^\star$, a border-circuit lower bound gives at least $2^{c(\log_2 n)^{5/4}}$ gates for exact circuits, with absolute $c>0$ and a threshold for $n$ depending only on the characteristic.

### Finite Fourier transforms

For a finite abelian group of order $n\ge2$, the forward and normalized inverse Fourier transforms each require $\Omega(n\sqrt{\log n})$ binary linear gates and admit circuits of size $O_\varepsilon(n(\log n)^{1/2+\varepsilon})$ for every $\varepsilon>0$. Each gate forms a weighted sum of two wires. The field must contain a primitive root of unity of order equal to the group exponent, and $n$ must be invertible. This includes the complex discrete Fourier transform (DFT) at every $n\ge2$.

For $J\ge1$ transforms of the same order over a common admissible field, both bounds scale by $J$, even with different groups, mixed directions, and gates shared across transforms. The lower bound also holds for feedback states under Zariski limits with simultaneous low-rank and sparse errors across the batch.

For formal polynomial multiplication, Lean proves an $O_\varepsilon(n(1+\log n)^{1/2+\varepsilon})$ upper bound using integer-coefficient circuits that specialize to every field. The paper’s $\Omega(Jn\sqrt{\log n})$ lower bound for $J\ge1$ independent products remains unformalized, even for a single product.

### Integer multiplication on tapes

One fixed deterministic multitape Turing machine writes the full $2n$-bit product of two $n$-bit integers for every $n\ge1$. Its worst-case time is at most $n(\log n)^{1/2+o(1)}$, and it visits $O(n)$ tape cells.

Under Weak ETH, even the low $n$ product bits require $\Omega(n\sqrt{\log_2 n})$ worst-case time. Thus $1/2$ is the infimum of exponents $r$ permitting exact deterministic multiplication in $O(n(\log n)^r)$ time. The theorem leaves attainment at $r=1/2$ open. Weak ETH rules out deterministic 3-SAT in time $2^{O(v^{1-\eta})}L^{O(1)}$ for fixed $0<\eta<1$, with $v$ variables and input length $L$.

The same lower bound applies to a randomized machine's deadline if its success probability is at least $2^{-n/100}$ over uniform inputs and private randomness. Success means halting and accepting by the deadline with at most $n/100$ wrong low bits. For nondeterministic machines, it suffices that this fraction of inputs admit a timely accepting run and every accepting output is exact.

The paper’s corresponding upper and conditional lower bounds for exact integer division and integer square root remain unformalized.

### Matrix multiplication

Over every field $F$, the square matrix multiplication exponent is $\omega_{\mathrm{MM}}=\omega(F;1,1,1)=9/4$. The dual exponent, the supremum of $t\in[0,1]$ with $\omega(F;1,1,t)=2$, is $\alpha(F)=1/2$. The model counts additions, subtractions, and multiplications in division-free programs and requires formal polynomial identities even over finite fields.

Write the positive weights $a,b,c$ in decreasing order as $x\ge y\ge z>0$. Then

```math
\omega(F;a,b,c)=x+y+\frac{\left[\max\left(0,(x+y)z-xy\right)\right]^2}{4xyz}.
```

Lean also proves that allowing division preserves the square exponent. In any circuit for matrix multiplication, the total number of multiplication and division gates is at least half the tensor rank over the algebraic closure of $F$. The paper’s lower bound of $\lceil n^{9/4}/2\rceil$ on the number of nonscalar multiplication or division gates at each side length $n\ge2$ remains unformalized.

### Sunflowers

For each integer $r\ge3$ there is an integer $C_r\ge1$ such that any finite family of more than $C_r^k$ distinct $k$-element sets contains an $r$-petal sunflower, meaning $r$ sets with identical pairwise intersections.

For sets of size at most $k$, the paper’s threshold $B_r^k$ with $\log B_r=O((\log r)^4(\log\log(2r))^{5/2})$ remains unformalized.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Strict inclusions among VF, VBP, VP, and VNP over every field | [Arithmetic hierarchy statement](../ComparatorChallenges/ArithmeticHierarchy.lean#L209-L211) |
| Separation of exact VP and VNP over every field | [VP versus VNP statement](../ComparatorChallenges/VPVNP.lean#L51-L54) |
| Forward and inverse transforms, upper and lower circuit bounds | [Single-transform statement](../ComparatorChallenges/ExactFourier.lean#L232-L245) |
| Batched transforms, upper and lower circuit bounds | [Batched statement](../ComparatorChallenges/ExactFourier.lean#L294-L310) |
| Subsequential savings for exact complex DFT circuits | [Scalar-gate circuit statement](../ComparatorChallenges/ExactFourier.lean#L51-L57) |
| Uniform exact DFT and convolution with a power saving | [DFT and convolution statements](../ComparatorChallenges/UniformFourier.lean#L317-L330) |
| Earlier deterministic integer multiplication upper bound | [Fixed-tape integer multiplication below the logarithmic overhead](../ComparatorChallenges/NearSquareRootMultiplication.lean#L130-L151) |
| Uniform integer multiplication upper bound with logarithmic exponent $1/2+o(1)$ | [Worst-case time and linear space](../ComparatorChallenges/NearSquareRootMultiplication.lean#L105-L123) |
| Multitape lower bound under Weak ETH | [Lower bound for computing the low product bits](../ComparatorChallenges/MultitapeWeakETH.lean#L371-L382) |
| Optimal logarithmic exponent under Weak ETH | [Infimum of achievable exponents for exact multiplication](../ComparatorChallenges/MultitapeWeakETH.lean#L387-L401) |
| Exact square matrix multiplication exponent | [Square exponent statement](../ComparatorChallenges/MatrixExponent.lean#L106-L107) |
| Exact dual matrix multiplication exponent | [Dual exponent definition and statement](../ComparatorChallenges/MatrixExponent.lean#L110-L118) |
| Exact rectangular matrix multiplication exponent | [Rectangular exponent formula](../ComparatorChallenges/MatrixExponent.lean#L121-L131) |
| Fixed-base bound for an $r$-petal sunflower | [Erdős–Rado sunflower statement](../ComparatorChallenges/Sunflower.lean#L13-L17) |
