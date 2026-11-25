# History

For any withdrawn papers, their README files explain the gap and link to the retracted manuscript. For any updated papers, previously published editions remain accessible through the version notes in their README.

## November 24, 2026

**New Results Added**

We have added nine manuscripts across two result families, with Lean formalizations of selected results from each manuscript.

*Euclidean tensor geometry and its applications to complexity and combinatorics* ([family 379](CONTENTS.md#family-379)). Seven manuscripts develop a geometric theory of tensors and apply it to arithmetic complexity and combinatorics.

- *Euclidean geometry in the asymptotic spectrum of tensors*
- *Paths, trees and grids separate Valiant’s hierarchy*
- *Circuit lower bounds for Hamiltonian cycle and the permanent*
- *The logarithmic exponent of finite Fourier transforms*
- *The logarithmic exponent of integer multiplication on tapes*
- *The matrix multiplication exponent is nine fourths*
- *An exponential bound for sunflowers*

The hierarchy and circuit lower bound papers subsume the results of *VP and VNP are different*, released November 23. The original manuscript remains available unchanged.

*Strongly polynomial-time linear programming* ([family 380](CONTENTS.md#family-380)). Two manuscripts address the complexity of solving a linear program and the length of paths along the edges of a polytope.

- *Strongly polynomial linear programming* gives a deterministic strongly polynomial algorithm for linear programming, answering Smale’s ninth problem.
- *Superpolynomial graph diameter of simple polytopes* disproves the polynomial Hirsch conjecture for bounded simple rational polytopes.

## November 23, 2026

**New Results Added**

- *VP and VNP are different*. This result was obtained on November 6, 2026.

## October 29, 2026

**Formalization Fix**

- *The rational Hodge conjecture for CM abelian varieties.* Diverging namespaces in the Comparator challenge and solution were adjusted.

## October 26, 2026

**New Results Added**

We have added two new manuscripts with accompanying Lean formalizations:

- *Local smoothing for the Euclidean wave equation.* The proof uses an auxiliary partial differential equation to establish Sogge's local smoothing for waves in every spatial dimension at least two. It also yields the Kakeya maximal and dimension conjectures and Stein’s spherical restriction estimates throughout the interior of the conjectured range. We are releasing the model output directly, as we did in our October 6 release.
- *The Exponential Time Hypothesis is False.* The paper gives a deterministic algorithm that exactly counts satisfying assignments of fixed-width CNF formulas in subexponential time and polynomial space. The case of 3-SAT refutes the Exponential Time Hypothesis. An independent working group of computer scientists led by Russell Impagliazzo, Ramamohan Paturi, and Ryan Williams will examine and explain the proof. At the group’s request, we are making the materials public immediately so others can examine them as well.

**Formalization Additions and Improvements**

- *The rational Hodge conjecture for CM abelian varieties.* A Lean formalization was added.
- Some Comparator configurations were fixed, and some Lean formalizations were improved. 

**Auxiliary Files Included**

- *The maximum number of mutually unbiased bases in dimension six.* We restored the C++ source and saved numerical records for the computation that excludes a fourth mutually unbiased basis. A Python checker verifies the consistency and coverage of the saved records.


## October 7, 2026

**Withdrawals**

In “Algebraicity of Weil classes on split abelian eightfolds” a sign error invalidates a stabilization-trace cancellation argument and the construction used by two dependent papers. As a result, we have withdrawn the following three manuscripts:

- Algebraicity of Weil classes on split abelian eightfolds
- Algebraicity of Kuga–Satake Correspondences for K3 Surfaces
- The rational Hodge conjecture for products of K3 surfaces

The withdrawn papers now carry notices explaining the gap and linking to the archived manuscripts.

**Fixes**

We have revised 14 other manuscripts with proof repairs, corrected statements, clearer hypotheses and dependencies, and one correction to an obsolete citation. The changes include:

- Lipschitz heights and Ashkin–Teller currents (4 manuscripts): repaired crossing, boundary-attachment, conditioning and convergence arguments, including additional work on the real-Lipschitz interface proof.
- Kähler minimal model programs and abundance (6 manuscripts): expanded positivity and contraction arguments and clarified which results are used as inputs, with their required hypotheses.
- Taming and hypersymplectic deformation (2 manuscripts): corrected the cone-equality claim in Taming implies compatibility, added a strict-inclusion example, and removed an unnecessary cone-comparison dependency from the hypersymplectic paper.
- Incompressible Box Transport and Finite Computation: revised the torus-projection and common-clock estimates.
- Exact Birch–Swinnerton-Dyer Formula from Low Selmer Corank: removed an obsolete introductory citation to a removed supporting manuscript.

Also, as a consequence of these fixes we updated 13 additional manuscripts to cite the revised editions of companion papers. These changes update references and version dates.

**Additional Formalizations**

We have added an additional 6 formalizations and 5 other additions covering supporting results. This brings the total percentage of top-line results formalized to 300 / 719 = ~42%.
