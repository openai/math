# [Superpolynomial graph diameter of simple polytopes](paper.pdf)

OpenAI · November 24, 2026 edition

For every sufficiently large facet count $n$, there is a bounded simple rational polytope with exactly $n$ facets and subpolynomial dimension whose graph diameter grows faster than every fixed power of $n$. This disproves the polynomial Hirsch conjecture. For any prescribed positive integer-valued $s(n)=n^{o(1)}$, the examples can be chosen so that two vertices remain superpolynomially far apart even if each step crosses a face of dimension at most $s(n)$.

The [companion paper on strongly polynomial linear programming](../Strongly-polynomial-linear-programming-November-24-2026/paper.pdf) gives an optimization algorithm that recovers exact certificates directly from the inequalities.

## Lean formalization

Lean proves the refutation for bounded simple rational polytopes, the distance bound for moves across low-dimensional faces, and superpolynomial separation of vertices with a prescribed objective gap. It also proves a quantitative lower bound with the dimension and facet excess prescribed independently. [Hirsch refutation](../../lean/OAI/Geometry/Hirsch/Main.lean#L107-L109) · [Theorem 1.1](../../lean/OAI/Geometry/Hirsch/Main.lean#L51-L64) · [Theorem 1.2](../../lean/OAI/Geometry/Hirsch/Main.lean#L112-L119) · [Comparator statement](../../lean/ComparatorChallenges/Hirsch.lean#L148-L150) · [Formalization scope](../../lean/docs/380.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/sections/references.tex) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:Superpolynomial-graph-diameter-of-simple-polytopes-November-24-2026,
  author = {{OpenAI}},
  title = {{Superpolynomial graph diameter of simple polytopes}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Superpolynomial-graph-diameter-of-simple-polytopes-November-24-2026/paper.pdf}{OAI:Superpolynomial-graph-diameter-of-simple-polytopes-November-24-2026}},
  year = {2026}
}
```
