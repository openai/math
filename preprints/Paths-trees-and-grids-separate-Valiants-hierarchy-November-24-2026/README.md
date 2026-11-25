# [Paths, trees and grids separate Valiant’s hierarchy](paper.pdf)

OpenAI · November 24, 2026 edition

Over every field, $\mathsf{VP}\ne\mathsf{VNP}$. The state sum on an $n\times n$ grid belongs to $\mathsf{VNP}$ and requires arithmetic circuits of size $n^{\Omega((\log n)^{1/12})}$. The same construction on paths and binary trees separates formulas from algebraic branching programs and branching programs from circuits. Together the examples prove $\mathsf{VF}\subsetneq\mathsf{VBP}\subsetneq\mathsf{VP}\subsetneq\mathsf{VNP}$. All three lower bounds hold in degree-component border complexity.

The [companion paper on complete polynomials](../Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/paper.pdf) gives quantitative lower bounds for Hamiltonian cycle and the permanent.

## Lean formalization

The Lean development proves all three strict inclusions for the exact arithmetic classes over every field. [Hierarchy proof](../../lean/OAI/Hierarchy/Strict.lean#L9-L12) · [Formalization scope](../../lean/docs/379.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:Paths-trees-and-grids-separate-Valiants-hierarchy-November-24-2026,
  author = {{OpenAI}},
  title = {{Paths, trees and grids separate Valiant's hierarchy}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Paths-trees-and-grids-separate-Valiants-hierarchy-November-24-2026/paper.pdf}{OAI:Paths-trees-and-grids-separate-Valiants-hierarchy-November-24-2026}},
  year = {2026}
}
```
