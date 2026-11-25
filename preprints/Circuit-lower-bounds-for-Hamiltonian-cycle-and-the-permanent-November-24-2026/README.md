# [Circuit lower bounds for Hamiltonian cycle and the permanent](paper.pdf)

OpenAI · November 24, 2026 edition

Arithmetic circuits computing the directed Hamiltonian cycle polynomial of order $N$ over any field require at least $\exp\!\big(c(\log N)^2/(\log\log N)^2\big)$ gates at every sufficiently large $N$. The constant $c>0$ is absolute, and the threshold depends only on the characteristic. The same bound holds for the permanent in every characteristic other than two. Theorem 1.1 allows circuits to approximate the coefficients of the degree-$N$ component.

The [companion paper on Valiant’s hierarchy](../Paths-trees-and-grids-separate-Valiants-hierarchy-November-24-2026/paper.pdf) gives an explicit grid witness for $\mathsf{VP}\ne\mathsf{VNP}$.

## Lean formalization

The Lean development proves eventual superpolynomial exact circuit lower bounds for the directed Hamiltonian cycle polynomial over every field and the permanent outside characteristic two. [Proof for the two polynomials](../../lean/OAI/Computability/VPVNP/Separation.lean#L31-L38) · [Formalization scope](../../lean/docs/379.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026,
  author = {{OpenAI}},
  title = {{Circuit lower bounds for Hamiltonian cycle and the permanent}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/paper.pdf}{OAI:Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026}},
  year = {2026}
}
```
