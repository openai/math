# [The matrix multiplication exponent is nine fourths](paper.pdf)

OpenAI · November 24, 2026 edition

The exponent of square matrix multiplication is $9/4$ over every field. The paper proves the matching lower bound for formal arithmetic circuits. At every side length $n\ge2$, at least $\lceil n^{9/4}/2\rceil$ nonscalar multiplication or division gates are required. The geometric border rank of the square multiplication tensor is at least $n^{9/4}$ and its asymptotic rank over the base field equals $n^{9/4}$.

The [companion paper on tensor geometry](../Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf) supplies the geometric framework for the lower bound.

## Lean formalization

The Lean development proves the square exponent $9/4$ for division-free circuits computing formal polynomial identities over every field. The scope document also states the formalized dual and rectangular exponents. [Square-exponent proof](../../lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L11-L12) · [Formalization scope](../../lean/docs/107.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026,
  author = {{OpenAI}},
  title = {{The matrix multiplication exponent is nine fourths}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf}{OAI:The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026}},
  year = {2026}
}
```
