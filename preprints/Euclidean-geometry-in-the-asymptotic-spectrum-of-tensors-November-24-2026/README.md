# [Euclidean geometry in the asymptotic spectrum of tensors](paper.pdf)

OpenAI · November 24, 2026 edition

Over every field, Theorem 1.1 assigns costs to tensors whose indices are placed in a real Hilbert space. A bit shared between two sites costs their Euclidean distance. For any finite set of sites, the cost of sharing one bit among them is the mean width of their convex hull, normalized to give a segment its length. For three sites this is half the perimeter of their triangle.

This geometry lets the companion papers compare a tensor with the networks that produce it. Two applications are the [matrix multiplication lower bound](../The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf) and the [fixed-petal sunflower bound](../An-exponential-bound-for-sunflowers-November-24-2026/paper.pdf).

## Lean formalization

On a convex Euclidean chart with jointly convex diagonal prices, the formal development identifies the price of a shared bit with the normalized mean width. The catalogue also describes the matrix multiplication application. [Mean-width proof](../../lean/OAI/LinearAlgebra/SpectralBooks/SpectralFlatLaw.lean#L98-L104) · [Matrix multiplication scope](../../lean/docs/107.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026,
  author = {{OpenAI}},
  title = {{Euclidean geometry in the asymptotic spectrum of tensors}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf}{OAI:Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026}},
  year = {2026}
}
```
