# [The logarithmic exponent of finite Fourier transforms](paper.pdf)

OpenAI · November 24, 2026 edition

For a finite abelian group of order $N$, the minimum number of binary linear gates for its Fourier transform is $N(\log N)^{1/2+o(1)}$. The field must contain a primitive root of unity of order the group exponent, and $N$ must be invertible. The bounds hold for both forward and inverse transforms and scale by $J$ for $J$ independent inputs, even when gates combine values from different transforms. The paper also proves the same logarithmic exponent for formal polynomial multiplication over every field.

## Lean formalization

The Lean development includes the upper and lower bounds for individual Fourier transforms and for batches of transforms. [Single-transform proof](../../lean/OAI/LinearAlgebra/FiniteFourier/Main.lean#L17) · [Batched-transform proof](../../lean/OAI/LinearAlgebra/FiniteFourier/BatchedTheorem.lean#L93) · [Formalization scope](../../lean/docs/130.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026,
  author = {{OpenAI}},
  title = {{The logarithmic exponent of finite Fourier transforms}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026/paper.pdf}{OAI:The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026}},
  year = {2026}
}
```
