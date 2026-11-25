# [The logarithmic exponent of integer multiplication on tapes](paper.pdf)

OpenAI · November 24, 2026 edition

One deterministic multitape Turing machine computes the full product of two $n$-bit integers in $n(1+\log n)^{1/2+o(1)}$ worst-case time and visits $O(n)$ tape cells. Under variable-count Weak ETH for 3-SAT, every exact deterministic multiplier needs $\Omega(n\sqrt{\log n})$ steps on some input at each sufficiently large length. Under that hypothesis, the infimum of achievable logarithmic exponents is $1/2$. The paper also obtains matching exponents for exact division and integer square root.

The upper bound uses short transforms from the [companion paper on finite Fourier transforms](../The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026/paper.pdf).

## Lean formalization

The Lean development proves the uniform multiplication algorithm and the lower bound under Weak ETH, including the resulting optimal exponent. [Upper bound](../../lean/OAI/Computability/NearSquareRoot/Main.lean#L45) · [Conditional lower bound](../../lean/OAI/Computability/MultitapeWeakETH/Main.lean#L31) · [Exponent under Weak ETH](../../lean/OAI/Computability/MultitapeWeakETH/NearRoot.lean#L11) · [Formalization scope](../../lean/docs/109.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026,
  author = {{OpenAI}},
  title = {{The logarithmic exponent of integer multiplication on tapes}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026/paper.pdf}{OAI:The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026}},
  year = {2026}
}
```
