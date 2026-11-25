# [An exponential bound for sunflowers](paper.pdf)

OpenAI · November 24, 2026 edition

Theorem 1.1 proves the fixed-petal sunflower conjecture. For every $r\ge3$, more than $B_r^k$ distinct sets of size at most $k$ force $r$ sets whose pairwise intersections are all the same. The bound is independent of the ground set, and $\log B_r=O((\log r)^4(\log\log(2r))^{5/2})$.

The proof uses the [geometry of the asymptotic spectrum](../Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf) to bound the size of a sunflower-free family of words uniformly over its alphabet.

## Lean formalization

The Lean development proves that for each $r\ge3$ there exists a constant $C_r$ giving the bound $C_r^k$ for finite families of $k$-element sets. The manuscript gives the quantitative dependence of the base on $r$. [Fixed-petal theorem in Lean](../../lean/OAI/Combinatorics/Sunflower/FixedBase.lean#L41-L48) · [Formalization scope](../../lean/docs/379.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX and BibTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:An-exponential-bound-for-sunflowers-November-24-2026,
  author = {{OpenAI}},
  title = {{An exponential bound for sunflowers}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/An-exponential-bound-for-sunflowers-November-24-2026/paper.pdf}{OAI:An-exponential-bound-for-sunflowers-November-24-2026}},
  year = {2026}
}
```
