# [Strongly polynomial linear programming](paper.pdf)

OpenAI · November 24, 2026 edition

A deterministic algorithm solves an explicitly given linear program with arbitrary real coefficients in strongly polynomial time, answering Smale’s ninth problem. The number of steps is polynomial in the numbers of variables and constraints. For rational input, every intermediate number has bit length polynomial in the full input length. The algorithm returns a strictly complementary optimal pair, a feasible point and an improving ray, or a sparse certificate of infeasibility. The paper also gives algorithms for convex quadratic programming and turn-based mean-payoff games.

The [companion paper on polytope diameter](../Superpolynomial-graph-diameter-of-simple-polytopes-November-24-2026/paper.pdf) shows that even a shortest edge path between two feasible vertices can have superpolynomial length.

## Lean formalization

For rational data with at least one constraint and one variable, Lean proves strongly polynomial feasibility and optimization on fixed rational RAM programs. The instruction count is polynomial in the dimensions, and the bit lengths of stored rationals are polynomial in the input length. In the finite-optimum case the formalized optimization certificate gives primal and dual solutions of equal value. [Feasibility proof](../../lean/OAI/Optimization/LinearProgramming/Feasibility.lean#L10-L15) · [Optimization proof](../../lean/OAI/Optimization/LinearProgramming/Optimization.lean#L10-L14) · [RAM statement and bounds](../../lean/ComparatorChallenges/LinearProgramming.lean#L146-L164) · [Formalization scope](../../lean/docs/380.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.tex) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through latexmk.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:Strongly-polynomial-linear-programming-November-24-2026,
  author = {{OpenAI}},
  title = {{Strongly polynomial linear programming}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Strongly-polynomial-linear-programming-November-24-2026/paper.pdf}{OAI:Strongly-polynomial-linear-programming-November-24-2026}},
  year = {2026}
}
```
