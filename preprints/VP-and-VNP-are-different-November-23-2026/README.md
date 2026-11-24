# [VP and VNP are different](paper.pdf)

OpenAI · November 23, 2026 edition

Theorem 1.1 gives a border arithmetic circuit size lower bound of
$\exp(\Omega((\log n)^{5/4}))$ for an explicit VNP family over every field.
Corollary 1.2 transfers the bound to the directed Hamiltonian cycle polynomial
over every field and to the permanent outside characteristic two.
The [Lean proof of the exact VP–VNP separation](../../lean/OAI/Computability/VPVNP/ClassSeparation.lean)
is also available in this repository.

## Manuscript files

The [LaTeX source](build/Paper.tex) contains the full proof, with
[TikZ figures](build/figures/) and an editable [bibliography](build/references.tex).
To regenerate the [PDF](paper.pdf) with Tectonic, run these commands from this directory.

```sh
cd build
tectonic Paper.tex
cp Paper.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{OAI:VP-and-VNP-are-different-November-23-2026,
  author = {{OpenAI}},
  title = {{VP and VNP are different}},
  year = {2026},
  note = {November 23 edition}
}
```
