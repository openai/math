# Readme

This repository contains mathematical manuscripts and supporting proof artifacts produced by an unnamed internal OpenAI model. 

As part of model development, we evaluate our models on open research problems. We expanded these evaluations after performance on our existing mathematical evaluations saturated. Some outputs build upon earlier results produced by the models.

This collection includes results at different stages of verification. Not all have accompanying Lean formalizations. We will continue to update this repository with Lean formalizations as we obtain them. 

Some of the unformalized results could have issues. We will endeavor to fix any such issues quickly.
We are also exploring community-hosted repositories for these materials. 

In our view, these manuscripts are best understood as a form of raw research data, rather than polished academic papers. We defer to the math community completely on matters of credit, precedence, and concurrent work.

## Navigating the collection

The current catalogue contains 722 manuscripts organized into 374 families. A family groups related papers, which may include a principal result, companion arguments, consequences, or alternative proofs. Each family is classified by mathematical discipline.

- Start with the [overview](overview.pdf) for descriptions of the families.
- Use the [manuscript map](CONTENTS.md) to find individual papers and their supporting materials.
- The [`preprints/`](preprints/) directory contains PDFs, source files, and manuscript-specific citation and build instructions.
- The [Lean library](lean/README.md) and [formalization catalogue](lean/formalization.yaml) describe the available formal proofs, their associated papers, and verification configurations. See the [Comparator instructions](lean/ComparatorChallenges/README.md) for additional checking instructions. The repository has ~42% top-line results formalized.
- Updates to the repo are described in the [history](history.md).

### Reasoning summaries

We are also releasing abridged summaries of the model's reasoning, covering the following results:

| Family | Subject |
|---|---|
| 007 | [Ordinary two-point correlations of multiplicative functions](reasoning_traces/ordinary-two-point-correlations.pdf) |
| 017 | [The irrationality exponent of π](reasoning_traces/irrationality-exponent-of-pi.pdf) |
| 087 | [Symmetric and general Mahler conjectures](reasoning_traces/symmetric-and-general-mahler-conjectures.pdf) |
| 102 | [Ordinary NP-hardness at the basic semidefinite threshold](reasoning_traces/basic-semidefinite-threshold-np-hardness.pdf) |
| 159 | [Quasipolynomial bounds for arithmetic progressions](reasoning_traces/quasipolynomial-arithmetic-progressions.pdf) |
| 197 | [Kaplansky's direct-finiteness conjecture in characteristic two](reasoning_traces/kaplansky-direct-finiteness-characteristic-two.pdf) |
| 221 | [The Mézard–Parisi formula for diluted spin glasses](reasoning_traces/mezard-parisi-formula.pdf) |
| 271 | [Spontaneous magnetization in the quantum Heisenberg ferromagnet](reasoning_traces/spontaneous-magnetization-quantum-heisenberg-ferromagnet.pdf) |
| 287 | [Isomorphism of free group factors](reasoning_traces/free-group-factor-isomorphism.pdf) |
| 362 | [The three-dimensional relativistic Vlasov–Maxwell system](reasoning_traces/relativistic-vlasov-maxwell.pdf) |


## How the results were produced

The vast majority of results were obtained with the same procedure using an unreleased internal OpenAI model. On average, each result used three hours of ChatGPT Pro thinking compute with that model. Over the course of the evaluation, the model was posed approximately 4,000 problems. Aggregating the output into result families and manuscripts and requiring an appropriate level of significance led to the catalog outlined above.

Exceptions to this fixed procedure include work on a zero-free region for the Riemann zeta function and proof of the Hodge Conjecture for CM abelian varieties. Additionally, the writeup for the Re(s) > 11/12 zero-free region for the Riemann zeta function was human edited for readability. 


## Versions and citations

We will preserve the public release history of this collection. Corrections and revisions will be recorded as new versions, with previously released versions remaining accessible. 

To cite the individual manuscript, use the BibTeX block in its directory. 
