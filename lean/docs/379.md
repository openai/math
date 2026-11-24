# Separation of VP and VNP over every field

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [VP and VNP are different](../../preprints/VP-and-VNP-are-different-November-23-2026/paper.pdf)

## Scope

The formalization proves that VP differs from VNP over every field in the nonuniform model of exact arithmetic circuits with binary addition, subtraction, and multiplication gates. It gives an explicit VNP-complete family whose $n$th polynomial is homogeneous of degree $n$ and multilinear in $2n$ variables. For each exponent $C\ge 1$ and each characteristic, its exact circuit size exceeds $n^C$ for all sufficiently large $n$, with a threshold uniform over fields of that characteristic.

Lean also proves this superpolynomial exact circuit lower bound for the directed Hamiltonian cycle polynomial over every field and for the permanent over fields of characteristic other than two. The paper gives the stronger lower bound $\exp(\Omega((\log n)^{5/4}))$ for border circuits.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Separation of exact VP and VNP over every field | [VPVNP.lean](../ComparatorChallenges/VPVNP.lean) |
