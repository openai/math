import OAI.Computability.VPVNP.DegreeRefreshMotif

/-!
# Expanding all degree-refresh motifs

Each block independently chooses a term of its internal motif identity. For
that choice, the product of block contractions is a sum over one shared
payload per internal supply edge. The outer external wire assignment remains
common to both of its incident blocks. This gives the portwise product and
the branch-dependent sums in equation (7.1) for the degree refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

open WireTensor

variable {B R S : Type*} {d : ℕ} [Fintype B] [Fintype S] [CommSemiring R]
variable {I : B → Type*} [∀ s, Fintype (I s)]
variable (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (a b : S → Fin d)
variable (A : (s : B) → I s → S → Type*) [∀ s i e, Fintype (A s i e)]

/-- The local supply network in the selected term of one block. -/
noncomputable abbrev blockSupply (s : B) (i : I s) :=
  wireNetwork (k := R) a b (A s i)

variable (M : ∀ s (i : I s) j, (internalDemand R t w s).Basis j →
  (blockSupply (R := R) a b A s i).Basis j → R)

/-- The matrix entry at one port multiplies its two local diagonal tests by
the entry of the block motif map. Only the incident half-wires are read. -/
noncomputable def refreshFactor (s : B) (i : I s) (j : Fin d)
    (x : (oldNetwork R t w).Basis (s,j)) (z : PortSegments t w s j)
    (y : (blockSupply (R := R) a b A s i).Basis j) : R :=
  portDiagonal t w s j x z * M s i j (portInput t w s j x z) y

/-- The external-bundle identity and the ordinary local identities in all
blocks give the edge-indexed expansion with independent choices in each block. -/
theorem refresh_edge_expansion
    (h : ∀ s, (internalDemand R t w s).coeff =
      ∑ i, applyLocal (M s i) (blockSupply (R := R) a b A s i).coeff)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) :
    (oldNetwork R t w).coeff x =
      ∑ c : (s : B) → I s, ∑ z : External w, ∑ y : (s : B) → (e : S) → A s (c s) e,
        ∏ s, ∏ j, refreshFactor t w a b A M s (c s) j (x (s,j)) (portSegments t w z s j)
          (edgeAssignment a b (y s) j) := by
  let term (z : External w) (s : B) (i : I s) (y : (e : S) → A s i e) :=
    ∏ j, refreshFactor t w a b A M s i j (x (s,j)) (portSegments t w z s j)
      (edgeAssignment a b y j)
  have localSum (z : External w) (s : B) :
      blockTies t w x z s = ∑ i, ∑ y, term z s i y := by
    rw [blockTies_factor, h, Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [applyLocal_wireNetwork a b (A s i) (M s i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact (Finset.prod_mul_distrib).symm
  rw [external_contraction]
  simp_rw [localSum]
  simp_rw [Fintype.prod_sum]
  exact Finset.sum_comm

end Compression.Refresh

end VPVNP
end Computability
end OAI
