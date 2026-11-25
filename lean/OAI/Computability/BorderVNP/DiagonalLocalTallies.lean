import OAI.Computability.BorderVNP.DiagonalPowerSites

/-! # Reading per-team tallies after the two ends of a packet are separated -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PowerSites

open Crossing MvPolynomial
open scoped BigOperators Classical

variable {D b : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {Team Param Gadget : Type*} {tags : N.Tables (Entry Param Gadget)}
    (sites : PowerSites Team Param Gadget b N tags)

/-- The independent incident cable words read by every original site. -/
abbrev LocalEdges (N : Network D P bits) :=
  (v : N.Site) → (e : {e : N.Edge // N.src e = v ∨ N.dst e = v}) → Fin (N.width e.val) → Bool

/-- The external port words read by every original site. -/
abbrev LocalPorts (N : Network D P bits) :=
  (v : N.Site) → (i : {i : P // N.attach i = v}) → Fin (bits i.val) → Bool

variable (edges : LocalEdges N) (ports : LocalPorts N)

/-- The bit at an original weighted unary site after its cable word has been supplied. -/
noncomputable def localUse (t : Team) (p : Param) (j : Fin b) : Bool :=
  let v := sites.site (t,p,j)
  decide ((counters (tags v (edges v) (ports v))).1 ≠ 0)

variable [Fintype Team] [Fintype Param]

/-- The binary powers still form exactly one word per parameter and batch
when different sites receive independent words at former wire ends. -/
theorem sum_local_exponents :
    (∑ v, (counters (tags v (edges v) (ports v))).1) =
      ∑ t, batchExponent (sites.localUse edges ports t) := by
  let localTags : N.Tables (Entry Param Gadget) := fun v _ _ => tags v (edges v) (ports v)
  let frozen : PowerSites Team Param Gadget b N localTags :=
    ⟨sites.site, fun w _ _ => sites.named w _ _, fun v h _ _ => sites.other v h _ _⟩
  exact frozen.sum_exponents (fun _ _ => false) (fun _ _ => false)

variable {Extra E : Type*} [Fintype Extra]
    (extra : Extra → Entry Param Gadget) (owner : N.Site ⊕ Extra → Team)

/-- Assign host and cube entries to their actual owner teams before taking
scalar subtotals. Only the original weighted sites supply parameter bits. -/
noncomputable def localTally : Tally Team Param Gadget b where
  powers := sites.localUse edges ports
  counts t g := ∑ v : {v : N.Site ⊕ Extra // owner v = t},
    (counters (v.val.elim (fun w => tags w (edges w) (ports w)) extra)).2 g

/-- Interpret a passing assigned term, including all the scalar factors
chosen by the independent cube selectors. This formula uses the same
per-team counters read by the entry processor. -/
theorem interpret_local_product [Field E] [Fintype Gadget] (values : Gadget → E)
    (hscalar : ∀ i, (counters (extra i)).1 = 0)
    (hpass : (∏ v, tags v (edges v) (ports v)) * (∏ i, extra i) ≠ 0) :
    interpret values ((∏ v, tags v (edges v) (ports v)) * (∏ i, extra i)) =
      monomial (sites.localTally edges ports extra owner).exponents
        ((sites.localTally edges ports extra owner).coefficient values) := by
  let factors : N.Site ⊕ Extra → Entry Param Gadget :=
    Sum.elim (fun v => tags v (edges v) (ports v)) extra
  have hsplit : (∏ v, factors v) = (∏ v, tags v (edges v) (ports v)) * (∏ i, extra i) :=
    Fintype.prod_sum_type factors
  rw [← hsplit] at hpass ⊢
  have hp := Finset.prod_ne_zero_iff.mp hpass
  rw [counters_prod factors (fun i => hp i (Finset.mem_univ _)), interpret_passed]
  have hμ : (∑ v, (counters (factors v)).1) = (sites.localTally edges ports extra owner).exponents := by
    rw [Fintype.sum_sum_type]
    simp only [factors, Sum.elim_inl, Sum.elim_inr, hscalar, Finset.sum_const_zero, add_zero]
    exact sites.sum_local_exponents edges ports
  rw [hμ, Finsupp.prod_pow]
  apply congrArg (monomial _)
  unfold Tally.coefficient
  apply Finset.prod_congr rfl
  intro g _
  apply congrArg (fun i : ℕ => values g ^ i)
  rw [Finsupp.finsetSum_apply]
  exact (Fintype.sum_fiberwise owner (fun v => (counters (factors v)).2 g)).symm

/-- The coarse degree budget remains valid for every row of the final packet expansion. -/
theorem local_degree_le :
    (sites.localTally edges ports extra owner).exponents.degree ≤
      Fintype.card Team * Fintype.card Param * (2 ^ b - 1) :=
  exponent_degree_le _

end Diagonal.CellEntries.PowerSites

end BorderVNP
end Computability
end OAI
