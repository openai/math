import OAI.Computability.BorderVNP.DiagonalLocalTallies

/-!
# Unary count words inside packed local boxes

Several weighted unary factors can occupy one public cell. A local assignment
of that cell's fine variables determines their individual use bits. Grouping
several copies into a shared cable changes these use bits only by slicing the
word read at the public vertex.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing MvPolynomial
open scoped BigOperators Classical

/-- A unary power occurrence, indexed by its original batch, parameter, and bit. -/
abbrev PowerSlot (Team Param : Type*) (b : ℕ) := Team × Param × Fin b

variable {D b : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {Team Param Gadget : Type*} [Fintype Team] [Fintype Param]
    {tags : N.Tables (Entry Param Gadget)}

/-- Formal exponent contributed by one unary use bit. -/
noncomputable def slotPower (w : PowerSlot Team Param b) (bit : Bool) : Param →₀ ℕ :=
  Finsupp.single w.2.1 (if bit then 2 ^ w.2.2.val else 0)

omit [Fintype Team] [Fintype Param] in
@[simp] theorem slotPower_false (w : PowerSlot Team Param b) : slotPower w false = 0 := by
  simp [slotPower]

/-- Selected powers at a cell, with one unique physical owner for every
original occurrence. The owner map need not be injective. -/
structure PowerWords (Team Param Gadget : Type*) [Fintype Team] [Fintype Param] (b : ℕ)
    (N : Network D P bits) (tags : N.Tables (Entry Param Gadget)) where
  /-- Current host site of each original unary factor. -/
  site : PowerSlot Team Param b → N.Site
  /-- Read the selected original bits from the current local words. -/
  selected : N.Tables (PowerSlot Team Param b → Bool)
  /-- Only the owning host can activate an occurrence. -/
  located : ∀ v z x w, selected v z x w = true → site w = v
  /-- The sum of all recorded contributions is the local parameter exponent. -/
  exact : ∀ v z x, (counters (tags v z x)).1 = ∑ w, slotPower w (selected v z x w)

namespace PowerWords

variable (words : PowerWords Team Param Gadget b N tags)
    (edges : PowerSites.LocalEdges N) (ports : PowerSites.LocalPorts N)

/-- Extract each selected bit at its one physical owner. -/
noncomputable def localUse (t : Team) (p : Param) (j : Fin b) : Bool :=
  let v := words.site (t,p,j)
  words.selected v (edges v) (ports v) (t,p,j)

/-- Even if a single box contains many unary occurrences and opposite
endpoints receive different words, every parameter power is tallied once. -/
theorem sum_local_exponents :
    (∑ v, (counters (tags v (edges v) (ports v))).1) =
      ∑ t, batchExponent (words.localUse edges ports t) := by
  simp_rw [words.exact]
  rw [Finset.sum_comm]
  have h (w : PowerSlot Team Param b) :
      (∑ v, slotPower w (words.selected v (edges v) (ports v) w)) =
        slotPower w (words.selected (words.site w) (edges _) (ports _) w) := by
    apply Finset.sum_eq_single (words.site w)
    · intro v _ hv
      have hfalse : words.selected v (edges v) (ports v) w = false := by
        cases hbit : words.selected v (edges v) (ports v) w with
        | false => rfl
        | true => exact False.elim (hv (words.located v _ _ w hbit).symm)
      simp [hfalse]
    · simp
  simp_rw [h]
  simp only [PowerSlot, Fintype.sum_prod_type, slotPower, batchExponent,
    Finsupp.single_finsetSum, localUse]
  rfl

variable {Extra E : Type*} [Fintype Extra] (extra : Extra → Entry Param Gadget)
    (owner : N.Site ⊕ Extra → Team)

/-- The subtotals of the actual grouped host factors and the extra cube positions. -/
noncomputable def localTally : Tally Team Param Gadget b where
  powers := words.localUse edges ports
  counts t g := ∑ v : {v : N.Site ⊕ Extra // owner v = t},
    (counters (v.val.elim (fun w => tags w (edges w) (ports w)) extra)).2 g

/-- Every passing grouped host and packet term evaluates to the monomial
specified by the subtotals of the respective cells and cube vertices. -/
theorem interpret_local_product [Field E] [Fintype Gadget] (values : Gadget → E)
    (hscalar : ∀ i, (counters (extra i)).1 = 0)
    (hpass : (∏ v, tags v (edges v) (ports v)) * (∏ i, extra i) ≠ 0) :
    interpret values ((∏ v, tags v (edges v) (ports v)) * (∏ i, extra i)) =
      monomial (words.localTally edges ports extra owner).exponents
        ((words.localTally edges ports extra owner).coefficient values) := by
  let factors : N.Site ⊕ Extra → Entry Param Gadget :=
    Sum.elim (fun v => tags v (edges v) (ports v)) extra
  have hsplit : (∏ v, factors v) = (∏ v, tags v (edges v) (ports v)) * (∏ i, extra i) :=
    Fintype.prod_sum_type factors
  rw [← hsplit] at hpass ⊢
  have hp := Finset.prod_ne_zero_iff.mp hpass
  rw [counters_prod factors (fun i => hp i (Finset.mem_univ _)), interpret_passed]
  have hμ : (∑ v, (counters (factors v)).1) = (words.localTally edges ports extra owner).exponents := by
    rw [Fintype.sum_sum_type]
    simp only [factors, Sum.elim_inl, Sum.elim_inr, hscalar, Finset.sum_const_zero, add_zero]
    exact words.sum_local_exponents edges ports
  rw [hμ, Finsupp.prod_pow]
  apply congrArg (monomial _)
  unfold Tally.coefficient
  apply Finset.prod_congr rfl
  intro g _
  apply congrArg (fun i : ℕ => values g ^ i)
  rw [Finsupp.finsetSum_apply]
  exact (Fintype.sum_fiberwise owner (fun v => (counters (factors v)).2 g)).symm

/-- Transport grouped words across cutting and sewing. New local boxes
may contain arbitrarily many scalar gadget factors. -/
noncomputable def cutSew (S : Finset N.Edge)
    (G : Network D (N.CutPorts S) (N.cutWidths S)) (inner : G.Tables (Entry Param Gadget))
    (hzero : ∀ v z x, (counters (inner v z x)).1 = 0) :
    PowerWords Team Param Gadget b ((N.cut S).sew G)
      ((N.cut S).sewTables G (N.cutTables S tags) inner) where
  site w := .inl (words.site w)
  selected := (N.cut S).sewTables G (N.cutTables S words.selected) (fun _ _ _ _ => false)
  located v z x w hbit := by
    rcases v with old | new
    · exact congrArg Sum.inl (words.located old _ _ w hbit)
    · contradiction
  exact v z x := by
    rcases v with old | new
    · exact words.exact old _ _
    · change (counters (inner new _ _)).1 = ∑ w, slotPower w false
      simp only [slotPower_false, Finset.sum_const_zero]
      exact hzero new _ _

end PowerWords
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
