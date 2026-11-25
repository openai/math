import OAI.Computability.BorderVNP.DiagonalPaidReplacement
import OAI.Computability.BorderVNP.DiagonalEvaluator
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Reading the unique unary power positions of an expanded pack -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening MvPolynomial
open scoped BigOperators Classical

variable {D b : ℕ} {P : Type*} {bits : P → ℕ} {Param Gadget Team E : Type*}

/-- Read back the two counter arrays of a passing factor. On a failed factor
the readback is immaterial and is set to zero. -/
def counters (z : Entry Param Gadget) : (Param →₀ ℕ) × (Gadget →₀ ℕ) :=
  WithZero.recZeroCoe 0 Multiplicative.toAdd z

@[simp] theorem counters_passed (μ : Param →₀ ℕ) (δ : Gadget →₀ ℕ) :
    counters (passed μ δ) = (μ, δ) := rfl

private theorem passed_counters {z : Entry Param Gadget} (hz : z ≠ 0) :
    passed (counters z).1 (counters z).2 = z := by
  induction z using WithZero.recZeroCoe with
  | zero => contradiction
  | coe z => rfl

/-- A product of passing entries retains the sum of both independent tallies. -/
theorem counters_prod {A : Type*} [Fintype A] (f : A → Entry Param Gadget)
    (hp : ∀ i, f i ≠ 0) :
    (∏ i, f i) = passed (∑ i, (counters (f i)).1) (∑ i, (counters (f i)).2) := by
  let g := fun i => Multiplicative.ofAdd (counters (f i))
  have hfg (i) : f i = WithZero.coeMonoidHom (g i) := (passed_counters (hp i)).symm
  simp_rw [hfg]
  rw [← map_prod, ← ofAdd_sum]
  change WithZero.coeMonoidHom (Multiplicative.ofAdd (∑ i, counters (f i))) = _
  apply congrArg (fun z : (Param →₀ ℕ) × (Gadget →₀ ℕ) => WithZero.coeMonoidHom (Multiplicative.ofAdd z))
  apply Prod.ext
  · exact map_sum (AddMonoidHom.fst _ _) _ _
  · exact map_sum (AddMonoidHom.snd _ _) _ _

/-- The original unary positions survive as distinct sites. Outside those
sites no parameter exponent is accumulated, even inside a grouped gadget. -/
structure PowerSites (Team Param Gadget : Type*) (b : ℕ) (N : Network D P bits)
    (tags : N.Tables (Entry Param Gadget)) where
  /-- One physical site per batch, parameter and place in the count word. -/
  site : Team × Param × Fin b ↪ N.Site
  /-- At that site the exponent is zero or the specified power of two. -/
  named : ∀ w z x, (counters (tags (site w) z x)).1 = 0 ∨
    (counters (tags (site w) z x)).1 = Finsupp.single w.2.1 (2 ^ w.2.2.val)
  /-- Every other site is a Boolean or gadget factor with zero parameter tally. -/
  other : ∀ v, v ∉ Set.range site → ∀ z x, (counters (tags v z x)).1 = 0

variable {N : Network D P bits} {tags : N.Tables (Entry Param Gadget)}
variable (sites : PowerSites Team Param Gadget b N tags)

/-- The actual unary selections recovered from a complete network assignment. -/
noncomputable def PowerSites.use (a : N.Assignment) (x : Ports bits) (t : Team)
    (p : Param) (j : Fin b) : Bool :=
  decide ((counters (N.read tags a x (sites.site (t,p,j)))).1 ≠ 0)

variable [Fintype Param] [Fintype Team]

/-- The local tallies at every vertex equal the sum of the readback words
at the surviving unary factors. -/
theorem PowerSites.sum_exponents (a : N.Assignment) (x : Ports bits) :
    (∑ v, (counters (N.read tags a x v)).1) = ∑ t, batchExponent (sites.use a x t) := by
  let F := fun v => (counters (N.read tags a x v)).1
  have hnamed (w : Team × Param × Fin b) : F (sites.site w) =
      Finsupp.single w.2.1 (if sites.use a x w.1 w.2.1 w.2.2 then 2 ^ w.2.2.val else 0) := by
    obtain ⟨t,p,j⟩ := w
    rcases sites.named (t,p,j) (fun e => a e.val) (fun i => x i.val) with hz | hbit
    · change F (sites.site _) = 0 at hz
      simpa only [PowerSites.use, show (counters (N.read tags a x (sites.site (t,p,j)))).1 = 0 from hz,
        ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, Finsupp.single_zero] using hz
    · change F (sites.site _) = Finsupp.single p (2 ^ j.val) at hbit
      have hn : F (sites.site (t,p,j)) ≠ 0 := by simp [hbit]
      change F (sites.site _) = Finsupp.single p (if decide (F (sites.site _) ≠ 0) then _ else _)
      rw [ite_eq_left (decide_eq_true hn)]
      exact hbit
  have hred : (∑ v, F v) = ∑ v ∈ Finset.univ.map sites.site, F v := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro v _ hv
    have h : v ∉ Set.range sites.site := fun ⟨w,hw⟩ => hv (Finset.mem_map.mpr ⟨w,Finset.mem_univ _,hw⟩)
    exact sites.other v h _ _
  rw [hred, Finset.sum_map]
  simp only [hnamed, Fintype.sum_prod_type, batchExponent, Finsupp.single_finsetSum]

/-- Every passing assigned term is literally one monomial of degree within
the residue bound, and its coefficient is the product of gadget entries
raised to their counted multiplicities. -/
theorem PowerSites.interpret_assignment [CommSemiring E] (values : Gadget → E)
    (a : N.Assignment) (x : Ports bits) (hpass : assignmentEntry N tags a x ≠ 0) :
    interpret values (assignmentEntry N tags a x) =
      monomial (∑ t, batchExponent (sites.use a x t))
        ((∑ v, (counters (N.read tags a x v)).2).prod fun g n => values g ^ n) := by
  have hv := Finset.prod_ne_zero_iff.mp hpass
  rw [assignmentEntry, counters_prod _ (fun v => hv v (Finset.mem_univ _)),
    interpret_passed, sites.sum_exponents]

/-- The exponents are grouped by original batch; scalar multiplicities
are grouped by the team to which the corresponding site was assigned. -/
noncomputable def PowerSites.tally (owner : N.Site → Team) (a : N.Assignment)
    (x : Ports bits) : Tally Team Param Gadget b where
  powers := sites.use a x
  counts t g := ∑ v : {v : N.Site // owner v = t}, (counters (N.read tags a x v.val)).2 g

omit [Fintype Param] in
/-- The counts sent to the other teams recover every gadget multiplicity. -/
theorem PowerSites.sum_counts (owner : N.Site → Team) (a : N.Assignment)
    (x : Ports bits) (g : Gadget) :
    (∑ t, (sites.tally owner a x).counts t g) = (∑ v, (counters (N.read tags a x v)).2) g := by
  rw [Finsupp.finsetSum_apply]
  exact Fintype.sum_fiberwise owner (fun v => (counters (N.read tags a x v)).2 g)

/-- Interpret all passing assignments in the input format of the residue
reader. Each path is a genuine assignment of every internal cable. -/
theorem PowerSites.value_eq_passing_tallies [Field E] [Fintype Gadget]
    (owner : N.Site → Team) (values : Gadget → E) (x : Ports bits) :
    N.value (fun v a y => interpret values (tags v a y)) x =
      ∑ z : {z : N.Assignment // assignmentEntry N tags z x ≠ 0},
        monomial (sites.tally owner z.val x).exponents
          ((sites.tally owner z.val x).coefficient values) := by
  rw [value_eq_passing_sum]
  rw [Finset.sum_subtype (p := fun z => assignmentEntry N tags z x ≠ 0) _
    (fun z => by simp)]
  apply Finset.sum_congr rfl
  intro z _
  rw [sites.interpret_assignment values z.val x z.property, Finsupp.prod_pow]
  congr 1
  unfold Tally.coefficient
  simp_rw [sites.sum_counts]

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
