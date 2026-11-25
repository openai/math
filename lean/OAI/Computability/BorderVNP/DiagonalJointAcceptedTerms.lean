import OAI.Computability.BorderVNP.DiagonalJointPositiveProgram

/-! # Accepting preparation and tally fibers of the genuine positive body -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator BorderVNP.Cube
open scoped BigOperators Classical

variable {dim box lanes selectors symbols w teams n : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    {gen : Fragment IO} (S : Fin teams → PositiveTeam id gen n w)

/-- Whether the actual deterministic tally checks return on the prepared cell bank.
This condition precedes any lead-team field computation. -/
def PositiveTeam.tallyReturns (T : PositiveTeam id gen n w) (p : T.Prefix) : Prop :=
  Nonempty (Returns (finishExpansion signedOccurrences) T.pub (install gen n T.routines)
    (cellBank T.pub (install gen n T.routines) p.2.val.2.1 p.2.val.2.2) p.2.val.2.2)

/-- A rejected native tally has no continuation weight. -/
theorem PositiveTeam.readerWeight_reject (T : PositiveTeam id gen n w) (p : T.Prefix)
    (bad : ¬ T.tallyReturns p) : T.readerWeight p = 0 := by
  let mac := install gen n T.routines
  let bank := cellBank T.pub mac p.2.val.2.1 p.2.val.2.2
  let : IsEmpty (Returns (finishExpansion signedOccurrences) T.pub mac bank p.2.val.2.2) :=
    not_nonempty_iff.mp bad
  unfold PositiveTeam.readerWeight tallyValue
  exact Finset.sum_eq_zero fun x _ => isEmptyElim x

variable (joint : ∀ a : (u : Fin teams) → (S u).Prefix,
    JoinedCells (fun u => (S u).pub) (fun u => (S u).postMemory) (fun u => (S u).generated) a)

/-- A joint preparation and all physical private cell bits. Each prefix
already contains its actual local pin guess. -/
abbrev PositiveAssignment := (a : (u : Fin teams) → (S u).Prefix) × (joint a).Private

/-- The physical cell validations and each team's own completed native
subtotal checks are exactly the predicates defining this finite fiber. -/
def positivePass (a : PositiveAssignment S joint) : Prop :=
  (joint a.1).privateWeight a.2 ≠ 0 ∧ ∀ u, (S u).tallyReturns (a.1 u)

/-- The remaining local cell sign times the actual native residue continuation
on all teams. No reduction of the field value is needed to define acceptance. -/
noncomputable def positiveWeight (a : PositiveAssignment S joint) : ℤ :=
  (joint a.1).privateWeight a.2 * ∏ u, (S u).readerWeight (a.1 u)

/-- The product of the bounded, agreeing evaluation bodies is the sum on
true passing native preparations and private cells. Real zero-valued residue
entries remain in the fiber. -/
theorem joint_accepted_sum (hn : 1 ≤ n) :
    (∏ u, boundedValue (signedBody id) (S u).pub (install gen n (S u).routines)
      (S u).bank (S u).memory ((S u).limit-(S u).used) (S u).burst (n^25)) =
      ∑ a : {a : PositiveAssignment S joint // positivePass S joint a}, positiveWeight S joint a.val := by
  refine (joint_positive_program id gen n hn S joint).trans ?_
  simp only [PositiveTeam.prefixWeight_one,Finset.prod_const_one,one_mul]
  refine (Fintype.sum_sigma (fun a : PositiveAssignment S joint => positiveWeight S joint a)).symm.trans ?_
  have no (a : {a : PositiveAssignment S joint // ¬ positivePass S joint a}) :
      positiveWeight S joint a.val = 0 := by
    by_cases z : (joint a.val.1).privateWeight a.val.2 = 0
    · exact mul_eq_zero_of_left z _
    · have failure : ¬ ∀ u, (S u).tallyReturns (a.val.1 u) := fun h => a.property ⟨z,h⟩
      obtain ⟨u,hu⟩ := not_forall.mp failure
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ u) ((S u).readerWeight_reject _ hu))
  have h := Fintype.sum_subtype_add_sum_subtype (positivePass S joint) (positiveWeight S joint)
  simpa only [no,Finset.sum_const_zero,add_zero] using h.symm

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
