import OAI.Computability.VPVNP.RankCoordinateAdvice
import OAI.Computability.VPVNP.RankCoordinateArgumentSelected
import OAI.Computability.VPVNP.RankCoordinateSliceTargets

/-! # Static advice of the two selected slice determinants

Both greedy scans and the ordinary entry reads start from the supplied
base matrix reader. The target uses a zero monomial, mark, and scale in the
cloned template. The two advised scales are the certificate power and its
product with the field order. The dynamic preparation then fills in the
replacement row and the powered monomial for each requested matrix entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate.SelectedAdvice

open RAMTape SliceArithmetic UniversalCountStack NativeReader
open RadicalCertificate.MonomialIndex
open SliceMinors

/-- Workspace ports for reading a denominator entry, with the base matrix reader serving both
pivot scans and the final entry query. -/
abbrev Den (K : Type) := SelectedMinor.Work K K
/-- Ports for the numerator's pivot scans, original matrix entries and powered target entries. -/
abbrev Raw (K : Type) := ArgumentStage.SelectedHost K K
/-- Private ports of the rank-prefix scan that recovers the source row ordinal. -/
abbrev Side (K : Type) := Select.Side K
/-- Port families for the determinant pair, the dynamic index calculation and unary label
conversion. -/
abbrev Parts (K : Type) := Prepare.Parts (Den K) (Raw K) (Side K)
/-- Read-only preparation ports carrying the component templates and the two possible target
scales. -/
abbrev Advice (K : Type) := Prepare.Advice (Den K) (Raw K) (Side K)
/-- Writable preparation ports for the template copies and their temporary stack. -/
abbrev Work (K : Type) := Prepare.Work (Den K) (Raw K) (Side K)

variable {K F : Type} {p e t eqs : ℕ}

/-- The certificate power for a label step, or its product with the field order for a Frobenius
step. -/
def powers (Q : QueryData t eqs F) (b : Bool) := if b then Q.power*Q.fieldOrder else Q.power

variable [DecidableEq K] [Fact p.Prime]

/-- Denominator template with both pivot scans initialized and the selected row and column
words empty. -/
def den (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K) : Stacks (Den K) :=
  Submatrix.workBank [] [] (SelectedMinor.initial w v (height Q) (width Q) c base base)

/-- Initial numerator reader banks for the base matrix, its pivot scans and the powered target
template. -/
def raw (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K) : Stacks (Raw K) :=
  ArgumentStage.selectedRaw w v (height Q) (width Q) c base base (targetTemplate Q) (TargetRead.literal c v)

/-- Numerator workspace before staging, with replacement ordinal zero and empty
selected-address words. -/
def num (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K) : Stacks (ArgumentStage.Num (Raw K)) :=
  Replacement.workBank w (digits w 0) (Submatrix.workBank [] [] (raw c Q w v base))

/-- Idle bank for scanning row ranks of the base matrix with the slice's column count. -/
def side (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K) : Stacks (Side K) :=
  SelectedMinor.selectorBank w v (width Q) c base

/-- Stack-height bound for the greedy row scan together with its ordinal input and output
registers. -/
def selectorCap (K : Type) [Fintype K] (d w v e A S : ℕ) := Select.scanSpace K d w v e A S+OrdinalABI.overhead w

/-- Maximum advised stack height accounting for selected-minor reads, ordinal selection and
determinant initialization. -/
def portBound (K : Type) [Fintype K] (d w v e A S : ℕ) :=
  FullAdvice.portBound w v e (SelectedMinor.space K d w v e A S) (selectorCap K d w v e A S)

variable [Field F] [DecidableEq F]

/-- Static advice for one slice, including the two determinant templates, equation rank, row
counts and target scales. -/
def selectedAdvice (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K) : Stacks (Advice K) :=
  FullAdvice.advice c (order Q) w v (rankQuery Q.equations) (eqs*size t Q.multiplierDegree)
    (den c Q w v base) (num c Q w v base) (side c Q w v base) (powers Q)

/-- The static slice advice paired with an initially empty private preparation workspace. -/
def selectedExtra (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K) : Stacks (Advice K ⊕ Work K) :=
  Sum.elim (selectedAdvice c Q w v base) (fun _ => [])

variable [Fintype K] {d w v A S P : ℕ}

omit [Fact p.Prime] [Field F] [DecidableEq F] in
theorem side_length (c : Vector p e) (Q : QueryData t eqs F) (base : Stacks K)
    (hbase : ∀ k, (base k).length ≤ A) (hm : width Q < 2^w) (k : Side K) :
    (side c Q w v base k).length ≤ selectorCap K d w v e A S := by
  have hw : w ≤ Select.scanSpace K d w v e A S := (Nat.le_add_right ..).trans (le_max_left ..)
  cases k with
  | inl k => exact (RegisterTable.bank_length_le Fin.elim0 0 _ k).trans (hw.trans (Nat.le_add_right ..))
  | inr k => exact (Select.side_length (ready := (· = base)) c base rfl (fun s hs => hs ▸ hbase) hm k).trans (Nat.le_add_right ..)

omit [Field F] [DecidableEq F] in
theorem reader_length (c : Vector p e) (Q : QueryData t eqs F) (base : Stacks K)
    (hbase : ∀ k, (base k).length ≤ A) (hn : height Q < 2^w) (hm : width Q < 2^w)
    (hword : w ≤ P) (harity : t ≤ P) (hscalar : max P (e*v) ≤ A) :
    (∀ k, (den c Q w v base k).length ≤ SelectedMinor.space K d w v e A S) ∧
    (∀ k, (num c Q w v base k).length ≤ SelectedMinor.space K d w v e A S) := by
  let isBase (s : Stacks K) := s = base
  have cap : ∀ s, isBase s → ∀ k, (s k).length ≤ A := fun s hs => hs ▸ hbase
  let target := targetTemplate Q
  let direct := directReady c w v target isBase
  have live : direct (Sum.elim base (TargetRead.bank w target (TargetRead.literal c v))) := ⟨rfl, rfl⟩
  have directCap (s : Stacks (Direct K)) (h : direct s) (k : Direct K) : (s k).length ≤ A := by
    rcases k with k | k
    · exact cap _ h.1 k
    · exact (TargetRead.ready_bound c target h.2 hword harity k).trans hscalar
  constructor
  · apply SelectedMinor.den_ready_length (pivot := isBase) (ready := isBase) base rfl cap cap hn hm
    exact ⟨_, SelectedMinor.initial_ready base base rfl, rfl⟩
  · apply SelectedMinor.num_ready_length (pivot := isBase) (ready := direct) base rfl cap directCap hn hm 0
    exact ⟨_, ⟨_, SelectedMinor.initial_ready base _ live, rfl⟩, rfl⟩

omit [DecidableEq K] [Fact p.Prime] [Fintype K] in
theorem order_lt (Q : QueryData t eqs F) (hn : height Q < 2^w) : order Q < 2^w := by
  exact lt_of_le_of_lt (by simpa only [order, rankQuery_eq, Fintype.card_fin] using
    (fieldMatrix Q).rank_le_card_height) hn

variable (c : Vector p e) (Q : QueryData t eqs F) (base : Stacks K)
    (hbase : ∀ k, (base k).length ≤ A) (hn : height Q < 2^w) (hm : width Q < 2^w)
    (hword : w ≤ P) (harity : t ≤ P) (hscalar : max P (e*v) ≤ A) (hv : Word.workingWidth p ≤ v)

include hbase hn hm hword harity hscalar hv

/-- Every advised stack and every initially empty private stack fits the
same concrete cap for all current/next ordinals and for both operations. -/
theorem extra_length (k : Advice K ⊕ Work K) : (selectedExtra c Q w v base k).length ≤ portBound K d w v e A S := by
  obtain ⟨hd,hu⟩ := reader_length (d := d) (S := S) c Q base hbase hn hm hword harity hscalar
  exact FullAdvice.extra_length c (order Q) w v (rankQuery Q.equations) (eqs*size t Q.multiplierDegree)
    (den c Q w v base) (num c Q w v base) (side c Q w v base) (powers Q) _ _ (order_lt Q hn) hv hd hu
    (side_length c Q base hbase hm) k

/-- The clone and the public entry words fit their actual initialization and
ambient capacities before the physical preparation machine starts. -/
theorem fit (label cur next : ℕ) :
    let M := portBound K d w v e A S
    let root := RootInit.template c (order Q) w v (den c Q w v base) (num c Q w v base)
    let dyn := Dynamic.bank (side c Q w v base) (Dynamic.regs (w := w) 0 0 (rankQuery Q.equations) (eqs*size t Q.multiplierDegree) 0 0 0 0)
    let unary := UnaryWord.store [] [] (digits w 0) [] []
    (∀ i, (root i).length ≤ M) ∧ (∀ i, (dyn i).length ≤ M) ∧ (∀ i, (unary i).length ≤ M) ∧
      (∀ k, (state (List.replicate label true) (digits w cur) (digits w next) [] (selectedAdvice c Q w v base)
        (fun _ : Work K => []) k).length ≤ max label M) := by
  obtain ⟨hd,hu⟩ := reader_length (d := d) (S := S) c Q base hbase hn hm hword harity hscalar
  exact FullAdvice.fit c (order Q) w v (rankQuery Q.equations) (eqs*size t Q.multiplierDegree)
    (den c Q w v base) (num c Q w v base) (side c Q w v base) (powers Q) _ _ (order_lt Q hn) hv hd hu
    (side_length c Q base hbase hm) label cur next

end RankQuery.Stack.Coordinate.SelectedAdvice

end

end VPVNP
end Computability
end OAI
