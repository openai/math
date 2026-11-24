import OAI.Computability.VPVNP.RankCoordinateOrdinal
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-!
# Entry reads for the selected Cramer submatrix

Two ordinal selectors return original row and column addresses into distinct
scratch words. The scalar reader uses both words directly. Their bits are
discarded before returning to the determinant engine, so later queries can
reuse the same two words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.CallClear

open RAMTape UniversalCountStack

/-- Popping a stack to empty never increases the peak height of any stack. -/
theorem clear_bounded {K : Type} [DecidableEq K] (k : K) (s : Stacks K) (S : ℕ)
    (fits : ∀ i, (s i).length ≤ S) :
    (clear k).BoundedRun S ((s k).length+1) s (Function.update s k []) := by
  generalize h : s k = bits
  induction bits generalizing s with
  | nil =>
    have pop := StackStep.pop (s := s) (code := (clear k).body.standalone) (q := some ())
      (show (clear k).body.standalone (some ()) = .pop k (fun b => b.map fun _ => ()) from rfl)
    rw [h] at pop
    refine .cons fits pop (.nil _ _ ?_)
    intro i
    by_cases hi : i = k
    · subst i; simp
    · simpa [hi] using fits i
  | cons b bits ih =>
    have pop := StackStep.pop (s := s) (code := (clear k).body.standalone) (q := some ())
      (show (clear k).body.standalone (some ()) = .pop k (fun b => b.map fun _ => ()) from rfl)
    rw [h] at pop
    have later := ih (Function.update s k bits) (fun i => by
      by_cases hi : i = k
      · subst i
        have hlen := fits k
        rw [h, List.length_cons] at hlen
        simpa using Nat.le_of_succ_le hlen
      · simpa [hi] using fits i) (Function.update_self ..)
    rw [Function.update_idem] at later
    exact .cons fits pop later

end SliceArithmetic.CallClear

namespace RankQuery.Stack.Coordinate.Submatrix

open RAMTape UniversalCountStack
open SliceArithmetic.CallClear (clear clear_bounded)

/-- Private ports holding the selected original row and column ordinals together with the
scalar reader's workspace. -/
inductive Work (K : Type) where
  | row | col | aux (k : K)
  deriving DecidableEq, Fintype

/-- Public row, column and scalar-result ports extended by the selected-submatrix workspace. -/
abbrev Port (K : Type) := MacaulayRead.Port (Work K)

variable {K : Type}

/-- Installs the two selected address words alongside the underlying scalar reader's stacks. -/
def workBank (row col : List Bool) (s : Stacks K) : Stacks (Work K)
  | .row => row | .col => col | .aux k => s k

/-- Both original addresses are recomputed for each scalar query. -/
def Ready (ready : Stacks K → Prop) (s : Stacks (Work K)) : Prop :=
  ∃ a, ready a ∧ s = workBank [] [] a

private def rowPorts : OrdinalRead.Port K → Port K
  | .input => .row | .result => .aux .row | .aux k => .aux (.aux k)

private def colPorts : OrdinalRead.Port K → Port K
  | .input => .col | .result => .aux .col | .aux k => .aux (.aux k)

private def scalarPorts : MacaulayRead.Port K → Port K
  | .row => .aux .row | .col => .aux .col | .result => .result | .aux k => .aux (.aux k)

private theorem rowInj : Function.Injective (rowPorts (K := K)) := by
  intro a b hab; cases a <;> cases b <;> simp_all [rowPorts]

private theorem colInj : Function.Injective (colPorts (K := K)) := by
  intro a b hab; cases a <;> cases b <;> simp_all [colPorts]

private theorem scalarInj : Function.Injective (scalarPorts (K := K)) := by
  intro a b hab; cases a <;> cases b <;> simp_all [scalarPorts]

/-- The caller supplies dense row and column indices, and receives the
selected entry on its own scalar result stack. -/
def minorRead (rows cols : FiniteRoutine (OrdinalRead.Port K))
    (entry : FiniteRoutine (MacaulayRead.Port K)) : FiniteRoutine (Port K) :=
  ((((rows.onPorts rowPorts).followedBy (cols.onPorts colPorts)).followedBy
    (entry.onPorts scalarPorts)).followedBy (clear (.aux .row))).followedBy (clear (.aux .col))

variable [DecidableEq K] {p e n m r s w v Br Bc Be S : ℕ} {c : SliceArithmetic.Vector p e}
    {ready : Stacks K → Prop} {rows cols : FiniteRoutine (OrdinalRead.Port K)}
    {entry : FiniteRoutine (MacaulayRead.Port K)} {M : Matrix (Fin n) (Fin m) (Scalar c)}
    {f : Fin r → Fin n} {g : Fin s → Fin m}

local macro "outside" : tactic => `(tactic|
  (intro k hk; cases k with
   | aux u => cases u <;> first | rfl | exact (hk (.aux _) rfl).elim | exact (hk .result rfl).elim
   | row | col | result => first | rfl | exact (hk .result rfl).elim))

/-- The square and rectangular versions use the same finite code. Only the
two short erase scans are added to the selectors' and entry reader's costs. -/
theorem correctSpace (hr : OrdinalRead.CorrectSpace rows f w Br S ready)
    (hc : OrdinalRead.CorrectSpace cols g w Bc S ready)
    (he : MacaulayRead.CorrectSpace entry M w v Be S ready) :
    MacaulayRead.CorrectSpace (minorRead rows cols entry) (M.submatrix f g) w v
      (Br+Bc+Be+2*(w+1)) S (Ready ready) := by
  rintro i j _ ⟨a, ha, rfl⟩
  let state (row col result : List Bool) (u : Stacks K) :=
    MacaulayRead.bank w i j result (workBank row col u)
  let ri := digits w (f i)
  let cj := digits w (g j)
  let val := Engine.scalar v (M (f i) (g j))
  obtain ⟨tr, htr, b, hb, row⟩ := hr i a ha
  obtain ⟨tc, htc, d, hd, col⟩ := hc j b hb
  obtain ⟨te, hte, u, hu, read⟩ := he (f i) (g j) d hd
  have rowRun : (rows.onPorts rowPorts).BoundedRun S tr (state [] [] [] a) (state ri [] [] b) := by
    apply FiniteRoutine.BoundedRun.framed rowInj row _ (fun k => by cases k <;> rfl)
      (fun k => by cases k <;> rfl) (by outside)
    intro k
    cases k with
    | row => exact row.initial_cap .input
    | col => simpa [state, MacaulayRead.bank, OrdinalRead.bank] using row.initial_cap .input
    | result => exact Nat.zero_le _
    | aux k => cases k with
      | row | col => exact Nat.zero_le _
      | aux k => exact row.initial_cap (.aux k)
  have colRun : (cols.onPorts colPorts).BoundedRun S tc (state ri [] [] b) (state ri cj [] d) := by
    apply FiniteRoutine.BoundedRun.framed colInj col rowRun.final_cap (fun k => by cases k <;> rfl)
      (fun k => by cases k <;> rfl) (by outside)
  have entryRun : (entry.onPorts scalarPorts).BoundedRun S te (state ri cj [] d) (state ri cj val u) := by
    apply FiniteRoutine.BoundedRun.framed scalarInj read colRun.final_cap (fun k => by cases k <;> rfl)
      (fun k => by cases k <;> rfl) (by outside)
  have eraseRow := clear_bounded (MacaulayRead.Port.aux Work.row) (state ri cj val u) S entryRun.final_cap
  have er : Function.update (state ri cj val u) (.aux .row) [] = state [] cj val u := by
    funext k; cases k with | aux k => cases k <;> rfl | _ => rfl
  rw [er] at eraseRow
  have eraseCol := clear_bounded (MacaulayRead.Port.aux Work.col) (state [] cj val u) S eraseRow.final_cap
  have ec : Function.update (state [] cj val u) (.aux .col) [] = state [] [] val u := by
    funext k; cases k with | aux k => cases k <;> rfl | _ => rfl
  rw [ec] at eraseCol
  change (clear _).BoundedRun S (ri.length+1) _ _ at eraseRow
  change (clear _).BoundedRun S (cj.length+1) _ _ at eraseCol
  simp only [ri, cj, length_digits] at eraseRow eraseCol
  exact ⟨_, by omega, workBank [] [] u, ⟨u, hu, rfl⟩,
    (((rowRun.followedBy colRun).followedBy entryRun).followedBy eraseRow).followedBy eraseCol⟩

end RankQuery.Stack.Coordinate.Submatrix

end VPVNP
end Computability
end OAI
