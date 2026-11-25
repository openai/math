import OAI.Computability.BorderVNP.CellProfileAuxRow

/-! # Multiplicity-one validation of sparse public wiring records

Profiles allocate and discharge their flags locally. Every row is checked on
the original wire assignment, including zero pins, range equalities and the
presence of each privately referenced site box.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open scoped Classical

/-- One compact private guard for each kind of sparse public record. -/
def recordGuard (boxes : List (List Factor)) : Record → Stmt
  | .zero copies lanes p => zeroRow copies lanes p
  | .equal copies lanes p q => equalRow copies lanes p q
  | .profile copies s w hist routes => profileRow copies s w hist routes
  | .box id _ _ _ => (Term.lit (decide (id < boxes.length))).guard

/-- A sparse record contributes exactly its validity guard and restores all
data and sign slots before the following instruction stream. -/
theorem recordGuard_checks (boxes : List (List Factor)) (r : Record) (env : List ℕ) :
    Profile.Tests (recordGuard boxes r) env (fun bank => r.Valid boxes bank) := by
  cases r with
  | zero copies lanes p =>
    apply Prefix.checks_congr (zeroRow_correct copies lanes p env)
    intro bank
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact zero_checks_iff ..)
  | equal copies lanes p q =>
    apply Prefix.checks_congr (equalRow_correct copies lanes p q env)
    intro bank
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact equal_checks_iff ..)
  | profile copies s w hist routes => exact profileRow_checks copies s w hist routes env
  | box id base copies stride =>
    apply Prefix.checks_congr (term_checks (Term.lit (decide (id < boxes.length))) env)
    intro bank
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun h => decide_eq_true (of_decide_eq_true h : id < boxes.length),
      fun h => decide_eq_true (of_decide_eq_true h : (Record.box id base copies stride).Valid boxes bank)⟩

/-- The full descriptor stream for public record validity. -/
def Directory.recordGuards (D : Directory) := sequence (D.records.map (recordGuard D.boxes))

/-- Running all descriptor guards checks exactly the record clause in the
signed cell weight, preserving every subsequent continuation. -/
theorem Directory.recordGuards_checks (D : Directory) (env : List ℕ) :
    Profile.Tests D.recordGuards env (fun bank => ∀ r ∈ D.records, r.Valid D.boxes bank) := by
  apply Prefix.checks_congr (sequence_checks D.records (recordGuard D.boxes) env
    (fun r bank => decide (r.Valid D.boxes bank)) (fun r _ => recordGuard_checks D.boxes r env))
  intro bank
  exact Bool.eq_iff_iff.mpr (by simp)

end CellSparse

end BorderVNP
end Computability
end OAI
