import OAI.Computability.BorderVNP.CellGadgetRows
import OAI.Computability.BorderVNP.CellSparseSignedResult

/-! # Compiling a sparse private cell validator

The generated program guesses the private wire bank once. It checks each copy
of each site box, validates the advertised subtotals in binary, and returns
the signed sum of the passing assignments. Temporary one-hot banks contribute
exactly one extension of each passing assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro
open scoped Classical

/-- Both conditions on the list of advertised gadget counts. -/
def Directory.countGuards (D : Directory) : Stmt := .seq D.rangeGuard D.subtotalGuards

/-- The combined count check rejects unrecognized identifiers and verifies every announced subtotal. -/
theorem Directory.countGuards_checks (D : Directory) (e : List ℕ) :
    Profile.Tests D.countGuards e (fun b =>
      D.occurrences.all (selectedInRange D.reportedCounts.length b) = true ∧
        ∀ id : Fin D.reportedCounts.length, D.occurrences.countP (selected id.val b) = word b D.reportedCounts[id]) := by
  apply Prefix.checks_congr (Prefix.seq_checks (D.rangeGuard_checks e) (D.subtotalGuards_checks e))
  intro b
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, selectedInRange]

/-- Check an assignment to the cell's private and external wires. -/
def Directory.checkAssignment (D : Directory) : Stmt :=
  .seq D.recordGuards (.seq (sweep (factorBody 0) D.blocks 0) D.countGuards)

/-- For an arbitrary physical wire assignment and incoming sign and guard, the
compiled sparse checker evaluates to the exact signed weight of the cell. -/
theorem Directory.value_checkAssignment (D : Directory) (e : List ℕ) (f : Flags) (v : List Bool) :
    value (D.checkAssignment.expand e) f v = TeamTape.haltWeight f.ok f.minus * D.weight (lookup v) := by
  let wires := @decide (∀ r ∈ D.records, r.Valid D.boxes (lookup v)) (Classical.propDecidable _)
  let counts := @decide (D.occurrences.all (selectedInRange D.reportedCounts.length (lookup v)) = true ∧
    ∀ id : Fin D.reportedCounts.length,
      D.occurrences.countP (selected id.val (lookup v)) = word (lookup v) D.reportedCounts[id]) (Classical.propDecidable _)
  let g := D.factorFlags (lookup v) ⟨f.ok && wires, f.minus⟩
  have hdata : Profile.data 0 (lookup v) = lookup v := funext fun i => by simp [Profile.data]
  calc
    value (D.checkAssignment.expand e) f v =
        value ((sweep (factorBody 0) D.blocks 0).expand e ++ D.countGuards.expand e)
          ⟨f.ok && wires, f.minus⟩ v := by
      simpa only [checkAssignment, Stmt.expand, wires] using D.recordGuards_checks e
        ((sweep (factorBody 0) D.blocks 0).expand e ++ D.countGuards.expand e) f v
    _ = value (D.countGuards.expand e) g v := by
      simpa only [hdata, g, factorFlags] using factor_sweep D 0 e (D.countGuards.expand e) ⟨f.ok && wires,f.minus⟩ v
    _ = TeamTape.haltWeight (g.ok && counts) g.minus := by
      simpa only [List.append_nil, value, counts] using D.countGuards_checks e [] g v
    _ = TeamTape.haltWeight f.ok f.minus * D.weight (lookup v) :=
      D.weight_eq_signedGuards (lookup v) f wires counts (by simp [wires]) (by simp [counts])

/-- The sole private-wire guessing block followed by the complete sparse validator. -/
def Directory.program (D : Directory) (privateWires : ℕ) : Stmt :=
  .seq (.loop (.lit privateWires) (.fixed .guess)) D.checkAssignment

/-- Complete signed cell multiplicity, including every private wire exactly once. -/
theorem Directory.value_program (D : Directory) (privateWires : ℕ) (e : List ℕ) (external : List Bool) :
    value ((D.program privateWires).expand e) ⟨true,false⟩ external =
      ∑ x : Fin privateWires → Bool, D.weight (lookup (List.ofFn x ++ external)) := by
  have h : ((D.program privateWires).expand e) =
      List.replicate privateWires .guess ++ D.checkAssignment.expand e := by
    simp [program, Stmt.expand, NatExpr.eval, List.flatMap_def, List.map_const']
  rw [h, value_guessBlock]
  apply Finset.sum_congr rfl
  intro x _
  simp [D.value_checkAssignment, TeamTape.haltWeight]

/-- The finite stack instruction interpreter gives the same signed count when
supplied with the privately expanded stream and its verified execution budget. -/
theorem Directory.execute_program (D : Directory) (privateWires : ℕ) (external : List Bool) (t : ℕ)
    (h : budget ((D.program privateWires).expand []) ≤ t) :
    let ops := (D.program privateWires).expand []
    let start := ((⟨true,false⟩ : Flags), (.fetch : CellMacro.Phase))
    let input := bank (stream ops) external []
    VPVNP.RAMTape.StopsWithin code t start input ∧
      TeamStack.paths code negative t start input =
        ∑ x : Fin privateWires → Bool, D.weight (lookup (List.ofFn x ++ external)) := by
  obtain ⟨hs,hv⟩ := execute ((D.program privateWires).expand []) ⟨true,false⟩ external t h
  exact ⟨hs,hv.trans (D.value_program privateWires [] external)⟩

end CellSparse

end BorderVNP
end Computability
end OAI
