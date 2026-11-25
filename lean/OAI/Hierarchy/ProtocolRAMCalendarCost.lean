import OAI.Hierarchy.ProtocolRAMCalendarFrozen
import OAI.Hierarchy.ProtocolRAMPurchaseMarketCost

namespace OAI
/-! # Separating row extents from the text of the actual native adaptive controller -/

namespace Hierarchy.ProtocolRAM.Calendar
open PurchaseStage PurchaseFrozen
open scoped BigOperators
variable {q d : ℕ}

/-- Scale of one scan when its actual number of rows is at most a constant
multiple of the number n of input records. This never multiplies by literal stock values. -/
def passFactor (rows : ℕ) (p : Pass) := 4+rows*(2*p.term.work+4)

theorem pass_bill {n rows : ℕ} (positive : 0<n) (p : Pass) (extent : p.rows≤n*rows) :
    p.clock≤n*passFactor rows p := by
  unfold Pass.clock passFactor
  have data := Nat.mul_le_mul_right (2*p.term.work+4) extent
  have base : 4≤n*4 := by nlinarith
  simpa only [Nat.mul_add,Nat.mul_assoc] using Nat.add_le_add base data

def checkFactor (rows : ℕ) (z : AttemptGate.Check) := 4+(rows+1)*(42+2*z.term.work)

theorem check_bill {n rows : ℕ} (positive : 0<n) (z : AttemptGate.Check) (extent : z.rows≤n*rows) :
    z.ticks≤n*checkFactor rows z := by
  have line : z.rows+1≤n*(rows+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
  have scan := Nat.mul_le_mul_right (42+2*z.term.work) line
  have base : 4≤n*4 := by nlinarith
  calc
    z.ticks ≤ n*4 + (n*(rows+1))*(42+2*z.term.work) := Nat.add_le_add base scan
    _ = n*checkFactor rows z := by unfold checkFactor; ring

theorem columns_bill {n rows : ℕ} (positive : 0<n) (ps : List Pass) (extent : ∀p∈ps,p.rows≤n*rows) :
    clock ps≤n*(4+(ps.map (passFactor rows)).sum) := by
  induction ps with
  | nil => simp [clock]; nlinarith
  | cons p ps ih =>
    have h := Nat.add_le_add (pass_bill positive p (extent p (by simp)))
      (ih (fun v hv=>extent v (by simp [hv])))
    simp only [clock,List.map_cons,List.sum_cons,Nat.mul_add]
    rw [Nat.mul_add] at h
    omega

theorem audit_columns (ps : List Pass) : auditTicks (columns ps)=clock ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change p.clock+auditTicks (columns ps)=p.clock+clock ps
    rw [ih]

/-- All native record fields, histograms and prices are scanned once per selected-format
column; the admission histogram is the one linear two-bin count. -/
def postFactor (B : Repair q d) (L : Dispatch) (rows : ℕ) :=
  checkFactor rows B.tests.excess+checkFactor rows B.tests.payload+checkFactor rows B.tests.discrepancy+
  (4+rows*(2*(repairMask B).work+4))+
  (4+rows*(2*(invalidExpr (enabledBatch L B)).work+4))+
  (7+6*2+11*rows)+
  (4+((writes L B).map (passFactor rows)).sum)+
  (4+1*(2*(verdict (audits L B)).work+4))

theorem post_bill (B : Repair q d) (L : Dispatch) (n rows : ℕ) (positive : 0<n)
    (ext : L.candidates≤n*rows) (excess : B.tests.excess.rows≤n*rows)
    (payload : B.tests.payload.rows≤n*rows) (disc : B.tests.discrepancy.rows≤n*rows)
    (written : ∀p∈writes L B,p.rows≤n*rows) :
    postTicks L B≤n*postFactor B L rows := by
  have x := check_bill positive _ excess
  have y := check_bill positive _ payload
  have z := check_bill positive _ disc
  have r := pass_bill positive (⟨B.repairBits.base,L.candidates,repairMask B⟩:Pass) ext
  have h := pass_bill positive (⟨B.keys,L.candidates,invalidExpr (enabledBatch L B)⟩:Pass) ext
  have cols := columns_bill positive (writes L B) written
  have tally : 7+6*2+11*L.candidates≤n*(7+6*2+11*rows) := by
    have mult := Nat.mul_le_mul_left 11 ext
    rw [show 11*(n*rows)=n*(11*rows) by ring] at mult
    rw [Nat.mul_add]
    nlinarith
  have tail := Nat.le_mul_of_pos_left (4+1*(2*(verdict (audits L B)).work+4)) positive
  simp only [postTicks,AttemptGate.TestBoard.ticks,postFactor,Nat.mul_add,audits,auditTicks,Audit.ticks,
    inspection,audit_columns,Pass.clock,passFactor] at *
  omega

end Hierarchy.ProtocolRAM.Calendar

end OAI
