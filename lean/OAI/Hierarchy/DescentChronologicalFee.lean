import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentHistoryPrivateLedger

namespace OAI
/-! # Private cable widths in the very archive supplying the physical scalar ordinals -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentKernelHistory DescentHistoryOrder
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {q ε u : ℝ} {S : AtomSchedule} {k i₀ z₀ D₀ i z D w hist p : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k i₀ z₀ D₀ w hist}
variable {source : Reached W G q ε S k i z D w hist}

section Ordinary
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' w hist}
variable (link : OrdinaryLink source he T c n target)

def ordinaryFee (_ : OrdinaryLink source he T c n target) : ℕ := scanFee he T c+mergeFee n
def ordinaryWidth (_ : OrdinaryLink source he T c n target) : ℕ := scanWidths he T c+mergeWidths n

private theorem ordinaryFee_le : ordinaryFee link≤ordinaryWidth link :=
  Nat.add_le_add (scanFee_le he T c) (mergeFee_le n)

private theorem advance_mass (a : Archive W) :
    privateMass (link.advance a).bit=privateMass a.bit+ordinaryFee link := by
  change privateMass (BitDescription.follow n (BitDescription.scanned he T a.bit c))=_
  rw [follow_mass,scanned_mass]
  exact Nat.add_assoc _ _ _

end Ordinary

private theorem resetArchive_mass {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset source ctl) (p : ℕ) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) :
    privateMass (resetArchive b p hp whole a).bit=privateMass a.bit+mergeFee b.reblock := by
  let split := BitDescription.granular W b.count (z*G.b) b.fit a.bit
  let key := DescentOrderedReset.grains W b.count b.order
  have fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole).symm
  let installed := split.batchedReset b.reset b.terminals key (b.reset.unit/p) p hp fit (resetMenu b)
  have bank : privateMass installed=privateMass split :=
    reset_mass split b.reset b.terminals key (b.reset.unit/p) p hp fit (resetMenu b)
  exact (follow_mass b.reblock installed).trans (congrArg (fun x : ℕ => x+mergeFee b.reblock)
    (bank.trans (granular_mass W b.count (z*G.b) b.fit a.bit)))

/-- Count each actual internalization along the very path carrying the dense node order. -/
def Path.privateCharge (path : Path start source) : ℕ := by
  induction path with
  | here => exact 0
  | ordinary prev ticket ih => exact ih+ordinaryFee ticket
  | reset prev b ih => exact ih+mergeFee b.reblock

/-- Charge the entire source cable width at each physical contraction on that path. -/
def Path.widthCharge (path : Path start source) : ℕ := by
  induction path with
  | here => exact 0
  | ordinary prev ticket ih => exact ih+ordinaryWidth ticket
  | reset prev b ih => exact ih+mergeWidths b.reblock

theorem Path.privateCharge_le (path : Path start source) : path.privateCharge≤path.widthCharge := by
  induction path with
  | here=>exact Nat.le_refl 0
  | ordinary prev ticket ih=>exact Nat.add_le_add ih (ordinaryFee_le ticket)
  | reset prev b ih=>exact Nat.add_le_add ih (mergeFee_le b.reblock)

/-- The archive stores this bit recipe together with its immutable node-index equivalence. -/
theorem Path.archive_mass (p : ℕ) (hp : 0<p) (a : Archive W₀) (path : Path start source) (whole : path.whole p) :
    privateMass (path.archive p hp a whole).bit=privateMass a.bit+path.privateCharge := by
  induction path with
  | here=>exact (Nat.add_zero _).symm
  | ordinary prev ticket ih=>
    calc
      _ = privateMass (prev.archive p hp a whole).bit+ordinaryFee ticket := advance_mass ticket _
      _ = _ := by rw [ih whole]; exact Nat.add_assoc _ _ _
  | reset prev b ih=>
    calc
      _ = privateMass (prev.archive p hp a whole.1).bit+mergeFee b.reblock := resetArchive_mass b p hp whole.2 _
      _ = _ := by rw [ih whole.1]; exact Nat.add_assoc _ _ _

section Append
variable {W₂ : MarkedWorld F d P bits} {i₂ z₂ D₂ : ℕ}
variable {last : Reached W₂ G q ε S k i₂ z₂ D₂ w hist}
theorem Path.privateCharge_append (x : Path start source) (y : Path source last) :
    (x.append y).privateCharge=x.privateCharge+y.privateCharge := by
  induction y with
  | here=>exact (Nat.add_zero _).symm
  | ordinary prev ticket ih =>
    exact (congrArg (fun n => n+ordinaryFee ticket) ih).trans (Nat.add_assoc _ _ _)
  | reset prev b ih =>
    exact (congrArg (fun n => n+mergeFee b.reblock) ih).trans (Nat.add_assoc _ _ _)

theorem Path.widthCharge_append (x : Path start source) (y : Path source last) :
    (x.append y).widthCharge=x.widthCharge+y.widthCharge := by
  induction y with
  | here=>exact (Nat.add_zero _).symm
  | ordinary prev ticket ih =>
    exact (congrArg (fun n => n+ordinaryWidth ticket) ih).trans (Nat.add_assoc _ _ _)
  | reset prev b ih =>
    exact (congrArg (fun n => n+mergeWidths b.reblock) ih).trans (Nat.add_assoc _ _ _)
end Append


end
end Hierarchy.DescentSixParty.Chronology

end OAI
