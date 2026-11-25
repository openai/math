import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
import OAI.Computability.BorderVNP.CellTeamOccurrenceClock

/-! # The clock of an arbitrary native report choice

The report input is measured before its private choices. Its count fields
occupy the public geometry array, its original sidecar descriptions are
delivered by the real incoming bits, and each expanded occurrence uses a
distinct original power slot. These same quantities charge every returning
choice of count and use bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM DiagonalTallyCellReports BorderVNP.Cube.TeamRowClock
open private tapeOriginal from OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
open private tape_map from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

private theorem bundleTicks_tape (l : ReportLayout) (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle)
    (q : LocalReportCursor) : bundleTicks l (tapeBundles a p bs) q=bundleTicks l bs q := by
  induction bs generalizing p q with
  | nil => rfl
  | cons b bs ih =>
    change 1+b.cost l q+bundleTicks l (tapeBundles a (p+b.useCount) bs) (q.advance b)=_
    rw [ih]
    rfl

private theorem bundleCursor_tape (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle) (q : ReportCursor) :
    (tapeBundles a p bs).foldl ReportCursor.afterBundle q=bs.foldl ReportCursor.afterBundle q := by
  induction bs generalizing p q with
  | nil => rfl
  | cons b bs ih => exact ih (p+b.useCount) (q.afterBundle b)

/-- Changing only the count and use bits leaves each native report loop's
instruction allowance unchanged, including its cursor for the next cell. -/
theorem cellTicks_tape {l : ReportLayout} (a : ℕ → Bool) (p : ℕ) (cs : List (ReportCell l)) (q : ReportCursor) :
    cellTicks (tapeCells a p cs) q=cellTicks cs q := by
  induction cs generalizing p q with
  | nil => rfl
  | cons c cs ih =>
    have after : (c.withTape a p).after q=c.after q := bundleCursor_tape ..
    have work : (c.withTape a p).work q=c.work q := by
      unfold ReportCell.work ReportCell.prefixCost
      simp only [ReportCell.bits_length,ReportCell.withTape_tailWidth]
      change _+(c.countFrame q).cost .count+bundleTicks l (tapeBundles a (p+l.gadgets*l.countWidth) c.bundles)
        (c.localStart q)+_+_ = _
      rw [bundleTicks_tape]
    simp only [tapeCells,cellTicks,work,after,ih]

/-- Every actual native report return fits the original report array's
instruction count, independent of the values read from its private tape. -/
theorem report_return_original {w description : ℕ} {l : ReportLayout} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s m} {cs : List (ReportCell l)} {q : ReportCursor}
    (seed : PreparedReportInput pub m cs q description) (x : Returns prepareCellReports pub mac s m) :
    traceCost x.val.1 ≤ prepareSetup.slots+cellTicks cs q+(writeFrame 32 60 61 35).slots := by
  let tape := (reportReturnEquiv seed mac s).symm x
  have bound := (reportReturnEquiv_spec seed mac s tape).2.1
  simpa only [tape,Equiv.apply_symm_apply,cellsOfTape,cellTicks_tape] using bound

/-- Charge the actual returning trace by the disjoint source description
bits, the true report-field capacities, and the individually indexed
original weighted uses. These source bounds hold before its tape is chosen. -/
theorem report_return_charge {A : Type} [Fintype A] {w C count p R H B X description : ℕ}
    {l : ReportLayout} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m}
    (owner : Fin C → ℕ) (team : ℕ) (order : Fin count ≃ {c : Fin C // owner c=team})
    (r : Fin C → ReportCell l) (recv : A → Fin C) (incoming : A → ℕ)
    (load : assignedSum (owner ∘ recv) team incoming ≤ X)
    (bundles : BitDelivery (fun j : (c : Fin C) × Fin (r c).bundles.length => j.1) (fun _ => description) recv incoming)
    (original : ((c : {c : Fin C // owner c=team}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B)
    (publicCounts : count*(l.gadgets+l.gadgets*l.countWidth) ≤ 2^p) (positive : 1 ≤ description)
    (q : ReportCursor) :
    let cs := List.ofFn (fun i => r (order i).val)
    PreparedReportInput pub m cs q description → ∀ x : Returns prepareCellReports pub mac s m,
    traceCost x.val.1 ≤ 54+79*count+105*2^p+516*X+131*(R*(H*B)) := by
  intro cs seed x
  let a : ℕ → Bool := fun _ => false
  have sized := original_team_le (tapeCells a 0 cs) q l.headers (readings m) (seed.inputs a)
  simp only [teamOriginal,tape_map a (fun c => originalFields c.bundles) (fun _ _ => tapeOriginal ..) cs 0,
    tape_map a (fun c => c.bundles.length) (fun _ _ => tapeBundles_length ..) cs 0] at sized
  change teamOriginal cs*(l.fieldWidth+1) ≤ 2*(description+1)*(cs.map (fun c => c.bundles.length)).sum at sized
  have del := (bundles.ordinal_load (fun c => (r c).bundles.length) description owner team).trans load
  have reindex := report_sum owner team order r (fun c => c.bundles.length)
  change (cs.map (fun c => c.bundles.length)).sum=assignedSum owner team (fun c => (r c).bundles.length) at reindex
  rw [←reindex] at del
  have one := Nat.le_mul_of_pos_left (cs.map (fun c => c.bundles.length)).sum positive
  rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul] at sized
  have originals : teamOriginal cs*(l.fieldWidth+1) ≤ 4*X := by omega
  have corr := report_sum owner team order r (fun c => weightedCopies c.bundles)
  change teamWeighted cs=_ at corr
  have powers := corr.trans_le (owned_use_le owner team (fun c => (r c).bundles) original)
  have seen := reportReturnEquiv_clock seed mac s ((reportReturnEquiv seed mac s).symm x)
  simp only [Equiv.apply_symm_apply,show cs.length=count from List.length_ofFn] at seen
  have digits : (105*l.gadgets+16*(l.gadgets*l.countWidth))*count ≤ 105*2^p := by
    apply le_trans _ (Nat.mul_le_mul_left 105 publicCounts)
    calc
      _ ≤ (105*(l.gadgets+l.gadgets*l.countWidth))*count := Nat.mul_le_mul_right count (by omega)
      _ = _ := by ring
  nlinarith only [seen,originals,powers,digits]

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
