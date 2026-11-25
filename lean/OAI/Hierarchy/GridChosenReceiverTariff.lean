import OAI.Hierarchy.GridChosenReceiverStartup
import OAI.Hierarchy.TraceReceiverFullRate
import OAI.ThreeFlat.Diagonal.PhysicalVisitRates
import OAI.ThreeFlat.RAM.TickTerminalRootPrice

namespace OAI
/-! # One charged native tariff and one common field-evaluation board -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution GridScale GridInstalledEvaluator TraceFactorReceiver Filter
open scoped BigOperators

def degree {F : Type} [Field F] (B : Block F) := 2*(2^B.exponent 0)
def stageRate {F : Type} [Field F] [Fintype F] (B : Block F) :=
  Gather.fullRate B.stageClockRate 0
def rootRate := TickTerminalRoot.rootFactor
def reserve : ℕ := 2^20

/-- Both the physical S44 traversal and the root stream transactions can
each be charged at the full root tariff. The terminal board still has the
requested capacities and the initial hardware has separate time. -/
theorem slot_clock {F : Type} [Field F] [Fintype F] {p n clock setup inside : ℕ}
    {arity : Fin n→ℕ} (nets : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→Fin p)
    (price : Fin n→ℕ) (sizes : ∀ i,10000*((nets i).cells+(nets i).internal)≤price i)
    (slot : reserve*(∑ i,price i)≤clock)
    (startRoom : 4*setup≤clock) (field : 4*fieldCost F≤clock)
    (spent : inside≤ setup+65536*(∑ i,price i)) :
    let N:=forest nets wire
    let H:=clock/40000
    let J:=2*H
    let pad:=H-N.internal
    let fill:=J-(N.cells+pad)
    N.internal≤H ∧ N.cells+pad≤J ∧
      inside+TickTerminalPadding.budget F pad fill+evalCost F H J≤clock := by
  intro N H J pad fill
  change 1048576*(∑ i,price i)≤clock at slot
  have budget : (∑ i,price i)≤clock/4 := by omega
  obtain ⟨hidden,rows⟩:=forest_fits (m:=clock) nets wire price sizes budget
  exact ⟨hidden,rows,clock_fits (bits:=N.internal) (cells:=N.cells) field (by omega)⟩

/-- This is the root list in the real S17 class-major order. The indexed
charges needed by the heterogeneous forest are exactly the published bill. -/
theorem slot_bill {F : Type} [Field F] [Fintype F] {B : Block F} {m A w : ℕ}
    {Q : ℕ→ℕ} {loss : ℕ→ℝ} {v : TickSelection F (m+1) A w Q loss}
    (I : Installed B m A w (degree B) (stageRate B) rootRate v)
    (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
    (recv : Machine (64*w) (GridDescription.capacity w) (GridDescription.capacity w) (GridDescription.capacity w))
    (z : I.D.trace)
    (t : GridThrough.Cell (m+1) (side (overhead Q loss w)-1) × Fin v.copies) :
    let D:=I.D
    let l:=layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
    let unit:=D.issuedUnit w (degree B) (stageRate B) rootRate
    let cost:=D.costs (GridNativeImage.resources D l) z.1 m l.sideMinusOne l.bank D.issuedCharges unit
    let group:=FactorAllocation.factors w cost (List.ofFn id) (GridTicks.index (k:=m+1) (g:=l.sideMinusOne+1) (q:=v.copies) t)
    reserve*(∑ i : Fin group.length,D.work z.1 D.issuedCharges unit group[i])≤
      UniversalTick.clock w UniversalTick.saving := by
  intro D l unit cost group
  have bounds:=(R.rooms recv 0 (26*GridDescription.sector w)).choose_spec (fun _=>false) z
  have actual:=bounds.2 t
  simp only [pow_zero,Nat.mul_one] at actual
  have mapSum : (group.map (fun i => D.work z.1 D.issuedCharges unit i)).sum=
      ∑ i : Fin group.length,D.work z.1 D.issuedCharges unit group[i] := by
    calc _ = (List.ofFn (fun i : Fin group.length => D.work z.1 D.issuedCharges unit group[i])).sum := by
              exact congrArg List.sum (List.ofFn_getElem_eq_map group _).symm
         _ = _ := Fin.sum_ofFn _
  rw [←mapSum]
  with_unfolding_all
    simpa only [group,cost,unit,l,D,List.ofFn_id] using actual

/-- The constant-field program gets its time from the same true sender
trajectory, regardless of which approved selector supplied the root list. -/
theorem field_clock {F : Type} [Field F] [Fintype F] (B : Block F) (m A : ℕ)
    {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss) (q : ℕ→ℕ)
    (valid : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ v : TickSelection F (m+1) A w Q loss,v.copies=q w →
      ∀ I : Installed B m A w (degree B) (stageRate B) rootRate v,
        let l:=layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
        4*setupTime I.D l≤UniversalTick.clock w UniversalTick.saving ∧
        4*fieldCost F≤UniversalTick.clock w UniversalTick.saving := by
  let margin:=4+4*fieldCost F
  filter_upwards [eventual_setup B m A (degree B) (stageRate B) rootRate margin env q valid] with w all
  intro v same I l
  have total:=all v same I
  let setup:=setupTime I.D l
  change margin*setup≤_ at total
  have pos : 0< setup := by
    dsimp only [setup,setupTime,GridReceiverClock.scans]
    omega
  have pay := Nat.mul_le_mul_left margin pos
  have left := Nat.mul_le_mul_right setup (show 4 ≤ margin by dsimp [margin];omega)
  simp only [Nat.mul_one] at pay
  exact ⟨left.trans total,by dsimp only [margin] at pay total;omega⟩

end Hierarchy.GridChosenReceiver
end

end OAI
