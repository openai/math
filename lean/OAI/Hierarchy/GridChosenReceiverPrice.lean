import OAI.Hierarchy.GridReceiverPrefixClock
import OAI.Hierarchy.GridReceiverLayoutScale
import OAI.Hierarchy.GridPinReceiverPrefix
import OAI.Hierarchy.TraceReceiverPreparation
import OAI.Hierarchy.TraceReceiverOwnerMount
import OAI.Hierarchy.TraceReceiverMaskLoop

namespace OAI
/-! # Startup cost of the receiving grid's complete native trace setup -/

namespace Hierarchy.GridReceiverClock
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open GridScale Filter

/-- Every term is the cost of an actual native phase. The final contribution
reserves the linear chronological cursor traversal and constant task headers. -/
def scans (w nlib nverifier lane low dict mask first roots : ℕ) (P : GridPinPublisher.Plan) :=
  (nlib*(5*(64*w)+6)+6)+(nverifier*(5*(64*w)+6)+6)+
  TraceReceiverMaskLoop.work (64*w) lane low dict mask+P.intervalCost+
  TraceReceiverOwnerMount.ticks first roots+24*(first+roots)+4096+TraceReceiverTasks.before_clock 0

theorem scans_le {w nlib nverifier lane low dict mask first roots pin cut dim C : ℕ}
    (P : GridPinPublisher.Plan) (nonempty : 0<pin)
    (mounted : nlib+nverifier≤C*(w+1)^14) (depth : lane+low≤64*w)
    (top : first+roots≤cut) (ticks : P.ticks≤cut)
    (slots : P.factors=(20*(w+1)+2)^dim*roots) (lanes : P.lanes≤cut) :
    scans w nlib nverifier lane low dict mask first roots P ≤
      (100000+TraceReceiverTasks.before_clock 0+1000*C+35*22^dim)*(w+1)^(max 15 dim)*(cut+pin) := by
  let z:=(w+1)^(max 15 dim)
  let vol:=cut+pin
  have pos : 0<vol := by dsimp only [vol];omega
  have l : w+1≤z := by
    simpa only [z,pow_one] using Nat.pow_le_pow_right (Nat.succ_pos w)
      (show 1 ≤ max 15 dim from (by omega : 1≤15).trans (le_max_left 15 dim))
  have zpos : 0<z := Nat.pow_pos (Nat.succ_pos _)
  have dscale : (20*(w+1)+2)^dim≤22^dim*z := by
    have h:=Nat.pow_le_pow_left (show 20*(w+1)+2≤22*(w+1) by omega) dim
    rw [mul_pow] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos w) (le_max_right 15 dim)))
  have cz : cut≤z*vol := by
    have := Nat.mul_le_mul_right vol (show 1≤z by omega)
    dsimp only [vol] at *
    omega
  have zz : z≤z*vol := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left z pos
  have rootsBound : roots≤vol := by dsimp only [vol];omega
  have fs := Nat.mul_le_mul dscale rootsBound
  rw [←slots] at fs
  have wordRate : 5*(64*w)+6≤326*(w+1) := by omega
  have table := Nat.mul_le_mul mounted wordRate
  have pack : (nlib+nverifier)*(5*(64*w)+6)≤326*C*z := calc
    _ ≤ C*(w+1)^14*(326*(w+1)) := table
    _ = 326*C*(w+1)^15 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos w) (le_max_left 15 dim))
  have funded := pack.trans (Nat.mul_le_mul_left (326*C) zz)
  rw [Nat.add_mul] at funded
  unfold scans
  rw [TraceReceiverMaskLoop.linear_work,P.interval_cost_eq]
  unfold TraceReceiverMaskBanks.count TraceReceiverOwnerMount.ticks
  change _ ≤ (100000+TraceReceiverTasks.before_clock 0+1000*C+35*22^dim)*z*vol
  rw [Nat.mul_assoc] at fs
  rw [show (100000+TraceReceiverTasks.before_clock 0+1000*C+35*22^dim)*z*vol=
      100000*(z*vol)+TraceReceiverTasks.before_clock 0*(z*vol)+1000*C*z*vol+35*22^dim*z*vol by ring]
  have keep : 326*C*(z*vol) ≤ 1000*C*z*vol := by
    simpa only [Nat.mul_assoc] using
      (Nat.mul_le_mul_right (C*(z*vol)) (by decide : 326≤1000))
  have init : TraceReceiverTasks.before_clock 0 ≤ TraceReceiverTasks.before_clock 0*(z*vol) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (TraceReceiverTasks.before_clock 0)
      (Nat.mul_pos zpos pos)
  have countWords : w+1≤z*vol := l.trans zz
  have countCost : 35*P.factors≤35*22^dim*z*vol := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 35 fs
  omega

/-- Any fixed reserve pays both traversals of S17, the native independent
interval prefix, static masks and the real positive kernel library. -/
theorem setup_clock {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss)
    (k A dim C reserve : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ q,0<q → q≤Q w →
      let pin:=pins w (overhead Q loss w)
      let cut:=2^(3*w/5)
      ∀ (a : Archive) (ss : List Stage) (N edges first nlib nverifier lane low dict mask : ℕ)
        (P : GridPinPublisher.Plan),first+N≤cut → edges≤cut → a.pairCapacity≤pin →
        nlib+nverifier≤C*(w+1)^14 → lane+low≤64*w →
        P.ticks≤cut → P.factors=(20*(w+1)+2)^dim*N → P.lanes≤cut →
        reserve*(2*startupTime w pin cut N dim a ss edges+scans w nlib nverifier lane low dict mask first N P)
          ≤UniversalTick.clock w UniversalTick.saving := by
  let R:=100000+TraceReceiverTasks.before_clock 0+1000*C+35*22^dim
  filter_upwards [eventual_with_scans env k A dim R (max 15 dim) (2*reserve)] with w bound
  intro q live qle pin cut a ss N edges first libN verifier lane low dict mask P count edgesFit bits mounted depth
    ticks factors lanes
  have extra:=scans_le (pin:=pin) (dict:=dict) (mask:=mask) P (Nat.two_pow_pos _) mounted depth
    count ticks factors lanes
  have clock:=bound q live qle a ss N edges _ (by omega) edgesFit bits extra
  have cheaper : reserve*(2*startupTime w pin cut N dim a ss edges+
      scans w libN verifier lane low dict mask first N P) ≤
      (2*reserve)*(startupTime w pin cut N dim a ss edges+scans w libN verifier lane low dict mask first N P) := by
    ring_nf
    omega
  exact cheaper.trans clock

end Hierarchy.GridReceiverClock

end OAI
