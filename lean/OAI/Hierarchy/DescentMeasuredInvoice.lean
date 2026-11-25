import OAI.Hierarchy.DescentMeasuredRowProducer

namespace OAI
/-! # One fixed sparse-mixer workspace and clock expression for the native reset -/
namespace Hierarchy.DescentMeasuredHeader
open DescentGL ProtocolRAM DescentMeasuredMixer DescentNativeColumns DescentWeightColumnRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- The first mixer scratch address after the three column arrays, one guard
and the complete measured load rows. -/
def workBase (start H k Δ : ℕ) := origin start H k Δ+(H * (k + 1) + H * Δ)*2^k+1

/-- Exclusive high end of all weight, mask, score, row, and permutation cells. -/
def endAddress (start H k Δ : ℕ) :=
  workBase start H k Δ + (H * (k + 1) + H * Δ)*2^k + (k+1)*2^k + k*(3*2^k+1) + 2*2^k

theorem extent (start H k Δ : ℕ) :
    endAddress start H k Δ = start + (H * (k + 1) + H * Δ)*(3+2*2^k) + (k+1)*2^k+k*(3*2^k+1)+2*2^k+2 := by
  simp only [endAddress,workBase,origin]
  ring

theorem global_room (start H k Δ : ℕ) (room : endAddress start H k Δ<2^w) :
    PhysicalTrajectory.Room w k (mixerBase k (workBase start H k Δ) (H * (k + 1) + H * Δ))
      (DescentNativeColumns.address k (keyBase k (workBase start H k Δ) (H * (k + 1) + H * Δ))) := by
  constructor
  · intro j
    have step:=Nat.mul_le_mul_right (2^k) j.isLt
    rw [Nat.succ_mul] at step
    simp only [mixerBase,DescentNativeColumns.address]
    omega
  · simpa only [endAddress,mixerBase,keyBase,DescentNativeColumns.address,
      PhysicalTrajectory.outputBase,RowStageRAM.placed,Nat.mul_two,Nat.two_mul,Nat.add_assoc] using room

theorem source_segments (start H k Δ : ℕ) (room : endAddress start H k Δ<2^w) (i : Fin (H * (k + 1) + H * Δ)) :
    let tab:=mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ) i
    (Bank.mk tab.payload k).Fits w (workBase start H k Δ) ∧ tab.depth<workBase start H k Δ ∧
    tab.gain<workBase start H k Δ := by
  have row := Nat.mul_le_mul_right (2^k) i.isLt
  rw [Nat.succ_mul] at row
  have pos:=Nat.two_pow_pos k
  simp only [Bank.Fits,Bank.size,mixerTab,workBase,origin]
  unfold endAddress workBase origin at room
  have hi:=i.isLt
  omega

def loadClock (k p : ℕ) := 4+2^k*(2*(1+2^k*(15+5*2^k+p*(p+10)))+4)
def weightClock (k N p : ℕ) := 4+2^k*(2*(1+N*(24+p*(p+10)))+4)
def layoutClock (k : ℕ) := 4+2^k*16+k*(3200*(k+1)*2^(3*k))+DescentGLPermutationRAM.clock k

theorem measured_clock_bound {N : ℕ} (w k base p g : ℕ) (tab : Fin N → Header) :
    measuredTime w k base p g tab ≤
      8 + N * loadClock k p + (k+1) * weightClock k N g + layoutClock k := by
  let src (j : ℕ) := if h : j < N then (tab ⟨j,h⟩).payload else 0
  let bank := DescentNativeColumns.address k (keyBase k base N)
  let rows := DescentMeasuredMixer.row k base tab
  let sweep (binds : ℕ) := 4 + 2^k * (2*binds + 4)
  have sweep_le {x y : ℕ} (h : x ≤ y) : sweep x ≤ sweep y :=
    Nat.add_le_add_left (Nat.mul_le_mul_left (2^k)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 4)) 4
  let loadTime (j : ℕ) := sweep
    (DescentCorrelationRAM.term w k (src j) (DescentNativeColumns.address k base j) p).binds
  let weightTime (j : ℕ) := sweep (vector k w (bank j) j g rows).binds
  have loads : cost loadTime N ≤ 4 + N * loadClock k p :=
    DescentNativeColumns.prefix_cost (timer := loadTime) (N := N) (K := loadClock k p)
      (fun j _ => sweep_le (correlation_binds w k (src j) (DescentNativeColumns.address k base j) p))
  have weights : cost weightTime (k+1) ≤ 4 + (k+1) * weightClock k N g :=
    DescentNativeColumns.prefix_cost (timer := weightTime) (N := k+1) (K := weightClock k N g)
      (fun j _ => sweep_le (weight_binds k w (bank j) j g rows))
  have layout : PhysicalTrajectory.time k (mixerBase k base N) bank k +
      DescentGLPermutationRAM.clock k ≤ layoutClock k :=
    PhysicalTrajectory.total_clock k (mixerBase k base N) bank
  calc
    measuredTime w k base p g tab ≤
        (4 + N*loadClock k p) + (4 + (k+1)*weightClock k N g) + layoutClock k :=
      Nat.add_le_add (Nat.add_le_add loads weights) layout
    _ = _ := by omega

theorem mixer_cheap {N : ℕ} (w k base p g : ℕ) (tab : Fin N → Header) :
    CheapCode (stages w k base p g tab) := by
  let src (j : ℕ) := if h : j < N then (tab ⟨j,h⟩).payload else 0
  let bank := DescentNativeColumns.address k (keyBase k base N)
  let rows := DescentMeasuredMixer.row k base tab
  have loads : CheapCode (loadCode w k base p tab) :=
    DescentNativeColumns.prefix_cheap w k base
      (fun j => DescentCorrelationRAM.machine w k (src j) (DescentNativeColumns.address k base j) p) N
      (fun j _ => correlation_cheap w k (src j) (DescentNativeColumns.address k base j) p)
  have weights : CheapCode (weightCode w k base g tab) :=
    DescentNativeColumns.prefix_cheap w k (keyBase k base N)
      (fun j => pass k w (bank j) j g rows) (k+1)
      (fun j _ => weight_cheap w k (bank j) j g rows)
  exact @cheap_seq w ((loadCode w k base p tab).seq (weightCode w k base g tab))
    (PhysicalTrajectory.program w k (mixerBase k base N) bank)
    (@cheap_seq w (loadCode w k base p tab) (weightCode w k base g tab) loads weights)
    (PhysicalTrajectory.program_cheap w k (mixerBase k base N) bank)

theorem combined_clock (L : Tape) (_D : DataTape) (w start H k Δ p g : ℕ) :
    let base:=workBase start H k Δ
    let tab:=mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ)
    clocks L H k Δ+measuredTime w k base p g tab ≤24+780*(H * (k + 1) + H * Δ)+(H * (k + 1) + H * Δ)*2^k*100+
      (H * (k + 1) + H * Δ)*loadClock k p+(k+1)*weightClock k (H * (k + 1) + H * Δ) g+layoutClock k := by
  dsimp only
  have a:=clock_bound L H k Δ
  have b:=measured_clock_bound w k (workBase start H k Δ) p g
    (mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ))
  omega

/-- All dependence on the number of occupied host sites is linear. The
cube in the GL score search is incurred once by the common layout. -/
theorem site_clock (L : Tape) (D : DataTape) (w start H k Δ p g : ℕ) :
    let base:=workBase start H k Δ
    let tab:=mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ)
    clocks L H k Δ+measuredTime w k base p g tab ≤
      24+(k+1)*(4+6*2^k)+layoutClock k+
      H*(k+1+Δ)*(780+100*2^k+loadClock k p+(k+1)*2*2^k*(24+g*(g+10))) := by
  dsimp only
  apply (combined_clock L D w start H k Δ p g).trans
  unfold weightClock
  apply le_of_eq
  ring

end
end Hierarchy.DescentMeasuredHeader

end OAI
