import OAI.Computability.BorderVNP.LabelIndexAllocation
import OAI.Computability.BorderVNP.LabelIndexTrialRoom
import OAI.Computability.BorderVNP.CubeLabelISARealization

/-! # One fixed RAM program constructing the sparse directory and choosing all labels -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA VPVNP.BurstRAM

/-- The complete public label routine, including its own directory initialization. -/
def directoryProgram : Code := .seq program LabelTrial.program

/-- Initialization and choice use only deterministic team instructions. -/
theorem directoryProgram_deterministic : directoryProgram.deterministic = true := by decide

/-- Exact bound for initialization from the occupied source and destination arrays. -/
def initTicks (l : Layout) := 63+6*l.cells+40*l.cableCount+13*l.deliveryCount+4*l.labels^2+5*l.labels

/-- The constants in the initialization bound count actual row slots and both loop ends. -/
theorem initTicks_eq (l : Layout) : initTicks l = setup.slots + (Phase.clear.ticks l +
    (Phase.cable.ticks l + (Phase.delivery.ticks l + (Phase.cableBins.ticks l + Phase.dataBins.ticks l)))) := by
  change initTicks l = 53 + (l.cells*6+2+(l.cableCount*40+2+(l.deliveryCount*13+2+
    (l.labels*l.labels*4+2+(l.labels*5+2)))))
  unfold initTicks
  ring

/-- Clearing and construction take linear time in the cells, descriptors and mean bins. -/
theorem initTicks_le (l : Layout) :
    initTicks l ≤ 63*(l.cells+l.cableCount+l.deliveryCount+l.labels^2+1) := by
  have leq : l.labels ≤ l.labels^2 := Nat.le_self_pow (by decide) _
  unfold initTicks
  omega

/-- Per-cell incident lists extracted from the actual initial cable triples. -/
def directoryRows (l : Layout) (m : ℕ → ℕ) (c : ℕ) : List LabelTrial.Incident :=
  incidents (cableAt l m) c l.cableCount

/-- From the original frame, with arbitrary starting registers, the combined
native execution returns the chooser's full memory image and the winning label
word at every cell. Its tick count includes both initialization and all scans. -/
theorem directoryProgram_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (z : ℕ) (s : Bank w) (m : Memory w) :
    let before := readings m
    let l := layout (pub 0).val before
    let p := LabelTrial.Frame.decode (pub 0).val before
    let rows := directoryRows l before
    let initial := (image l before).mem
    let pref := p.prefix z rows initial
    (pub 0).val+56 < l.heads → (pub 0).val+56 < 2^w →
    Allocated l → Endpoints l before → Fits l w before → p.Fitted w z rows initial →
    ∃ tr t mt, Runs pub macros directoryProgram s m tr t mt ∧
      traceCost tr ≤ initTicks l + LabelTrial.assignmentTicks LabelTrial.setup.slots z l.cells
        (fun c => (rows c).length) ∧
      (t 1).val = l.cells ∧ readings mt = pref l.cells ∧
      ∀ c < l.cells, (mt (p.labels+c)).val = (p.winner z c (pref c) (rows c)).val := by
  intro before l p rows initial pref frame hf al ep fit chooser
  have hz : l.labels*l.labels < 2^w := by
    have count := chooser.count
    change l.labels^2+l.labels < 2^w at count
    rw [pow_two] at count
    omega
  obtain ⟨es,u,mu,build,bc,ready⟩ := program_runs pub macros s m hf hz (room_of_fits l before w al ep fit)
  have mem : readings mu = initial := ready.2.2.2
  have untouched := (image_view l before al ep).input
  have field (k : ℕ) (hk : k ≤ 56) : readings mu ((pub 0).val+k) = before ((pub 0).val+k) := by
    rw [mem]; exact untouched _ (by omega)
  have eq : LabelTrial.Frame.decode (pub 0).val (readings mu) = p := by
    dsimp only [p,LabelTrial.Frame.decode]
    simp only [field _ (by decide : 56 ≤ 56),field _ (by decide : 11 ≤ 56),
      field _ (by decide : 48 ≤ 56),field _ (by decide : 49 ≤ 56),field _ (by decide : 50 ≤ 56),
      field _ (by decide : 51 ≤ 56),field _ (by decide : 52 ≤ 56),field _ (by decide : 53 ≤ 56)]
  obtain ⟨fs,t,mt,choose,fc,endCell,table,win⟩ := LabelTrial.program_run pub macros z rows u mu hf
    (by rw [eq,mem]; exact chooser)
  rw [eq] at fc endCell table win
  rw [mem] at table win
  refine ⟨es++fs,t,mt,build.seq choose,?_,endCell,table,win⟩
  rw [initTicks_eq]
  exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add bc fc)

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
