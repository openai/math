import OAI.Computability.VPVNP.CompressorShrinkHeaderVisitWalk
import OAI.Computability.VPVNP.CompressorShrinkGreedyPlannerSupport
import OAI.Computability.VPVNP.CompressorGreedyPacketWalk
import OAI.Computability.VPVNP.CompressorGreedyPacketFootprints
import OAI.Computability.VPVNP.CompressorShrinkGreedyHeaderValues
import OAI.Computability.VPVNP.CompressorRecordsShrinkInput

/-! # Online source packets for the shrinking header and greedy assignment

The global calendar first relabels the old level, publishes the next header
and its pointers, then executes the six greedy kernels. All nine visits use
their computed operands and actual source traces. The post-memory is the
typed greedy result used by the subsequent placement and rank scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHeaderGreedyPackets

open BurstRAM Compression BlockPlanner DescriptorSpace BlockHeaderRun SourceTransport
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g : ℕ}
  (X : GreedyArena.ShrinkingState (ShrinkBlockInputs.a i) g)
  (sel : SelectedScore.Selection B X) (tape : List Bool)
local notation "v" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "script₀" => BlockProgram.script B
variable {w : ℕ} (base : Word w) (positions blocks t : ℕ)
local notation "L" => BlockProgram.layout B (Fin.val base) positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog script₀)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first₀" => BlockPlanner.Script.levelsPerBlock script₀*t
local notation "st" => (levelStart L first₀ : Word w)
local notation "H" => levelStart L 0
local notation "W" => window B i

/-- Common private-fuel bound for a single header or greedy worker call in this shrinking
substep. -/
def fuelBound := max (headerClock B i) (GreedyVisit.maxFuel (ShrinkBlockInputs.a i))

/-- A single clock suffices for all inputs and all block repetitions. Its
finite sum is over the actual nine catalog positions of this substep. -/
def clock :=
  (((W).indices).map (fun j => ((script₀).plan.recipes j).2.code.length+1+2*Schedule.Online.N (script₀).size (script₀).size+5 +
    (fuelBound B i+3+4*(((script₀).catalog j).params+1)+2*Schedule.Online.N (script₀).size (script₀).size+5))).sum

theorem group (old new : Fin (L).levels) (hOld : first₀+i.val=old.val) (hNew : old.val+1=new.val)
    (m : Memory w) (sub : Substep v L old new (by change 6 ≤ 54; decide) m)
    (T : IncidenceDirectory w)
    (r : GreedyArena.Run X T (tableBase L old (0 : Fin 6)) (finalMemory v L old new m))
    (heads : ∀ c : Fin 6, m (incidenceHead L old c)=T.column c)
    (scratch : m (tableHead L old (0 : Fin 6))=(tableBase L old (0 : Fin 6) : Word w))
    (low : ∀ c, H ≤ (T.column c).val)
    (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val=(directoryRows L : Word w)) (pitch : m ((pt).directory-1).val=(levelWords L : Word w))
    (ht : t < blocks) (cap : ℕ) (hc : clock B i ≤ cap) :
    ∃ ps : List (SourceOnline.Packet script₀ w),
      SourceOnline.Group script₀ L base cap ((script₀).initial.length+t*(script₀).block.length+(BlockIndex.earlier B i).length)
        (directoryRows L) m ps ∧ ps.map (fun p => p.stage.phase)=(W).indices ∧
      ps.flatMap SourceWalk.Packet.reports=reports v L old new m++r.reports ∧
      SourceOnline.post m ps=r.post := by
  let origin := tableBase L old (0 : Fin 6)
  let D := Window.operandRegion script₀ L base
  have hH : H < 2^w := (levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit
  have cells := Window.lowCells (A:=script₀) L base (BlockProgram.layout_arity B ..).symm rfl hH
  have atOld : H ≤ levelStart L old := levelStart_mono L (Nat.zero_le _)
  have entry : LevelFields.Entry L first₀ pub st m := ⟨rfl,pitch⟩
  have head : BlockHeaderPlan.firstHeader.eval pub st m=header w L 0 :=
    BlockHeaderPlan.firstHeader_eval L base m st (Fin.ofNat_val_eq_self base).symm rows
  have headersRun := header_walk B f hf i X sel tape base positions blocks t old new hOld (by omega) m sub fit entry head
    (cells.2.trans_le atOld) (cells.1.trans_le atOld) (fuelBound B i) (Nat.le_max_left ..)
  have geom := ShrinkGreedyHeaderValues.post_header B i X f hf sel tape base positions blocks T first₀ old new
    hOld.symm hNew.symm m sub fit pub st entry (cells.2.trans_le atOld) heads scratch
  have initial := geom.reads_at B (fun _ _ => rfl)
  have lo := levelStart_mono L (Nat.zero_le (first₀+i.val))
  have lowSupp := operand_support B i X geom.raw geom.entry (· < origin) geom.pitchBelow
    (fun j hj => by have hi := geom.fieldsBelow; change _ < tableBase L old (0 : Fin 6); omega)
  have supp := operand_support B i X geom.raw geom.entry D (.inr (.inl rfl))
    (fun j _ => Or.inr (Or.inr (lo.trans (Nat.le_add_right ..))))
  have floor : H ≤ origin := by have h := geom.fieldsBelow; exact lo.trans ((Nat.le_add_right ..).trans h.le)
  have access := GreedyVisit.packet_access r H low
  have tailRun := GreedyVisit.packet_walk r L (BlockProgram.geometry B) i.val (BlockProgram.arena B i.val 0)
    pub st D initial lowSupp supp floor (fun j a x he => ((access j).1 a x he).1)
    (fun j a x he => ((access j).2 a x he).1) (fuelBound B i) (Nat.le_max_right ..)
  have totalRun : SourceWalk (Window.Raw (A:=script₀) L base t (fuelBound B i)) (visits B i) m
      (reports v L old new m++r.reports) := by
    apply headersRun.append
    rw [reports_after]; exact tailRun
  have live (j : Fin (visits B i).length) : Window.ordinal (A:=script₀) t ((W).index j) < directoryRows L := by
    rw [(W).ordinal_index,BlockProgram.directory_rows,(script₀).calendar_total]
    have hj := ((W).position j).isLt
    have hmul := Nat.mul_le_mul_right (script₀).block.length ht
    rw [Nat.succ_mul] at hmul
    omega
  let rowTime (j : Fin (script₀).size) := ((script₀).plan.recipes j).2.code.length+1+2*Schedule.Online.N (script₀).size (script₀).size+5
  let dataTime (j : Fin (script₀).size) := fuelBound B i+3+4*(((script₀).catalog j).params+1)+2*Schedule.Online.N (script₀).size (script₀).size+5
  have time (j : Fin (script₀).size) (hj : j ∈ (W).indices) : rowTime j + dataTime j ≤ clock B i := by
    apply List.single_le_sum (fun _ _ => Nat.zero_le _)
    exact List.mem_map.mpr ⟨j,hj,rfl⟩
  obtain ⟨ps,group,phases,logs⟩ := (W).group L base t (BlockProgram.layout_arity B ..).symm rfl hH cap
    (fuelBound B i) m _ totalRun rows pitch live (fun j hj => (Nat.le_add_right ..).trans ((time j hj).trans hc))
    (fun j hj => (Nat.le_add_left ..).trans ((time j hj).trans hc))
  refine ⟨ps,group,phases,logs,?_⟩
  rw [SourceOnline.post,logs,SourceWalk.after_append,reports_after]
  exact r.post_reports

end CompressorRecords.ShrinkHeaderGreedyPackets

end

end VPVNP
end Computability
end OAI
