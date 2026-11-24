import OAI.Computability.VPVNP.CompressorSourcePitch
import OAI.Computability.VPVNP.CompressorSourceBankFrame
import OAI.Computability.VPVNP.CompressorOnlineBranchCut

/-!
# Executing a complete chronological sequence of native descriptor visits

The input is the sequence of original source packets and its memory
invariants. Each row recipe is evaluated at its own calendar ordinal in
any live memory that agrees with that packet's input data. The construction
threads the *actual* post-memory of the dispatcher through all packets,
preserving source reports and branch choices, and terminates at exhaustion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM BlockPlanner DescriptorSpace Schedule SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} (A : Script) (L : Layout) (base : Word w)
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0
local notation "D" => Online.N A.size A.size
local notation "strideCell" => Fin.val (Schedule.Ports.directory pt - 1)
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex A.size A.size)
local notation "Pkt" => SourceWalk.Packet (Visit A w) w

/-- Facts obtained by inspecting the actual source program for this packet. -/
structure Checked (cap : ℕ) (p : Pkt) : Prop where
  positiveFuel : 0 < p.stage.fuel
  recipeClock : (A.plan.recipes p.stage.phase).2.code.length+1+2*D+5 ≤ cap
  dataClock : p.stage.fuel+3+4*((A.catalog p.stage.phase).params+1)+2*D+5 ≤ cap
  progress : Progress p.stage.stop p.stage.start p.reports
  read : Reads (H ≤ ·) (eventLog p.reports)
  write : Writes (H ≤ ·) (eventLog p.reports)

/-- Physical recipe evaluation at the packet's true offset. -/
def Prepared (ordinal total : ℕ) (p : Pkt) : Prop :=
  ∀ m : Memory w, Agree (H ≤ ·) p.input m → (m (pt).ordinal.val).val = ordinal →
    (m (pt).rows.val).val = total → m (pt).tag.val = tag → m strideCell = (levelWords L : Word w) →
    (Online.calendar A.plan).phase ordinal = p.stage.phase.val ∧ p.stage.Launch pt m

private theorem fold_append (m : Memory w) (r s : List (Report w)) :
    after m (eventLog (r++s)) = after (after m (eventLog r)) (eventLog s) :=
  SourceWalk.after_append m r s

/-- A semantic source-packet sequence determines valid steps of the concrete
online program, with precisely the same worker reports and worker tapes. -/
theorem interval_stable (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (cap ordinal total : ℕ) (m raw : Memory w) (ps : List Pkt)
    (chron : SourceWalk.Chronological Visit.Runs raw ps)
    (checks : ∀ p ∈ ps, Checked A L cap p)
    (prepare : ∀ i : Fin ps.length, Prepared A L base (ordinal+i.val) total ps[i.val])
    (count : ordinal+ps.length ≤ total) (room : total ≤ directoryRows L)
    (agree : Agree (H ≤ ·) raw m) (ho : (m (pt).ordinal.val).val=ordinal) (ht : (m (pt).rows.val).val=total)
    (hTag : m (pt).tag.val = tag) (pitch : m strideCell = (levelWords L : Word w)) :
    ∃ steps : List (Online.Run.Step A.size A.size w),
      Online.Run.Interval A.plan pt cap m steps ∧
      steps.map Online.Run.Step.phase = ps.map (fun p ↦ p.stage.phase) ∧
      steps.map (fun s ↦ s.row.reports) = ps.map SourceWalk.Packet.reports ∧
      steps.map (fun s ↦ s.row.choices) = ps.map (fun p ↦ p.stage.choices) ∧
      Agree (H ≤ ·) (after raw (eventLog (ps.flatMap SourceWalk.Packet.reports)))
        (Online.Run.finalMemory (C := A.catalog) pt m steps) ∧
      ((Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).ordinal.val).val = ordinal+ps.length ∧
      (Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).rows.val = m (pt).rows.val ∧
      (Online.Run.finalMemory (C := A.catalog) pt m steps) strideCell = m strideCell ∧
      SourceBankFrame.Stable (base.val+6) m (Online.Run.intervalLog A.plan pt m steps) := by
  induction ps generalizing raw m ordinal with
  | nil =>
    exact ⟨[],trivial,rfl,rfl,rfl,agree,by simpa only [Online.Run.finalMemory,List.length_nil,Nat.add_zero] using ho,rfl,rfl,trivial⟩
  | cons p ps ih =>
    obtain ⟨rfl,run,rest⟩ := chron
    have lead : Prepared A L base ordinal total p := by simpa using prepare (0 : Fin (p::ps).length)
    have active : m (pt).ordinal.val < m (pt).rows.val := by
      apply Fin.lt_def.mpr; simp only [List.length_cons] at count; omega
    obtain ⟨phase,launch⟩ := lead m agree ho ht hTag pitch
    let r := p.stage.row pt m p.reports
    let s : Online.Run.Step A.size A.size w := ⟨p.stage.phase,r⟩
    let post := Online.post A.catalog A.size pt r
    have ck := checks p List.mem_cons_self
    obtain ⟨hv,ha,ho',ht'⟩ := packet A L base hg hb fit p.stage p.input m p.reports cap agree
      (ho ▸ phase) active ((Fin.lt_def.mp active).trans_le (ht.le.trans room)) launch ck.positiveFuel
      ck.recipeClock ck.dataClock run ck.progress ck.read ck.write
    have prepTail (i : Fin ps.length) : Prepared A L base ((ordinal+1)+i.val) total ps[i.val] := by
      simpa only [Fin.val_succ,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i.val] using prepare i.succ
    have postTag : post (pt).tag.val = tag := by simp [post,Online.post,writeMemory]
    have stride : post strideCell = m strideCell :=
      pitch_packet A L base hg hb fit p.stage m p.reports ((Fin.lt_def.mp active).trans_le (ht.le.trans room)) ck.write
    obtain ⟨ss,hss,hp,hr,hc,hm,hl,htail,hstride,hstable⟩ := ih (ordinal := ordinal+1) (raw := p.output) (m := post) rest
      (fun q hq ↦ checks q (List.mem_cons_of_mem _ hq)) prepTail (by simp only [List.length_cons] at count; omega)
      ha (ho'.trans (congrArg (·+1) ho)) ((congrArg Fin.val ht').trans ht) postTag (stride.trans pitch)
    refine ⟨s::ss,⟨hv,hss⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact congrArg (p.stage.phase :: ·) hp
    · exact congrArg (p.reports :: ·) hr
    · exact congrArg (p.stage.choices :: ·) hc
    · simpa only [List.flatMap_cons,fold_append,Online.Run.finalMemory,SourceWalk.Packet.output,s,post] using hm
    · simpa only [Online.Run.finalMemory,List.length_cons,s,post,Nat.add_assoc,Nat.add_comm 1 ps.length] using hl
    · exact htail.trans ht'
    · exact hstride.trans stride
    · apply (SourceBankFrame.row_stable A L base hg hb fit m p.stage.phase r
        ((Fin.lt_def.mp active).trans_le (ht.le.trans room)) hv.input hv.source ck.write).append
      rw [(Online.row_effect A.plan pt m p.stage.phase r hv.input hv.source 0).1]
      exact hstable

/-- A semantic source-packet sequence determines valid steps of the concrete
online program, with precisely the same worker reports and worker tapes. -/
theorem interval (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (cap ordinal total : ℕ) (m raw : Memory w) (ps : List Pkt)
    (chron : SourceWalk.Chronological Visit.Runs raw ps)
    (checks : ∀ p ∈ ps, Checked A L cap p)
    (prepare : ∀ i : Fin ps.length, Prepared A L base (ordinal+i.val) total ps[i.val])
    (count : ordinal+ps.length ≤ total) (room : total ≤ directoryRows L)
    (agree : Agree (H ≤ ·) raw m) (ho : (m (pt).ordinal.val).val=ordinal) (ht : (m (pt).rows.val).val=total)
    (hTag : m (pt).tag.val = tag) (pitch : m strideCell = (levelWords L : Word w)) :
    ∃ steps : List (Online.Run.Step A.size A.size w),
      Online.Run.Interval A.plan pt cap m steps ∧
      steps.map Online.Run.Step.phase = ps.map (fun p ↦ p.stage.phase) ∧
      steps.map (fun s ↦ s.row.reports) = ps.map SourceWalk.Packet.reports ∧
      steps.map (fun s ↦ s.row.choices) = ps.map (fun p ↦ p.stage.choices) ∧
      Agree (H ≤ ·) (after raw (eventLog (ps.flatMap SourceWalk.Packet.reports)))
        (Online.Run.finalMemory (C := A.catalog) pt m steps) ∧
      ((Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).ordinal.val).val = ordinal+ps.length ∧
      (Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).rows.val = m (pt).rows.val ∧
      (Online.Run.finalMemory (C := A.catalog) pt m steps) strideCell = m strideCell := by
  obtain ⟨steps,valid,phase,reports,bits,memory,ord,rows,stride,_⟩ :=
    interval_stable A L base hg hb fit cap ordinal total m raw ps chron checks prepare count room agree ho ht hTag pitch
  exact ⟨steps,valid,phase,reports,bits,memory,ord,rows,stride⟩

private theorem valid_at_end {d w i r cap : ℕ} {C : Catalog d} {plan : Online.Config C i r} {ports : Ports w}
    {m : Memory w} (steps : List (Online.Run.Step d (i+r) w)) (hs : Online.Run.Interval plan ports cap m steps)
    (endRows : let z := Online.Run.finalMemory (C := C) ports m steps
      z ports.rows.val ≤ z ports.ordinal.val) : Online.Run.Valid plan ports cap m steps := by
  induction steps generalizing m with
  | nil => exact endRows
  | cons s rest ih => exact ⟨hs.1,ih hs.2 endRows⟩

/-- A semantic source-packet sequence determines valid steps of the concrete
online program, with precisely the same worker reports and worker tapes. -/
theorem sequence (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (cap ordinal total : ℕ) (m raw : Memory w) (ps : List Pkt)
    (chron : SourceWalk.Chronological Visit.Runs raw ps)
    (checks : ∀ p ∈ ps, Checked A L cap p)
    (prepare : ∀ i : Fin ps.length, Prepared A L base (ordinal+i.val) total ps[i.val])
    (count : ordinal+ps.length = total) (room : total ≤ directoryRows L)
    (agree : Agree (H ≤ ·) raw m) (ho : (m (pt).ordinal.val).val=ordinal) (ht : (m (pt).rows.val).val=total)
    (hTag : m (pt).tag.val = tag) (pitch : m strideCell = (levelWords L : Word w)) :
    ∃ steps : List (Online.Run.Step A.size A.size w),
      Online.Run.Valid A.plan pt cap m steps ∧
      steps.map Online.Run.Step.phase = ps.map (fun p ↦ p.stage.phase) ∧
      steps.map (fun s ↦ s.row.reports) = ps.map SourceWalk.Packet.reports ∧
      steps.map (fun s ↦ s.row.choices) = ps.map (fun p ↦ p.stage.choices) ∧
      Agree (H ≤ ·) (after raw (eventLog (ps.flatMap SourceWalk.Packet.reports)))
        (Online.Run.finalMemory (C := A.catalog) pt m steps) := by
  obtain ⟨steps,valid,phase,reports,choices,mem,ordinalEnd,rowsEnd,_⟩ := interval A L base hg hb fit cap ordinal total m raw ps
    chron checks prepare count.le room agree ho ht hTag pitch
  refine ⟨steps,valid_at_end steps valid ?_,phase,reports,choices,mem⟩
  apply Fin.le_def.mpr
  rw [rowsEnd,ht,ordinalEnd,count]


end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
