import OAI.Computability.VPVNP.CompressorShrinkTermOnline
import OAI.Computability.VPVNP.CompressorShrinkHeaderReads

/-!
# Launching the shrinking term visits from the repeated calendar

At the packet's global ordinal the live scheduler computes the first
level of the block and uses the published scalar, incidence and scratch
cells of its shrinking substep. Evaluating the two concrete visit recipes
therefore launches the exact worker, start, stop and bank of the original
source packet.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkTermOnline

open BurstRAM Schedule BlockPlanner DescriptorSpace Compression ShrinkBlockInputs SourceOnline SourceTransport
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (s : X.ShrinkSelection B.shrink) (fuel : ℕ)
local notation "A" => BlockProgram.script B
local notation "F" => BlockProgram.geometry B
local notation "O" => BlockProgram.arena B i.val 0

private theorem transfer {u v : BlockPlanner.Visit} (e : u=v) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (bank : Fin v.worker.params → Word w) (h : (fun j => (v.params j).eval pub state m) = bank) :
    ∀ j, (u.params j).eval pub state m = bank (j.cast (congrArg (fun z : BlockPlanner.Visit => z.worker.params) e)) := by
  subst u
  exact fun j => congrFun h j

set_option maxHeartbeats 1200000 in
theorem prepared (L : DescriptorSpace.Layout) (base : Word w) (iteration total : ℕ) (j : ShrinkTermPackets.Stage)
    (raw : Memory w) (rs : List (Report w))
    (fields : ShrinkHeaderReads.Header i X T start L ((S.steps+1)*iteration) raw)
    (room : ShrinkInput.termEnd X start 10 < 2^w)
    (arityFit : arity (A).catalog = L.shape.arity) (baseFit : base.val = L.base) (fit : levelStart L 0 < 2^w)
    (totalRows : total = directoryRows L) (live : ordinal B i iteration j < total) :
    Prepared A L base (ordinal B i iteration j) total ⟨globalVisit B i X T start s fuel j,raw,rs⟩ := by
  intro m agree ord rows _ pitch
  let pt := Workspace.ports (arity (A).catalog) base
  let phase := index B i j
  let pre := Online.calendarMemory (d := (A).size) pt m phase
  let st := (A).recipeState base m
  have hcal := calendar B i iteration j
  have hlevel : (Online.calendar (A).plan).level (m pt.ordinal.val).val = iteration := by
    rw [ord]; exact hcal.2
  obtain ⟨entry,kept⟩ := SourceOnline.calendar_entry A L base arityFit baseFit fit m phase iteration hlevel
    (rows.trans totalRows) pitch
  have header : ShrinkHeaderReads.Header i X T start L ((S.steps+1)*iteration) pre :=
    (fields.keep agree).keep kept
  have read := ShrinkTermPackets.visit_readback B i O X T start F pt.data st pre (header.reads B entry) room j
  refine ⟨hcal.1,SourceOnline.launch_of_evaluation A base L arityFit baseFit fit m _ ?_ ?_ ?_ ?_ ?_⟩
  · rw [ord,← totalRows]; exact live
  · apply Fin.lt_def.mpr; rw [ord,rows]; exact live
  · change (((A).visit phase).initial).eval pt.data st pre = 0
    rw [index_visit]; exact read.1
  · change (((A).visit phase).stop).eval pt.data st pre = (ShrinkTermInputs.motifCount X : Word w)
    rw [index_visit]; exact read.2.1
  · exact transfer (index_visit B i j) pt.data st pre _ read.2.2

end CompressorRecords.ShrinkTermOnline

end

end VPVNP
end Computability
end OAI
