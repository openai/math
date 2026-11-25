import OAI.Hierarchy.GridChosenReceiverTerminalScalars
import OAI.Hierarchy.GridChosenReceiverWriters
import OAI.Hierarchy.GridChosenReceiverWriterSpending
import OAI.Hierarchy.GridChosenReceiverEndpoints
import OAI.Hierarchy.TraceReceiverTerminalReturn
import OAI.Hierarchy.TraceReceiverJournalMaps
import OAI.Hierarchy.TraceReceiverElectedSites

namespace OAI
/-! # The installed terminal program reaches its actual weighted-field input -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage
open RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution GridScale GridThrough
open GridRegisteredSetting GridInstalledEvaluator Filter
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {B : Block F} {m A w : ℕ}
variable {Q : ℕ→ℕ} {loss : ℕ→ℝ} {v : TickSelection F (m+1) A w Q loss}
variable (I : Installed B m A w (degree B) (stageRate B) rootRate v)
variable (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
set_option quotPrecheck false
local notation "D" => I.D
local notation "l" => layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
local notation "n" => (l).sideMinusOne
local notation "channels" => GridControllerSimGeometry.railCount m n (l).bank
local notation "W" => (64*w)
local notation "gate" => (26*GridDescription.sector w)
local notation "arch" => GridDescription.capacity w
local notation "p" => (l).pinWidth
local notation "clock" => UniversalTick.clock w UniversalTick.saving
local notation "fuelCap" => (clock/40000)
local notation "V" => TraceAdmission.receiverAge w
local notation "units" => (D).issuedUnit w (degree B) (stageRate B) rootRate
local notation "widths" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)
local notation "U" => TraceReceiverSeedWords.wordsLayout (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "trees" => TraceReceiverSeedWords.forest (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "work" z:arg => (D).work z.1 (D).issuedCharges units
local notation "cost" z:arg => (D).costs (GridNativeImage.resources D l) z.1 m n (l).bank (D).issuedCharges units
local notation "group" z:arg c:arg j:arg => FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j))
local notation "chosen" z:arg => (D).run.plan.assemble z.1 ((receiverAssembly I) U) trees
local notation "which" z:arg => ((D).ordinal z.1).symm
local notation "fixed" z:arg => (D).run.terminalLabels z.1 z.2
local notation "table" safe:arg => (GridNativeDispatch.actualTable D safe).codes
local notation "room" safe:arg => GridNativeDispatch.selectorRoom D l R.table R.selector safe
local notation "rooms" recv:arg => (R.rooms recv 0 gate).choose
local notation "input" recv:arg safe:arg z:arg x:arg c:arg j:arg => streamInput I recv 0 gate R.text (rooms recv) widths
  (table safe) (room safe) z x c j
local notation "salt" recv:arg x:arg => (fun i : Fin I.inputSize=>GridDescription.input (x ∘ Wiring.railPin.symm)
  (GridDescription.code (q:=w^2) recv (D).machine) (GridNativeDispatch.source D l v.replacement 0 gate) i.val)

open TraceReceiverForward TraceReceiverJournalMemory
open scoped Fin.CommRing

local notation "b" => GridReceiverBanks.tasks w
local notation "qhead" => GridReceiverBanks.mapHeader w
local notation "cmd" => GridReceiverBanks.commands w
local notation "ctr" => GridReceiverBanks.cursor w
local notation "s" => TickWorkspace.base V
local notation "lim" => GridReceiverBanks.limit w
local notation "width" => GridReceiverBanks.width w

omit [Field F] [Fintype F] in
private theorem same_internal {leftArity rightArity : ℕ} (A : BitNetwork F leftArity) (T : BitNetwork F rightArity)
    (ports : leftArity=rightArity) (net : HEq A T) : A.internal=T.internal := by
  subst rightArity
  rw [eq_of_heq net]

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 64000 in
theorem slot_terminal (geom : GridReceiverDirectory.ElectionRoom D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom D) (z : (D).trace) (x : GridDiagonal.Pins (Fin channels))
    (c : Cell (m+1) n) (i : Fin v.copies) (before final : Memory W)
    (elected : GridReceiverDirectory.Elected D l geom safe z (GridReceiverDirectory.InputWindow D l z safe (room safe))
      (GridTicks.index (c,i)) (GridReceiverDirectory.shifted l w (input recv safe z x c i))
      (GridReceiverDirectory.original D l (GridReceiverDirectory.InputWindow D l z safe (room safe))
        (input recv safe z x c i)) before)
    (cache : slotCache I R geom recv safe z x c i before final)
    (scalar : TerminalScalars D l z.1)
    (ready : ∀ j : TraceReceiverElectedJournal.Journal D l geom safe z
      (GridReceiverDirectory.InputWindow D l z safe (room safe)) (GridTicks.index (c,i))
      (GridReceiverDirectory.shifted l w (input recv safe z x c i))
      (GridReceiverDirectory.original D l (GridReceiverDirectory.InputWindow D l z safe (room safe))
        (input recv safe z x c i)) before,TraceReceiverInstalledScalars.Ready D l j) :
    let t:=GridTicks.index (c,i)
    let ids:=selectedRoots D l z.1 t
    let ns:=fun j : Fin ids.length=>((D).issuedTree z.1 ids[j]).compile
    let wire:=slotWire I R geom recv safe z c i
    (terminal D l).Spec (·=final) (fun _ out=>Gather.Prepared ns (ctrl:=ctr) (control:=s 18)
      (atCmd:=cmd) (H:=fuelCap) wire (fun pinIndex : Fin p => (input recv safe z x c i) pinIndex.val)
      (s 9) (List.ofFn (Gather.rootSpan (s 9) fun j=>(ns j).cells)) out) (termAllowance D l z.1 ids) := by
  intro t ids ns wire
  obtain ⟨journal,ledger,held,owners,total⟩:=cache
  let ok:=ready journal
  let intervals:=streamLayout I R geom recv safe z
  let self:=GridDescription.code (q:=w^2) recv (D).machine
  let tape:=input recv safe z x c i
  have topo:=streamLayout_rows I R geom recv safe z
  obtain ⟨bounds,small⟩:=streamLayout_room I R geom z
  have header:=stream_header I recv 0 gate R.text (rooms recv) widths (table safe) (room safe) z x c i
  have frame:=elected_pins I geom safe z _ t elected
  have suffixIn:=wireSuffix_fit I R recv safe z c i
  have boundSuffix : wireSuffix I safe z≤p:=by omega
  have big:=ok.big
  have late : 7≤w:=(by decide : 7≤64^10).trans big
  obtain ⟨lower,upper⟩:=TraceAdmission.receiverAge_chart w big
  have pins : p≤2^w:=Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have timed : clock≤2^w:=Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have low : BitLayout.cellsBase p fuelCap≤ s 1:=
    TraceReceiverProgram.input_window late lower pins ((Nat.div_le_self _ _).trans timed)
  have here : s 1+TickWorkspace.stride V≤ s 9:=TickWorkspace.apart (u:=V) (by decide)
  have idsFit : ids.length≤2^(3*w/5):=by
    have h : ids.length≤(D).roots z.1:=by
      let fees := (D).issuedUnit w (l).degree (l).stageRate (l).rootRate
      let prices := (D).costs (GridNativeImage.resources D l) z.1 (l).dimension n (l).bank (D).issuedCharges fees
      simpa only [ids,selectedRoots,Fintype.card_fin] using
        (FactorAllocation.factors_nodup geom.teams_pos w prices t).length_le_card
    exact h.trans (journal.card.le.trans ((Nat.le_add_left _ _).trans total))
  rw [terminal_parts]
  intro _ _ _ machine
  refine TraceReceiverProgram.then_budget _ _ final (SlotRestored I R recv safe z x c i final) _
    (rebuild D l) (termAllowance D l z.1 ids)
    (slot_rebuild I R geom recv safe z x c i journal ok ledger held owners) ?_ machine
  intro restored closed
  let P:=selectedSource D l journal intervals ok final restored ledger closed.1 bounds small topo.1
    R.text self tape header.1 header.2 frame scalar.terminal (room safe) scalar.work scalar.degree boundSuffix
  have facts:=selectedInputs D l journal intervals ok final restored ledger closed.1 bounds small topo.1
    R.text self tape header.1 header.2 frame scalar.terminal (room safe) scalar.work scalar.degree boundSuffix
  have boot : P.initial=TraceReceiverTasks.beforeImage b (s 18+1) lim width ids.length
      (TraceAdmission.Resources.mounted (b).parent [s 9,p,0,0] restored):=rfl
  let arity:=fun k : Fin ids.length=>(D).issuedPorts z.1 ids[k]
  have ar (k : Fin ids.length) : (P.value k).pins=arity k:=
    (TraceReceiverElectedCache.selected_network D l journal intervals ids[k]).1
  have nt (k : Fin ids.length) : HEq (P.value k).net (ns k):=
    (TraceReceiverElectedCache.selected_network D l journal intervals ids[k]).2
  have ports : P.ports=arity:=funext fun k=>(P.original k).localPins.symm.trans (ar k)
  have rb := (TraceReceiverTasks.grid_before_sites late upper idsFit).1
  have countWord : TraceAdmission.Resources.mounted (b).parent [s 9,p,0,0] restored (s 18+1)=(ids.length : Word W) := facts.num
  have countFits : ids.length < 2^W :=
    ((Nat.le_mul_of_pos_left ids.length (by decide : 0 < 5)).trans (Nat.le_add_left _ _)).trans_lt rb.tasksFit
  have countValue := (congrArg Fin.val countWord).trans (Fin.val_cast_of_lt countFits)
  have ap : GridReceiverBanks.arena D l=P.arena:=arena_eq I safe z
  have code : P.writers=writeTerminal D l:=by
    unfold TraceReceiverForward.Source.writers writeTerminal
    rw [ap]; rfl
  refine ⟨P.writerCost restored,?_,?_⟩
  · refine terminal_spending D l z.1 ids P (s 18+1) lim cmd ctr width restored rfl ?_ ?_ rfl ok.even
      ?_ scalar.count scalar.resources ar nt ?_
    · change (degree B)=2*(2^(D).block.exponent 0)
      rw [I.block_eq]; rfl
    · change stageRate B=Gather.fullRate (D).block.stageClockRate 0
      rw [I.block_eq]; rfl
    · exact scalar.large
    · intro k
      exact (P.iteration k).2.1
  · rw [←code]
    intro _ _ _ machine
    refine P.ready_cast restored boot rb countValue facts.caches arity ports ns wire (fun k : Fin p=>tape k.val)
      fuelCap (slotEndpoint I R geom recv safe z) suffixIn rfl nt ?_ ?_ ?_ ?_ ?_ ?_ machine
    · intro k port
      exact slotWire_at I R geom recv safe z c i k (P.site k)
        (TraceReceiverElectedSites.terminal_heq D z.1 ids[k]) port _ rfl
    · intro k a
      let f := ids[k]
      have ext := (TraceReceiverJournalMemory.physical_width D l journal intervals f).1
      exact slotEndpoint_at_value I R geom recv safe z journal f ((D).terminalSite z.1 f)
        (TraceReceiverElectedSites.terminal_heq D z.1 f) ext a
    · intro f
      exact (Fintype.equivFin _ f).isLt.trans_le scalar.tags
    · intro k
      have size:=TraceReceiverElectedCache.selected_budget D l journal intervals ids[k]
        (l).degree (l).stageRate (l).rootRate (scalar.work _) (ok.paid _)
      have h:(P.value k).net.internal=(ns k).internal:=
        same_internal _ _ (ar k) (nt k)
      have gapBound : 2^(3*w/5)≤GridReceiverBanks.gap w:=Nat.pow_le_pow_right (by decide) (by omega)
      have hidden : (P.value k).net.internal ≤ 2^(3*w/5) :=
        ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans size
      exact h ▸ hidden.trans gapBound
    · exact low.trans (by omega)
    · intro a smallA
      have geo:=(Gather.grid_window late upper).1
      have s45:=TickWorkspace.apart (u:=V) (by decide : 1<45)
      exact (facts.frame a (by change a<GridReceiverBanks.base w;omega)).trans (closed.2.2 a (smallA.trans_le low))

/-- Every sufficiently large aligned receiver executes its terminal phase at
the single static allowance assigned to its actual roster. -/
theorem eventual_installed_terminal (blk : Block F) (env : Envelopes Q loss) (m A : ℕ)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ age : ℕ,64*w=16*age^10 → Even w →
    ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
    ∀ (I : Installed blk m A w (degree blk) (stageRate blk) rootRate v)
      (R : GridInstalledFit.Receipt blk m A w (degree blk) (stageRate blk) rootRate v I reserve 0),
    ∀ geom,InstalledTerminal I R geom := by
  let scale:=trace_scale env (m+1) A 2 q range
  filter_upwards [TraceReceiverInstalledScalars.ready (F:=F) (Q:=Q) (loss:=loss) blk m A scale,
    eventual_terminal_scalars blk m A env q range] with w compiler terminalNumerics
  intro age align even v copies I R geom recv safe z x c i
  have real : 64*w=16*(TraceAdmission.receiverAge w)^10 := by
    rw [GridReceiverClock.age_exact align]
    exact align
  have axes : I.axes+1=evalDepth w (m+1) A 2 (overhead Q loss w) (q w)+1-w/2 := by
    rw [←copies]
    exact I.axes_eq
  exact fun before final elected cache =>
    slot_terminal I R geom recv safe z x c i before final elected cache
      (terminalNumerics v copies I R recv safe z x c i)
      (compiler even real v I R axes I.passes_eq geom recv safe z x c i before)

end Hierarchy.GridChosenReceiver
end

end OAI
