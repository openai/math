import OAI.Computability.VPVNP.CompressorRefreshSelectorInput
import OAI.Computability.VPVNP.CompressorRefreshCoreHeader
import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorTermWorkerDispatch

/-! # The physical selector packet at the degree-refresh cut

The fixed block index identifies the term worker following the gathered demand
rows. Its four address operands are computed from the live header. The same
packet is prepared at that ordinal in each repetition of the fixed script.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.RefreshSelector

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PairSimulation.LocalHistory
open PortRefresh PortRefresh.LevelRecipe SelectedTerms NewSlots BlockPlanner DescriptorSpace
open Schedule PhaseRecipe SourceTransport
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {g w : ℕ} (X : State S.portExponent (S.portExponent+g))
local notation "O" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "sh" => RefreshBlockPlan.shape B
local notation "ord" => RefreshBlockPlan.order B
local notation "n" => Fintype.card X.Base * 2^g
local notation "d" => LevelRecipe.Shape.ties sh
local notation "stride" => LevelRecipe.Shape.stride sh
local notation "e" => (LevelRecipe.Shape.ports sh)*(LevelRecipe.Shape.dH sh)
local notation "scr" => BlockProgram.script B
local notation "inp" => RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)
local notation "V" => BlockIndex.refreshSelector B
local notation "demand" => blockDemandWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X)

/-- The occurrence immediately after the last demand scan, inside the complete script. -/
def selectorWindow : Window scr [V] :=
  let foc := BlockIndex.blockRefresh B
  ⟨foc.before,foc.after,foc.split.trans (by simp only [List.append_assoc,List.cons_append,List.nil_append]; rfl)⟩

/-- The fixed-script visit index of the refresh motif selector immediately after the
deterministic demand prefix. -/
def selectorIndex := (selectorWindow B).index 0

theorem selector_visit : (scr).visit (selectorIndex B) = V := (selectorWindow B).visit 0

theorem selector_position : Fin.val (Window.position (selectorWindow B) 0) = (BlockIndex.blockRefresh B).index.val := Nat.add_zero _

/-- The packet uses the published header evaluated before the selector. It
may be mounted with any prospective tape, including an empty one. -/
def packet (C : Context w) (fuel : ℕ) (tapes : List (List Bool)) (rs : List (Report w)) : SourceOnline.Packet scr w :=
  ⟨HeaderPacket.attach scr (selectorIndex B) C.pub C.state C.memory fuel tapes,C.memory,rs⟩

private theorem params_at {v v' : BlockPlanner.Visit} (h : v=v') (i : Fin v.worker.params) :
    v.params i = v'.params (Fin.cast (congrArg (fun q : BlockPlanner.Visit ↦ q.worker.params) h) i) := by subst v'; rfl

variable (old : IncidenceDirectory w) (start : ℕ)
local notation "p" => Allocation.plan X (LevelRecipe.Shape.a₀ sh) (LevelRecipe.Shape.dH sh) d stride start
local notation "source" => NewSlots.word (bits := w) (Allocation.Plan.demand p)
local notation "dest" => NewSlots.word (bits := w) (Allocation.Plan.term p)

private theorem selectorHeads : PortRefresh.termAddresses source dest stride d =
    ![source, NewSlots.word d, dest, NewSlots.word stride] := by
  funext i; fin_cases i <;> apply Fin.ext <;> simp [PortRefresh.termAddresses,NewSlots.word]

theorem termParams (C : Context w) (h : Describes (s := sh) inp C X start old)
    (i : Fin ((scr).catalog (selectorIndex B)).params) :
    let code : (scr).catalog (selectorIndex B) = TermWorker.motifPass (grid O).block (grid O).demandOrder.entries (grid O).e :=
      congrArg BlockPlanner.Visit.worker (selector_visit B)
    (((scr).visit (selectorIndex B)).params i).eval C.pub C.state C.memory =
      TermWorker.catalogWords (grid O).block (grid O).demandOrder.entries (grid O).supplyOrder.entries
        (scr).catalog (selectorIndex B) (PortRefresh.termAddresses source dest stride d) code i := by
  intro code
  have hv := selector_visit B
  let i' := Fin.cast (congrArg (fun q : BlockPlanner.Visit ↦ q.worker.params) hv) i
  have hi := params_at hv i
  let slot : Fin (RefreshBlockPlan.term B).params := i'
  have banks : C.eval ((V).params i') = _ := motif_workerBank_eq (s := sh) (w := w) (g := g) inp S.degree_bounds.2 S.graph ord C X start old (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh h (.term : Stage sh) slot
  rw [hi]
  change C.eval ((V).params i') = _
  refine banks.trans ?_
  have orderEq : (grid O).supplyOrder.entries = finProdFinEquiv.symm := by ext j; rfl
  rw [TermWorker.catalogWords,orderEq,selectorHeads B X start]
  rfl

variable (L : DescriptorSpace.Layout) (base : BurstRAM.Word w) (t : ℕ)
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Ports.data pt
local notation "firstLevel" => Script.levelsPerBlock scr*t
local notation "state" => (levelStart L firstLevel : BurstRAM.Word w)
local notation "H" => levelStart L 0
local notation "idx" => selectorIndex B
local notation "pos" => Fin.val (Window.position (selectorWindow B) 0)
local notation "atRow" => List.length (Script.initial scr) + t*List.length (Script.block scr) + pos

/-- The actual calendar launches this packet from every scheduler memory
agreeing with the prepared post-memory. No term selection enters this proof. -/
theorem prepared (m : Memory w) (fuel : ℕ) (tapes : List (List Bool)) (rs : List (Report w))
    (arityEq : arity (scr).catalog = L.shape.arity) (baseEq : base.val=L.base) (fit : H<2^w)
    (rows : m (pt).rows.val = (directoryRows L : BurstRAM.Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : BurstRAM.Word w))
    (live : atRow < directoryRows L)
    (head : RefreshCore.Header (Fintype.card X.Base) g (levelStart L (firstLevel+S.steps)) start old m) :
    SourceOnline.Prepared scr L base atRow (directoryRows L) (packet B ⟨pub,state,m⟩ fuel tapes rs) := by
  let C : Context w := ⟨pub,state,m⟩
  let D := Window.operandRegion scr L base
  have ent : LevelFields.Entry L firstLevel C.pub C.state C.memory := ⟨rfl,pitch⟩
  have supp : InputReads D C.pub C.state C.memory inp := RefreshCore.Header.reads (F := BlockProgram.geometry B)
    (step := S.steps) rfl (0 : Fin 6) rfl ent head (.inr (.inl rfl))
    (fun z _ ↦ .inr (.inr ((levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..))))
  have stage := stage_supported D C.pub C.state C.memory B supp (.term : Stage sh)
  have h : HeaderOperands.Supported D C.pub C.state C.memory ((scr).visit idx) := (selector_visit B).symm ▸ stage
  exact (selectorWindow B).prepared L base arityEq baseEq fit 0 t (packet B C fuel tapes rs) m (fun _ _ ↦ rfl) rows pitch live
    ⟨rfl,rfl,rfl,fun _ ↦ rfl,h.initial,h.stop,h.params⟩

end CompressorRecords.RefreshSelector

end

end VPVNP
end Computability
end OAI
