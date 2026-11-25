import OAI.Computability.VPVNP.PairShrinkPreparedCall
import OAI.Computability.MultitapeWeakETH.ShrinkABPlaced
import OAI.Computability.MultitapeWeakETH.ShrinkCDTape
import OAI.Computability.MultitapeWeakETH.ShrinkSharedTape
import OAI.Computability.MultitapeWeakETH.ShrinkSupplyTape
import OAI.Computability.VPVNP.PairShrinkRoleMapLabels

/-! # A selected resident's physical operand banks and typed local arguments -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid CompressorRecords
open DescriptorSpace PhaseRecipe ShrinkBlockInputs MapResidentRows
open scoped Classical Fin.CommRing
noncomputable section

/-- External read context, keyed old packets, new packet and keyed hidden fields. -/
abbrev Buffers (D : Type) := ((D × NamedPackets.Bank) × Bits.Word) × NamedPackets.Bank

def external {D : Type} (read : D × Bits.Word → Bits.Word) (q : Buffers D × Bits.Word) :=
  read (q.1.1.1.1,q.2)

theorem external_poly {D : Type} [Codec D] {read : D × Bits.Word → Bits.Word} (hr : Poly read) : Poly (external read) :=
  (show Poly (fun q : Buffers D × Bits.Word => (q.1.1.1.1,q.2)) by fun_prop).compose hr

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)

/-- A single mathematical realization of the independent parent, child and internal
fields used by all the resident calls at a selected site. -/
structure SiteArguments (g : ℕ) where
  state : State (a i) (packingLaneBits (a i) g)
  choice : SelectedScore.Selection B state
  owner : MapResidentRows.Site state
  children : Order {u // owner = (state.packingData.shrinkPlace (SelectedFinish.chosen B state choice) ∘
    state.packingInputIso.site.symm) u}
  old : Placed (state.packingData.shrinkPlace (SelectedFinish.chosen B state choice) ∘ state.packingInputIso.site.symm)
    state.network.Half owner
  parent : (state.shrinkNext B.shrink (S.shrink i) choice).network.Half owner
  hidden : Placed (state.packingData.shrinkInternalOwner (SelectedFinish.chosen B state choice))
    (internalLabel (ShrinkPreparedCall.width B.shrink state choice) (SelectedFinish.chosen B state choice)) owner

variable {B i} {g : ℕ} (z : SiteArguments B i g)

def SiteArguments.buffers {D : Type} (ctx : D) (w : ℕ) : Buffers D :=
  let h := ShrinkHiddenSlots.rows z.state (SelectedFinish.chosen B z.state z.choice)
    (ShrinkPreparedCall.width B.shrink z.state z.choice) z.owner z.hidden
  (((ctx,NamedPackets.placedBank z.state _ z.owner z.children z.old w),
    packed (z.state.shrinkNext B.shrink (S.shrink i) z.choice) z.owner z.parent),
    h.map (fun r => wordBits (r.1 : Word w)),h.map Prod.snd)

abbrev SiteArguments.Row := Fin (order z.state (SelectedFinish.chosen B z.state z.choice) z.owner).length

/-- The native row index, with its equality oriented for the six-party map. -/
def SiteArguments.row (j : z.Row) :=
  let side := SelectedFinish.chosen B z.state z.choice
  (⟨entry z.state side z.owner j,((order z.state side z.owner).entries j).property.symm⟩ :
    z.state.packingData.ResidentMap side z.owner)

theorem SiteArguments.row_ordered (j : z.Row) : z.row j =
    ShrinkRole.MapWitness.rowEquiv z.state (SelectedFinish.chosen B z.state z.choice) z.owner j := rfl

noncomputable def SiteArguments.input (j : z.Row) : EntryInput B.shrink :=
  ShrinkRole.MapWitness.input B i z.state z.choice z.owner z.old z.parent z.hidden
    (ShrinkRole.MapWitness.rowEquiv z.state (SelectedFinish.chosen B z.state z.choice) z.owner j)

/-- Address parameters of the retained level and the native memory containing its records. -/
structure Level (w : ℕ) where
  base : Word w
  positions : ℕ
  blocks : ℕ
  n : ℕ
  cur : ℕ
  memory : Memory w

variable {w : ℕ} (d : Level w)

def Level.head (B : S.Templates) : Word w :=
  ((levelStart (BlockProgram.layout B d.base.val d.positions d.blocks) d.cur : ℕ) : Word w)

def SiteArguments.query {D : Type} (ctx : D) (j : z.Row) : ShrinkHidden.Indexed (Buffers D) :=
  (ShrinkHidden.query (z.buffers ctx w) (d.head B) (d.n*d.n) (siteIndex z.state z.owner).val,tally j.val)

/-- Native payload and size bounds used uniformly over the entire resident row. -/
structure SiteArguments.Ready : Prop where
  data : CompiledResident.ShrinkPayload B d.base d.positions d.blocks d.n d.cur i z.state z.choice d.memory
  positions : z.state.positions ≤ d.n
  degree : 2^(a i) ≤ d.n
  nextDegree : 2^(b i) ≤ d.n
  width : z.state.maxWireWidth ≤ d.n
  nextWidth : (z.state.shrinkNext B.shrink (S.shrink i) z.choice).maxWireWidth ≤ d.n
  factor : fieldFactor B.shrink * (z.state.maxWireWidth+1) ≤ d.n*d.n
  positive : 1 ≤ d.n
  room : 2*d.n*d.n*d.n < 2^w

theorem SiteArguments.space (h : z.Ready d) :
    (siteOrder z.state).length ≤ 2^w ∧ 2*d.n*d.n < 2^w ∧
    (siteOrder z.state).length * (2*d.n*d.n) ≤ 2^w ∧ z.state.maxWireWidth ≤ d.n*d.n ∧ d.n*d.n < 2^w := by
  have ord : (siteOrder z.state).length = z.state.positions := by
    change (siteOrder z.state).length = Fintype.card z.state.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder z.state).entries
  have sq := Nat.le_mul_of_pos_right d.n h.positive
  have twice : d.n*d.n ≤ 2*d.n*d.n := by rw [Nat.mul_assoc]; omega
  have cube := Nat.le_mul_of_pos_right (2*d.n*d.n) h.positive
  have sf := cube.trans_lt h.room
  rw [ord]
  exact ⟨h.positions.trans (sq.trans (twice.trans sf.le)),sf,
    ((Nat.mul_le_mul_right _ h.positions).trans_eq (Nat.mul_comm ..)).trans h.room.le,
    h.width.trans sq,twice.trans_lt sf⟩

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
