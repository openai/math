import OAI.Hierarchy.DescentResidentGeometryPhase
import OAI.Hierarchy.DescentDonorLayoutBit
import OAI.Hierarchy.DescentPackedColonyStep

namespace OAI
/-! # The same dynamic geometry phase publishes all three distinct resident banks -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic
open DescentPacking.PackedMatch.Local DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentHaloWalkRAM DescentSixParty.Chronology DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {r D p d cap profile H G M w : ℕ} (L : Layout)
local notation "P" => breadth D
local notation "rows" => H*chunks G M
local notation "a" => Owners.inputBits r D p d
local notation "out" => Owners.Board.venue a M L.ownerBase rows

structure Prior (L : Layout) : Prop where
  adjacency : L.walks.adjacency.base+L.walks.adjacency.size≤L.ownerBase
  root : L.walks.root.base+L.walks.root.size≤L.ownerBase
  directions : ∀j,(L.walks.choice j).base+(L.walks.choice j).size≤L.ownerBase
  offsets : L.ranks.start.base+L.ranks.start.size≤L.ownerBase
  flags : L.hub.base+L.hub.size≤L.ownerBase

theorem resident_dynamic (Q : Owners.LayoutBit.Banks) (raw : Expr) (lay : Bool) (u : Fin H→Fin G→Panel r D p d)
    (rs : Fin H→Fin D→Option (Fin H)) (hub : Fin H→Bool) (m : Memory w)
    (room : Room L r D p d H G M w (Owners.LayoutBit.field Q raw))
    (source : Owners.LayoutBit.Room Q raw H G M (d*DescentPacking.PackedMatch.Local.fields r D p) w L.ownerBase)
    (kept : Prior L) (amount : H≤L.hub.size)
    (gate : m Q.gate.base=(if lay then (1:Word w) else 0))
    (active : ∀j : Row H G M,m (Q.live.base+(row H G M j).val)=((data (fun (_:Fin H) (_:Fin G)=>(1:Cell 1)) j).val:Word w))
    (tables : Static Q.widen (Owners.LayoutBit.join (d*DescentPacking.PackedMatch.Local.fields r D p)) M m)
    (old_ : Source raw (fun h g=>encodePanel (u h g)) M m)
    (neighbors : DescentHaloWalkRAM.Reads L.walks rs m)
    (roots : ∀ (h : Fin H) (k : Fin P), m (L.ranks.start.base+(Ranks.id h k).val)=((h.val*P:ℕ):Word w))
    (hubBits : ∀h : Fin H,m (L.hub.base+h.val)=((hub h).toNat:Word w)) :
    let term:=Owners.LayoutBit.field Q raw
    let state:=phase L r D p d cap profile H G M w term
    state.Runs m ∧ Source term (fun h g=>Owners.register lay (u h g)) M (state.image m) ∧
      DescentPackedColony.Reads (Owners.Board.bank out rows) (fun h g=>Owners.render r D p d cap profile (Owners.register lay (u h g))) M (state.image m) ∧
      DescentHaloPackedRebase.Reads (DonorHeaders.shelf H G M D L.literal L.rankOut) (DonorHeaders.ordValue rs) M G (state.image m) ∧
      DescentHaloPackedRebase.Reads (DonorHeaders.shelf H G M D L.literal L.hubOut) (DonorHeaders.tagValue rs hub) M G (state.image m) ∧
      ∀i,i<L.ownerBase→state.image m i=m i := by
  intro term state
  let up:=Owners.Board.issued cap profile L.ownerBase term H G M r D p d m
  have operand:=Owners.LayoutBit.source Q raw L.ownerBase source lay u m gate active tables old_
  have span:=room.owner_end
  have eout:=room.order.output
  have keys:=room.order
  have step : L.ranks.endpoints.base+H*P≤L.rankOut:=(Nat.add_le_add_left keys.sizeEnd _).trans keys.endpoints.2.2
  obtain ⟨oldRun,owner,oldFrame,cpu⟩:=Owners.Board.run cap profile L.ownerBase term u lay m room.operand room.packed (by omega) operand
  have begin_ : L.ownerBase ≤ out :=
    calc
      L.ownerBase ≤ Owners.Board.rom L.ownerBase rows := Nat.le_add_right ..
      _ ≤ Owners.Board.rom L.ownerBase rows + 2^(a*M) := Nat.le_add_right ..
      _ ≤ out := Nat.le_add_right ..
  have before (i : ℕ) (small : i<L.ownerBase) : up i=m i:=oldFrame i (.inl small)
  have near : DescentHaloWalkRAM.Reads L.walks rs up := by
    constructor
    · intro h j
      have idx:= (finProdFinEquiv (h,j)).isLt
      have atVal : (finProdFinEquiv (h,j)).val=h.val*D+j.val:=by
        simp only [finProdFinEquiv_apply_val]
        ac_rfl
      rw [atVal] at idx
      have within := (Nat.add_lt_add_left (idx.trans_le room.walk.adjacencySize)
        L.walks.adjacency.base).trans_le kept.adjacency
      rw [before _ (by simpa only [Nat.add_assoc] using within)]
      exact neighbors.adjacency h j
    · intro h k
      rw [before _ ((Nat.add_lt_add_left ((DescentHaloWalkRAM.row h k).isLt.trans_le room.walk.rootSize) _).trans_le kept.root)]
      exact neighbors.root h k
    · intro h k j
      rw [before _ ((Nat.add_lt_add_left ((DescentHaloWalkRAM.row h k).isLt.trans_le (room.walk.choiceSize j)) _).trans_le (kept.directions j))]
      exact neighbors.choice h k j
  obtain ⟨headRun,ord,flags,headFrame⟩:=DonorHeaders.native_headers rs hub L.walks L.ranks L.hub L.rankOut L.hubOut L.literal up
    room.walk room.order room.separated room.table room.ceiling near
    (fun h k=>(before _ ((Nat.add_lt_add_left ((Ranks.id h k).isLt.trans_le keys.sizeStart) _).trans_le kept.offsets)).trans (roots h k))
    (by have:=kept.offsets;omega) room.walk.sentinel room.flag amount
    (fun h=>(before _ ((Nat.add_lt_add_left (h.isLt.trans_le amount) _).trans_le kept.flags)).trans (hubBits h))
  have held (i : ℕ) (small : i<L.ownerBase) : state.image m i=m i:=(headFrame i (by omega)).trans (before _ small)
  refine ⟨oldRun.then headRun,fun x=>(ProtocolRAM.eval_below term _ m (state.image m) room.operand held).trans (operand x),
    fun x=>?_,ord,flags,held⟩
  exact (headFrame _ ((Nat.add_lt_add_left (row H G M x).isLt out).trans_le span)).trans (owner x)

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic

end OAI
