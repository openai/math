import OAI.Hierarchy.TaggedWideSpillPooledLive
import OAI.Hierarchy.ProtocolRAMDateSpillRoles
import OAI.Hierarchy.TaggedWirePacketNeighborSlots

namespace OAI
/-! # The original signed roles drive the true physical chord word at the dated site -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ReportSockets CoreBoard HistoryRoles RoleProgram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope NamedAperture Tagged PassiveWindow
open scoped Classical
set_option quotPrecheck false
variable {h W k attempts n cap : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark)
    (names : Fin n≃HistoryRoles.Source S π depth mark) (vtx : Site h (2^W) k)
local notation "whereAt" => name vtx
local notation "sites" => siteLast h (2^W) k+1
local notation "deg" => stride k S.degree attempts
local notation "ends" => sorted S π depth mark ∘ names
local notation "port" => named S π depth mark unique names
local notation "half" => physical S π depth mark unique
local notation "shelf" => shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S
local notation "here" => named_coordinate S π depth mark unique names
local notation "fiber" => Fiber (attempts:=attempts) S vtx

/-- The same finite public role number is used by the physical barrel and
the scheduled native half-word directory. -/
def spillSeat (a : fiber) : Fin deg := ⟨HistoryRoles.code S a.val,code_bound S a.val⟩

variable (amount : Fin n→ℕ) (bound : ∀i,amount i≤cap) {total : Widths (siteLast h (2^W) k+1)}
    (shape : installedWidths (sorted S π depth mark ∘ names) amount=total)
local notation "slot" => PacketNeighbor.localSlot ends amount port shelf here whereAt
local notation "parts" => carried ends amount whereAt bound slot shape

/-- A positive named entry of the real full dated sheet always points at
the genuine aggregate local chord. -/
theorem outlet (i : Fin n) (b reported : Bool) (positive : 0<amount i)
    (loc : (rowGraph ends).vertex i b=whereAt) :
    ∃a:fiber,
      ProtocolRAMTurnOperands.printed S reported (fun c=>half (names i,c)) b false=labelled S reported a.val ∧
      (parts).owner (spillSeat S vtx a)=some ⟨(ends i,b),loc⟩ := by
  let src : EndsAt ends amount whereAt:=⟨⟨(i,b),loc⟩,positive⟩
  have namedAt : name (HistoryRoles.site S (port (i,b)))=whereAt:=(named_site S π depth mark unique names i b).trans loc
  let a:fiber:=⟨port (i,b),name.injective namedAt⟩
  refine ⟨a,printed_named S π depth mark unique names i b reported false,?_⟩
  have addr:slot src=spillSeat S vtx a := by
    change (finProdFinEquiv.symm (finProdFinEquiv _)).2=_
    rw [Equiv.symm_apply_apply]
    rfl
  exact addr ▸ (PacketNeighbor.local_owner ends amount port shelf here whereAt bound shape src)

variable (board : RoleProgram.Board) (B : Mount (S:=S) π (name (h:=h) (W:=W) (k:=k)) board.edges)
    (pad : Chord (siteLast h (2^W) k+1)) (spill : Goods h W k→ℕ)
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "L" => B.datedLayout inj pad
local notation "cnt" => (L).bits spill
local notation "mass" => routeLoad (L).routes cnt

private theorem vertex_of_chord_eq {s n m : ℕ} {first : Fin n → Chord s} {second : Fin m → Chord s}
    {i : Fin n} {j : Fin m} (same : first i = second j) (b : Bool) :
    (rowGraph first).vertex i b = (rowGraph second).vertex j b := by
  cases b
  · exact congrArg (fun e : Chord s => e.val.1) same
  · exact congrArg (fun e : Chord s => e.val.2) same

theorem original_outlet
    (pay : Fin board.edges→Bool→Public S h W k attempts)
    (grows : ∀g,0<spill g→0<amount (names.symm (.inr (.inl g))))
    (i) (digit : Fin (cnt i)) (b : Bool) (loc : (rowGraph (L).family).vertex i b=whereAt) :
    ∃a:fiber,ProtocolRAMDateSpillPosition.originalSpillCodes S π board B pad pay i b=labelled S false a.val ∧
      (parts).owner (spillSeat S vtx a)=some (sourcePort (L).family cnt
        (v:=whereAt) ⟨(⟨i,digit⟩,b),by cases b <;>exact loc⟩) := by
  have positive:0<cnt i:=Nat.zero_lt_of_lt digit.isLt
  change 0<SettledMatrix.Layout.available (fun _:Fin board.edges=>0) spill
    (fun _:Empty=>0) (fun _:Empty=>0) ((L).num i) at positive
  cases row:(L).num i with
  | inl e=>simp [row,SettledMatrix.Layout.available] at positive
  | inr other=>
    cases other with
    | inr dead=>exact dead.elim
    | inl good=>
      let next:=names.symm (.inr (.inl good))
      have stock:0<spill good:=by simpa [row,SettledMatrix.Layout.available] using positive
      have edgeAt:ends next=(L).family i := by
        change sorted S π depth mark (names next)=(L).data.original ((L).num i)
        rw [Equiv.apply_symm_apply,row]
        rfl
      have atNext:(rowGraph ends).vertex next b=whereAt:=(vertex_of_chord_eq (first:=ends) (second:=(L).family) edgeAt b).trans loc
      obtain ⟨a,old,owner⟩:=outlet S π depth mark unique names vtx amount bound shape next b false (grows good stock) atNext
      refine ⟨a,?_,owner.trans (congrArg some (Subtype.ext (Prod.ext edgeAt rfl)))⟩
      change ProtocolRAMTurnOperands.printed S false (publicRoleFor S π pay (ProtocolRAMDateSpillPosition.source ((L).num i))) b false=_
      rw [row]
      change ProtocolRAMTurnOperands.printed S false (fun c=>half (.inr (.inl good),c)) b false=_
      simpa only [next,Equiv.apply_symm_apply] using old

theorem paid_outlet {r : ℕ} (ord : Fin r≃Σi,Fin ((L).routes i).length)
    (totalPaid : Fin board.edges→ℕ) (charged : ∀e,routeLoad B.ordinary spill e≤totalPaid e)
    (id : {e:Fin board.edges // 0<totalPaid e}→Catalogue S π depth mark)
    (aligned : ∀e,filledChord B.actual pad e.val=sorted S π depth mark (.inl (id e)))
    (paidHere : ∀e (pos:0<routeLoad B.ordinary spill e),0<amount (names.symm (.inl (id ⟨e,pos.trans_le (charged e)⟩))))
    (i) (u : Fin ((L).routes i).length) (digit : Fin (cnt i)) (b : Bool)
    (loc : (rowGraph (L).edge).vertex (((L).routes i).get u) b=whereAt) :
    let after:=ProtocolRAMTurnStepOrder.liveCode S true totalPaid
      (fun e on side=>.inl (HistoryRoles.paid S π depth mark unique (id ⟨e,on⟩,side)))
    ∃a:fiber,after (((L).routes i).get u) b=labelled S true a.val ∧
      (parts).owner (spillSeat S vtx a)=some (sourcePort (L).edge mass
        (datedHopPort (L).edge (L).routes cnt ord i u digit b whereAt loc)) := by
  intro after
  let e:=((L).routes i).get u
  have nonempty:0<cnt i:=Nat.zero_lt_of_lt digit.isLt
  have top:=NativeSlot.start_room (L).routes cnt ord i u nonempty
  rw [(L).measured] at top
  have hit:0<routeLoad B.ordinary spill e:=nonempty.trans_le ((Nat.le_add_left ..).trans top)
  let pos:=hit.trans_le (charged e)
  let next:=names.symm (.inl (id ⟨e,pos⟩))
  have edgeAt:ends next=(L).edge e:=by change sorted _ _ _ _ (names next)=_;rw [Equiv.apply_symm_apply];exact (aligned ⟨e,pos⟩).symm
  have atNext:(rowGraph ends).vertex next b=whereAt:=(vertex_of_chord_eq (first:=ends) (second:=(L).edge) edgeAt b).trans loc
  obtain ⟨a,old,owner⟩:=outlet S π depth mark unique names vtx amount bound shape next b true (paidHere e hit) atNext
  refine ⟨a,?_,owner.trans (congrArg some (Subtype.ext (Prod.ext ?_ rfl)))⟩
  · change ProtocolRAMTurnStepOrder.liveCode S true totalPaid _ e b = _
    simp only [ProtocolRAMTurnStepOrder.liveCode, pos, ↓reduceDIte]
    change ProtocolRAMTurnOperands.printed S true (fun c=>half (.inl (id ⟨e,pos⟩),c)) b false = _
    simpa only [next,Equiv.apply_symm_apply] using old
  · exact edgeAt.trans (congrArg (L).edge
      (datedHopPort_edge (L).edge (L).routes cnt ord i u digit b whereAt loc)).symm

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
