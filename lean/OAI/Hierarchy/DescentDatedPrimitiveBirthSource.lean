import OAI.Hierarchy.DescentPhysicalRoleRooms
import OAI.Hierarchy.DescentPhysicalResetRoleFrames
import OAI.Hierarchy.DescentPrimitiveBirthCases

namespace OAI
/-! # Direct readings at the installed primitive instruction after the physical reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 900000
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : FinalInputs u)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "ds" => (v).actor.directory ((v).middle.stop b)
local notation "venue" => (v).venue
local notation "fund" => (v).fundedEnd b
local notation "stop₀" => (v).finalEnd b
local notation "roleAt" => (v).fullEnd b
local notation "movedAt" => (v).roleEnd b
local notation "classAt" => (v).classEnd b
local notation "bornAt" => (v).birthEnd b
local notation "meta" => (v).primitiveEnd b
local notation "T" => (v).metadata.chart
local notation "B" => (v).birth
local notation "P" => (B).placement
local notation "C" => (v).primitive.chart

theorem low_class (mid : Memory w) (fit : z.Room) (j : ℕ) (low : j<roleAt) :
    z.classImage mid j=z.venueImage mid j:=by
  have move:roleAt≤ movedAt:=by rw [ResetOutput.roleEnd,(v).roleTransfer.translate];exact Nat.le_add_right ..
  have cls:movedAt≤classAt:=((v).actorClass.guard movedAt).1.trans ((v).actorClass.guard movedAt).2
  have framed:=z.role_input_frames fit mid
  exact (framed.1 j (Or.inl (low.trans_le (move.trans cls)))).symm.trans (framed.2.2 j (Or.inl low))

private theorem higher {page : Bank} {p q : ℕ} (h : page.Fits w p) (up : p≤q) : page.Fits w q :=
  ⟨h.1,h.2.1,h.2.2.trans up⟩

theorem birth_operand_rooms (ready : u.Ready) (fit : z.Room) (blocks : (T).blocks≤2^(venue).next.k) :
    (classWord u).Fits w classAt ∧ (∀x,(paid u x).Fits w classAt) ∧
       (∀x n j,(z.spans x n j).Fits w classAt) ∧ bornAt<2^w:=by
  obtain ⟨_f,actorStart,actorEnd,trunkEnd,massEnd,jointEnd,privateEnd,maskedEnd,sectionEnd⟩:=ready.ordered
  obtain ⟨fundLo,venueLo⟩:=(v).complete_after b
  obtain ⟨_d₁,_d₂,venueEnd⟩:=(venue).after fund
  have moveLo:roleAt≤ movedAt:=by
    change _≤(v).roleTransfer.endAddress roleAt
    rw [(v).roleTransfer.translate];exact Nat.le_add_right ..
  have classLo:movedAt≤classAt:=by
    change _≤(v).actorClass.endAddress movedAt
    rw [(v).actorClass.translate];exact Nat.le_add_right ..
  have bornLo:classAt≤bornAt:=by
    change _≤(v).birth.endAddress classAt
    rw [(v).birth.translate];exact Nat.le_add_right ..
  have primLo:bornAt≤ meta:=by
    change _≤(v).primitive.endAddress bornAt
    rw [(v).primitive.translate];exact Nat.le_add_right ..
  have endLo:meta≤a.endAddress floor:=by
    change _≤(v).metadata.endAddress meta
    rw [(v).metadata.translate];exact Nat.le_add_right ..
  have room:=fit.endFits
  have classFit:classAt<2^w:=by omega
  have birthFit:bornAt<2^w:=by omega
  obtain ⟨_,_,_,oldCount,oldInv⟩:=(ds).fits ready.actor.room
  have actorBefore:(ds).endAddress≤ movedAt:=by change (v).actorEnd b≤ movedAt;omega
  have count:=higher oldCount actorBefore
  have inv:=higher oldInv actorBefore
  have remapRoom: (v).actorClass.next movedAt≤classAt:=((v).actorClass.guard movedAt).2
  have beforePage : movedAt≤(v).actorClass.next movedAt:=((v).actorClass.guard movedAt).1
  have safe:=((v).actorClass.remap movedAt).book_fits (ds).count (ds).inverse
    (higher count beforePage) (higher inv beforePage) classFit
  have classWord:(FinalInputs.classWord u).Fits w classAt:=
    ((v).actorClass.remap movedAt).fits safe _
      ⟨higher ((v).actorClass.page_fits movedAt classFit) remapRoom,trivial⟩
  have paid (x : Fin (T).blocks) : (FinalInputs.paid u x).Fits w classAt:=by
    let x' : Fin (2^(venue).next.k):=⟨x.val,x.isLt.trans_le blocks⟩
    have orig:=(fit.successor.return_.paid x').1
    have toClass:(venue).venueStart fund≤classAt:=venueEnd.trans (moveLo.trans classLo)
    exact ⟨higher orig toClass,trivial⟩
  have span (x node j) : (z.spans x node j).Fits w classAt:=
    ProtocolRAMGeneratedWrite.fits_mono _ (by omega : stop₀≤classAt) (z.span_at ready x node j)
  exact ⟨classWord,paid,span,birthFit⟩

/-- Earlier roster, paid population and cable spans determine both live primitive inputs on
the memory used by the final instruction. The old root pages are the original acquired pages. -/
theorem birth_sources {U : ℕ} (mid : Memory w) (ready : u.Ready) (fit : z.Room) (blocks : (T).blocks≤2^(venue).next.k)
    (depth : (B).Population) (original : (B).Original) (read : (B).Observed z.guards (z.classImage mid) depth original)
    (pos : 0<(B).sourceLanes) (name : Fin U→Fin (P).sparse) (count : z.venueImage mid (ds).count.base=(U:Word w))
    (inverse : ∀i:Fin U,z.venueImage mid ((ds).inverse.base+i.val)=((name i).val:Word w)) (narrow : U<2^w)
    (hosts : (P).newHosts≤2^w) (saved : U≤(ds).inverse.size)
    (x : Fin (C).blocks) (n : Fin (C).nodes)
    (kind : Fin (P).newHosts→Fin (P).groups→Cell (B).classBits)
    (quantity : Fin (P).newHosts→Fin (P).groups→Cell (B).paidBits)
    (ranges : Fin (B).arguments→Fin (P).newHosts→Fin (P).groups→Cell (B).spanBits)
    (rack : Source (classWord u) kind (P).lanes (z.classImage mid))
    (paid_ : Source (paid u (x.cast z.censusBlocks)) quantity (P).lanes (z.venueImage mid))
    (cable : ∀j,Source (z.spans (x.cast z.censusBlocks) (n.cast z.censusNodes) (j.cast z.birthArgs))
      (ranges j) (P).lanes (z.venueImage mid)) :
    Source (z.roles.fresh x n) (fun h g=>(B).raw (n.cast z.birthNodes) (kind h g) (quantity h g)
       (fun j=>ranges j h g) (fun q=>(B).rootActual depth original name (n.cast z.birthNodes) (x.cast z.birthBlocks) q h g))
        (P).lanes (z.roleInput mid) ∧
    Source (z.roles.relay x n) (fun h g=>(B).tagRelay ((B).admitted (n.cast z.birthNodes) (kind h g) (quantity h g)))
        (P).lanes (z.roleInput mid):=by
  obtain ⟨fc,fp,fs,roof⟩:=z.birth_operand_rooms ready fit blocks
  have ⟨fundLo,venueLo⟩:=(v).complete_after b
  have done:stop₀≤roleAt:=fundLo.trans venueLo
  have preCount:=fit.roleMove.countFit.2.2
  have preInv:=fit.roleMove.inverseFit.2.2
  have measured (i : Fin U):z.classImage mid ((ds).inverse.base+i.val)=((name i).val:Word w):=by
    rw [z.low_class mid fit _ (by have hi:=i.isLt.trans_le saved;change (ds).inverse.base+(ds).inverse.size≤roleAt at preInv;omega)]
    exact inverse i
  have size : z.classImage mid (ds).count.base=(U:Word w):=by
    have positive:0<(ds).count.size:=Nat.two_pow_pos _
    rw [z.low_class mid fit _ (by change (ds).count.base+(ds).count.size≤roleAt at preCount;omega)]
    exact count
  have payFit (i : Fin (T).blocks) : (paid u i).Fits w roleAt:=by
    let x' : Fin (2^(venue).next.k):=⟨i.val,i.isLt.trans_le blocks⟩
    have toRole:=(venue).after fund
    exact ⟨higher (fit.successor.return_.paid x').1 toRole.2.2,trivial⟩
  have fixed {ah : ℕ} {exp : Expr} (A : Fin (P).newHosts→Fin (P).groups→Cell ah)
      (bound : exp.Fits w roleAt) (seen : Source exp A (P).lanes (z.venueImage mid)) :
      Source exp A (P).lanes (z.classImage mid):=by
    intro i
    exact (eval_below exp _ _ _ bound (z.low_class mid fit)).trans (seen i)
  exact (B).issued classAt z.guards (ds).count (ds).inverse (z.classImage mid) fit.birth roof depth original read pos
    name size measured narrow hosts saved (n.cast z.birthNodes) (x.cast z.birthBlocks) (classWord u) (paid u (x.cast z.censusBlocks))
    _ kind quantity ranges fc (fp _) (fun j=>fs _ _ _) rack (fixed _ (payFit _) paid_)
      (fun j=>fixed _ (by exact ProtocolRAMGeneratedWrite.fits_mono _ done (z.span_at ready _ _ _)) (cable j))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
