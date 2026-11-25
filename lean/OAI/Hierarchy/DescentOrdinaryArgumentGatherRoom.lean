import OAI.Hierarchy.DescentOrdinarySelectedMeasure
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! The ordinary gather's original input-address bounds, before inspecting any memory. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOrdinaryReferenceInputs
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
private theorem access_reindex {a b H G M w end_} (h : a=b) (ports : Ports a) (bank : Bank)
    (can : Accessible ports bank H G M w end_) : Accessible (h ▸ ports) bank H G M w end_ :=by
  cases h
  exact can
private theorem port_roundtrip {a b} (h : a=b) (ports : Ports a) :
    (h.symm ▸ (h ▸ ports : Ports b) : Ports a)=ports :=by cases h;rfl

variable (floor : ℕ) (matched : A.Match v floor)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "M₀" => A.clip.working
local notation "P₀" => A.ports v floor
local notation "L₀" => A.population v floor
local notation "R₀" => A.directory v floor matched

theorem gather_ports {w} (inlet : A.Room v floor w)
    (priorGroups : G₀=A.previous.groups) (bornH : v.bornBook.hosts=H₀)
    (bornG : v.bornBook.groups=G₀) (hosts : v.vector.hosts=H₀)
    (_radix : 0<v.vector.radix) (_lanes : 0<v.vector.lanes) (room : v.routedStart floor<2^w) :
    ∀pg low, let c:=(R₀).refs pg low
      (c.expr v.vector.hosts).Fits w (v.vectorStart floor) ∧
      (DescentOrdinaryAtomFieldRAM.masked c.tables c.want c.addr c.counts).Fits w (v.vectorStart floor) :=by
  have board : v.vectorStart floor<2^w:=by
    have h:=DescentOperandVectorArena.affine v.vector (v.vectorStart floor)
    change v.vector.endAddress (v.vectorStart floor)<2^w at room
    omega
  have origin : A.finish v floor≤v.vectorStart floor :=
    matched.atRefs.le.trans ((v.mount_order floor).1.trans (v.mount_order floor).2)
  have rank : (L₀).outBase≤v.vectorStart floor :=
    (show (L₀).outBase≤(L₀).endAddress from Nat.le_add_right ..).trans origin
  let block : Fin A.previous.blocks :=⟨0,by rw [matched.oldBlocks];exact Nat.two_pow_pos _⟩
  have before:=RoleControl.Layout.accessible_after (inlet.walk block) rank
  have dir : (R₀).rootPorts=P₀:=port_roundtrip matched.paths P₀
  have can (B : Bank) (fit : B.Fits w (v.vectorStart floor)) (size : H₀*chunks G₀ v.reference.lanes≤B.size) :
      Accessible (R₀).ports B H₀ G₀ v.reference.lanes w (v.vectorStart floor) :=by
    rw [matched.refPitch] at size ⊢
    apply access_reindex matched.paths P₀ B
    exact ⟨before.ids,before.idsRoom,before.roster,before.rosterRoom,before.offsets,before.offRoom,
      before.chunks,before.chunkRoom,fit,size⟩
  have C:=(v.refChart floor).rooms ((v.ref_end floor).le.trans (v.mount_order floor).2) board
  intro pg low
  dsimp only
  obtain ⟨old,birth⟩:=A.bank_places v floor matched priorGroups bornH bornG inlet board pg low
  have want : ((R₀).refs pg low).want.Fits w (v.vectorStart floor) :=by
    change ((L₀).want (R₀).rootPorts low).Fits w _
    rw [dir]
    have b:=(L₀).bank_fits inlet.ceiling ((L₀).askIndex low)
    exact ⟨⟨b.1,b.2.1,b.2.2.trans rank⟩,before.chunks,trivial⟩
  have venue : ((R₀).refs pg low).addr.Fits w (v.vectorStart floor) :=by
    obtain ⟨_,oldEnd,roleEnd,chipEnd,popEnd⟩:=A.inlet_order v floor
    let bank:=A.clip.fieldBank (v.signedEnd floor)
    have fit : bank.Fits w (A.priorStart v floor):=
      ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt inlet.venue.space,le_rfl⟩
    exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans (oldEnd.trans (roleEnd.trans (chipEnd.trans (popEnd.trans origin))))⟩,trivial⟩
  have count : ((R₀).refs pg low).counts.Fits w (v.vectorStart floor):=
    ⟨(L₀).result_fit board origin,trivial⟩
  have fitted:=(R₀).expr_fits pg low _ C (fun x=>can _ (old x).1 (old x).2)
    (fun x t j=>can _ (birth x t j).1 (birth x t j).2) want venue count
  have active:=(R₀).mask_fits pg low _ C want venue count
  rw [hosts]
  exact ⟨fitted,active⟩

theorem gather_room {w} (inlet : A.Room v floor w)
    (priorGroups : G₀=A.previous.groups) (bornH : v.bornBook.hosts=H₀)
    (bornG : v.bornBook.groups=G₀) (hosts : v.vector.hosts=H₀)
    (radix : 0<v.vector.radix) (lanes : 0<v.vector.lanes) (room : v.routedStart floor<2^w) :
    (R₀).refs.Room w (v.vectorStart floor) :=by
  refine ⟨radix,lanes,?_,room⟩
  intro pg low
  have fit:=(A.gather_ports v floor matched inlet priorGroups bornH bornG hosts radix lanes room pg low).1
  exact (ProtocolRAM.PrefixAgreement.inputEnd_of_fits _ fit).trans (by simp only [Layout.scratch,Layout.norm];omega)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
