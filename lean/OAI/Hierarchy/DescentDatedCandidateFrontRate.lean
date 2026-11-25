import OAI.Hierarchy.DescentContactDonorFrontRate
import OAI.Hierarchy.DescentDatedCandidateFront

namespace OAI
/-! # Word room for each hardware bank before the mixed receiver sheets -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetStemPackedIssue DescentSIMDLookup DescentDyadicSpan Filter
noncomputable section
variable {ι : ℕ→Type*} (v : ∀h,ι h→CandidateFront)

/-- An exponent for the serialized bits of a single table lookup. -/
def Packed (f : ∀h,ι h→ℕ) :=∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,f h i≤K*h
private theorem power {f : ∀h,ι h→ℕ} (fitted : Packed f) : Bounded (fun h i=>2^(f h i)) :=by
  obtain ⟨k,hk⟩:=fitted
  exact Bounded.pow_of_linear hk

structure ScalarRoom : Prop where
  oldHosts : Bounded (fun h i=>(v h i).peer.oldHosts)
  shapes : Bounded (fun h i=>(v h i).peer.shapes)
  degree : Bounded (fun h i=>(v h i).peer.oldDegree)
  evidence : Bounded (fun h i=>(v h i).peer.evidence)
  groups : Bounded (fun h i=>(v h i).peer.groups)
  lanes : Bounded (fun h i=>(v h i).peer.lanes)
  oldGroups : Bounded (fun h i=>(v h i).oldGroups)
  oldLanes : Bounded (fun h i=>(v h i).oldLanes)
  oldKeys : Bounded (fun h i=>(v h i).oldKeysCount)
  cap : Bounded (fun h i=>(v h i).wireCap)
  tickets : Bounded (fun h i=>(v h i).oldTicketCount)
  live : Bounded (fun h i=>(v h i).newHosts)
  project : Bounded (fun h i=>(v h i).projectionCount)
  blocks : Bounded (fun h i=>(v h i).blocks)
  signed : Bounded (fun h i=>(v h i).signedQueries)
  donor : DescentContactDonorFront.Shape.ScalarRoom (fun h i=>(v h i).donor)
  contact : DescentContactPreROM.Layout.ScalarRoom (fun h i=>(v h i).contact)
  key0 : Packed (fun h i=>let u:=v h i;DescentResetStemKey.unit u.peer.oldDegree u.stemField*u.oldLanes)
  key1 : Packed (fun h i=>let u:=v h i;DescentResetStemKey.unit u.peer.oldDegree u.stemField*u.peer.lanes)
  port : Packed (fun h i=>let u:=v h i;u.privateBits*(u.wireCap*5)*u.oldLanes)
  sign : Packed (fun h i=>let u:=v h i;(u.stemField+2)*u.oldLanes)
  peer : Packed (fun h i=>(v h i).peer.bits*(v h i).peer.evidenceLanes)
  trunk : Packed (fun h i=>(v h i).peer.evidenceLanes)
  oldWord : Packed (fun h i=>let u:=v h i;u.projectionBits*u.oldLanes)
  newWord : Packed (fun h i=>let u:=v h i;u.projectionBits*u.blocks*u.peer.lanes)
  «meta» : Packed (fun h i=>(v h i).metaBits*7)
  mux : Packed (fun h i=>let u:=v h i;DescentResetStemMux.unit (u.stemField+2) (u.metaBits*7)*u.peer.lanes)
  joined : Packed (fun h i=>let u:=v h i;(u.metaBits*7+u.metaBits)*u.peer.lanes)

theorem rate (r : ScalarRoom v) : Bounded (fun h i=>(v h i).trunkEnd 0) := by
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  have raw:=r.oldHosts.mul r.shapes
  have chunkBound {x y : ∀h,ι h→ℕ} (a : Bounded x) (b : Bounded y) :
      Bounded (fun h i=>chunks (x h i) (y h i)) :=
    (a.add b).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have priorRows:=r.oldHosts.mul (chunkBound r.oldGroups r.oldLanes)
  have rail:=chunkBound r.groups r.lanes
  have oldKey:=(((r.degree.add (c 2)).add (c 2)).mul ((c 2).mul (power r.key0)))
  have prior : Bounded (fun h i=>(v h i).oldKeys 0) :=by
    simpa only [oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start,
      DescentResetStemKey.words,DescentDyadicSpan.span,Nat.zero_add] using ((oldKey.add (r.oldKeys.mul priorRows)).add priorRows.padded)
  have priv:=((c 2).mul raw.padded).add (r.cap.mul (r.shapes.mul (power r.port)).padded)
  have pm : Bounded (fun h i=>(v h i).privateChip 0) :=by
    exact prior.add priv
  have extra:=(r.shapes.mul (power r.sign)).padded
  have pos : Bounded (fun h i=>(v h i).positiveStem 0) :=(pm.add raw.padded).add extra
  have neg : Bounded (fun h i=>(v h i).negativeStem 0) :=(pos.add raw.padded).add extra
  have four : Bounded (fun h i=>(v h i).rawTablesEnd 0) := (neg.add raw.padded).add (r.shapes.mul (power r.trunk)).padded
  have donor:=DescentContactDonorFront.Shape.rate _ r.donor
  have before : Bounded (fun h i=>(v h i).donorEnd 0) :=by
    apply (four.add donor).of_le
    intro h i
    rw [donorEnd,(v h i).donor.translate];exact le_rfl
  have cc:=DescentContactPreROM.Layout.rate _ r.contact
  have contact : Bounded (fun h i=>(v h i).contacts 0) :=by
    apply (before.add cc).of_le
    intro h i
    rw [contacts,(v h i).contact.translate]
  have p0:=PeerAperture.bounded (fun h i => (v h i).peer) r.oldHosts r.shapes r.degree r.evidence r.groups r.lanes r.peer
  have start : Bounded (fun h i=>(v h i).parentStart 0) :=by
    apply ((contact.add p0).add r.live).of_le
    intro h i
    rw [parentStart,(v h i).peer.extent];rfl
  have directory:=DescentResetParentAperture.bounded raw r.live
  have parentStop : Bounded (fun h i=>(v h i).parentEnd 0) :=by
    apply (start.add directory).of_le
    intro h i
    rw [parentEnd,DescentResetParentAperture.affine];rfl
  have pre:=DescentResetStemProject.rates r.project r.oldHosts r.groups r.blocks r.oldLanes r.lanes r.oldWord r.newWord
  have projectedBound : Bounded (fun h i=>(v h i).projected 0) :=by
    apply (parentStop.add pre).of_le
    intro h i
    rw [projected,DescentResetStemProject.extent]
  have receive : Bounded (fun h i=>(v h i).mixed 0) :=
    Mixed.bounded _ _ _ _ _ _ _ _ _ _ _ _ projectedBound r.degree r.tickets r.oldHosts r.live r.blocks r.signed rail
      (power r.key1) (power r.meta) (power r.mux)
  have rows:=(r.live.mul rail).padded
  have gather:=((receive.add r.live.padded).add (r.live.padded.add ((c 2).mul rows))).add rows
  exact gather.add ((c 3).mul (power r.joined))

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
