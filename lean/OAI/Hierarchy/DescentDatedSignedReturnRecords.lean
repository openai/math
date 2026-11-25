import OAI.Hierarchy.DescentDatedSignedLocalRecords
import OAI.Hierarchy.DescentOrdinaryReceivedRaw

namespace OAI
/-! The mixed remote comparison fields are read through the authentic old
halo and the two prior short paths, in the common dated RAM. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open DescentParallelBase DescentParallelBase.ParentFilter DescentHaloWalkRAM DescentOrdinarySignedMeta
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ}
variable (s:SignedExtent) (I:s.Input) (base:ℕ) (m:Memory w)
local notation "P"=>s.reach
local notation "Q"=>s.lowSites
local notation "b"=>s.fieldBits
local notation "M"=>s.lanes
local notation "sheet"=>s.installed I base m
local notation "tk" => SourceReturn.RAM.ROM.table P Q b M (s.routeStart base)
local notation "tf" => DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.forward P Q) M) s.forwardBits (s.forwardBase base) id
local notation "tr" => DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.finish P Q) M) s.finishBits (s.backBase base) id
local notation "bank" c:arg f:arg l:arg r:arg => subbank (s.projectedStart base) s.oldSlab (s.projectedId (s.sourceAt c r) f l)
local notation "returned" c:arg f:arg =>subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)

/-- The three original short observations at the donor, preceding the
new-source comparison. Finite lookup rows use the one-based public token. -/
structure RouteDigits (s:SignedExtent) where
  forward:Fin s.blocks→Fin s.residentSlots→Fin s.priorHosts→Fin s.groups→Cell (Packed.bits s.reach)
  low:Fin s.blocks→Fin s.residentSlots→Fin s.priorHosts→Fin s.groups→Cell (Packed.bits s.lowSites)
  back:Fin s.blocks→Fin s.residentSlots→Fin s.priorHosts→Fin s.groups→Cell (Packed.bits s.reach)
variable {s} in
def RouteDigits.choice (v:s.RouteDigits) (x:Fin s.blocks) (o:Fin s.residentSlots) (h:Fin s.priorHosts) (g:Fin s.groups):Option (Fin s.routeTotal):=do
  let p←Packed.readToken P (v.forward x o h g)
  let low:=(v.low x o h g).val
  let back:=(v.back x o h g).val
  if room:low<Q ∧ back<P then some (SourceReturn.RAM.key p ⟨low,room.1⟩ ⟨back,room.2⟩) else none

variable {s} in
theorem RouteDigits.measures_choice (v:s.RouteDigits) (x:Fin s.blocks) (o:Fin s.residentSlots) (h:Fin s.priorHosts) (g:Fin s.groups):
    SourceReturn.Query.finish P Q (SourceReturn.Query.forward P Q (v.forward x o h g) (v.low x o h g)) (v.back x o h g)=Packed.token (v.choice x o h g):=by
  cases found:Packed.readToken P (v.forward x o h g) with
  | none=>simp [RouteDigits.choice,SourceReturn.Query.forward,SourceReturn.Query.finish,found,Packed.token_back]
          rfl
  | some p=>
    by_cases lo:(v.low x o h g).val<Q <;> by_cases back:(v.back x o h g).val<P <;>
      simp [RouteDigits.choice,SourceReturn.Query.forward,SourceReturn.Query.finish,found,lo,back,Packed.token_back] <;> try rfl
    let l : Fin Q := ⟨(v.low x o h g).val,lo⟩
    let r : Fin P := ⟨(v.back x o h g).val,back⟩
    change Packed.token (some (SourceReturn.RAM.key (finProdFinEquiv.symm (finProdFinEquiv (p,l))).1
      (finProdFinEquiv.symm (finProdFinEquiv (p,l))).2 r)) = _
    rw [Equiv.symm_apply_apply]
    rfl

variable {s} in
def RouteDigits.Earlier (v:s.RouteDigits) (I:s.Input) (m:Memory w):Prop:=
  (∀x o,Source (I.donorForward x o) (v.forward x o) s.lanes m) ∧
  (∀x o,Source (I.donorLow x o) (v.low x o) s.lanes m)
variable (ok:s.Fits I base w) (space:s.roof base<2^w)
variable (walks:Fin s.priorHosts→Fin s.reach→Option (Fin s.priorHosts))
variable (v:s.RouteDigits)
local notation "revChart"=>DescentPackedChildNeighbor.SIMD.ROM.layout (s.reverseBase base) P s.reverseBits s.reverseBits M (Nat.clog 2 s.oldSlab) I.reversePath

include ok space in
theorem counted_back (R:Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts))
    (prior:v.Earlier I m) (x:Fin s.blocks) (o:Fin s.residentSlots)
    (old:(I.donorForward x o).Fits w base) (early:I.reversePath.Fits w base) (length:s.priorHosts*P≤I.reversePath.size)
    (issued:∀h p,m (I.reversePath.base+(DescentHaloWalkRAM.row h p).val)=(Rebase.value R .path h p:Word w))
    (room:DescentPackedChildNeighbor.SIMD.Room revChart (I.donorForward x o) s.priorHosts s.groups s.reverseBits s.reverseBits M w (s.tailStart base))
    (token:∀h g,Packed.token (Packed.readToken P (v.forward x o h g))=v.forward x o h g)
    (back:∀h g,v.back x o h g=SourceReturn.Query.packedRoute R h (Packed.readToken P (v.forward x o h g))):
    Source (s.backDigit I base x o) (v.back x o) M sheet:=by
  have priorFrame:∀a<base,sheet a=m a:=(s.installed_words I base m ok space).2
  have hdr:=SourceReturn.Query.raw_reads R I.reversePath m issued
  let vals:=SourceReturn.Query.route R
  have lit (u:DescentPackedChildNeighbor.SIMD.ROM.Index P s.reverseBits s.reverseBits M s.priorHosts s.groups):
      sheet (DescentPackedChildNeighbor.SIMD.ROM.address (s.reverseBase base) u)=(DescentPackedChildNeighbor.SIMD.ROM.word u:Word w):=by
    let i:=DescentPackedChildNeighbor.SIMD.ROM.index P s.reverseBits s.reverseBits M s.priorHosts s.groups u
    have hi:s.mapIndices+i.val < s.mapWords:=by
      change _ < s.mapIndices+(_+_);have less:=i.isLt;omega
    have hw:=s.funded_map I base m ok space ⟨s.mapIndices+i.val,hi⟩
    rw [DescentPackedChildNeighbor.SIMD.ROM.address_eq]
    simpa [reverseBase,maps,Nat.not_lt.mpr (Nat.le_add_right s.mapIndices i.val),Nat.add_assoc,i,
      DescentPackedChildNeighbor.SIMD.ROM.numbers,(DescentPackedChildNeighbor.SIMD.ROM.index P s.reverseBits s.reverseBits M s.priorHosts s.groups u).isLt] using hw
  have store:DescentPackedChildNeighbor.SIMD.Stored revChart s.priorHosts s.groups s.reverseBits s.reverseBits M vals sheet:=by
    constructor
    · intro h j
      have hlt:h.val*P+j.val < s.priorHosts*P:=by
        exact (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
      have earlier : I.reversePath.base+(h.val*P+j.val) < base := by
        have := early.2.2
        omega
      exact (priorFrame _ earlier).trans (hdr h j)
    · intro t;exact (lit (.inr (.inr (.inr (.inr (row s.priorHosts s.groups M t)))))).trans (by simp [DescentPackedChildNeighbor.SIMD.ROM.word])
    · intro t;exact lit (.inl t)
    · intro j t;exact lit (.inr (.inl (j,t)))
    · constructor
      · intro t;exact lit (.inr (.inr (.inl t)))
      · intro t;exact lit (.inr (.inr (.inr (.inl t))))
  have dig:=SignedPrefix.from_prior m sheet _ _ priorFrame old (prior.1 x o)
  have good:=DescentPackedChildNeighbor.SIMD.measures revChart (I.donorForward x o) (s.tailStart base) room vals sheet store _ dig (List.finRange P)
  have agree:(fun h g=>DescentPackedChildNeighbor.SIMD.lookup (vals h) (v.forward x o h g) (List.finRange P))=v.back x o:=by
    funext h g
    rw [back]
    exact congrArg (fun cell=>DescentPackedChildNeighbor.SIMD.lookup (vals h) cell (List.finRange P)) (token h g).symm
  rw [←agree]
  exact good

include ok space in
theorem returned_records (prior:v.Earlier I m)
    (access:∀x o,(I.donorForward x o).Fits w base ∧ (I.donorLow x o).Fits w base)
    (returnRead:∀x o,Source (s.backDigit I base x o) (v.back x o) M sheet)
    (fa:∀x o,DescentPackedZip.Fits tf (I.donorForward x o) (I.donorLow x o) (Packed.bits P) (Packed.bits Q) M (s.tailStart base) w)
    (fb:∀x o,DescentPackedZip.Fits tr ((tf).read (I.donorForward x o) (I.donorLow x o)) (s.backDigit I base x o)
      (Packed.bits (P*Q)) (Packed.bits P) M (s.tailStart base) w)
    (real:Mounted I.ports walks m s.groups M)
    (early:∀(c:s.Consumer) (f:Fin 11) (l:Fin Q) (r:Fin P),Accessible I.ports (bank c f l r) s.priorHosts s.groups M w (s.tailStart base))
    (priorBank:Bank) (priorPorts:Accessible I.ports priorBank s.priorHosts s.groups M w base)
    (storage:Fin Q→s.Socket→Fin 11→Fin s.priorHosts→Fin s.groups→Cell b)
    (reads:∀(z:s.Socket) (f:Fin 11) (l:Fin Q),Reads (subbank (s.projectedStart base) s.oldSlab (s.projectedId z f l)) (storage l z f) M sheet)
    (geom:∀(c:s.Consumer) (f:Fin 11) (j:Fin s.routeTotal),DescentPackedZip.Fits (tk j) (s.routeQuery I base c.1.1 (s.priorSlot c).2)
      (peerExpr I.ports (bank c f (SourceReturn.RAM.parts j).2.1 (SourceReturn.RAM.parts j).2.2) s.priorHosts (SourceReturn.RAM.parts j).1)
      (Packed.bits s.routeTotal) b M (returned c f).base w)
    (top:∀(c:s.Consumer) (f:Fin 11),(returned c f).base+s.oldSlab<2^w)
    (c:s.Consumer) (f:Fin 11) (remote:c.1.2.val=2):
    Reads (returned c f) (SourceReturn.RAM.output walks (fun l r=>storage l (s.sourceAt c r) f) (v.choice c.1.1 (s.priorSlot c).2)) M sheet:=by
  let x:=c.1.1
  let o:=(s.priorSlot c).2
  have kept:∀a<base,sheet a=m a:=(s.installed_words I base m ok space).2
  have mounted:=SourceReturn.mounted_before I.ports walks m sheet real priorBank priorPorts kept
  have q:=SourceReturn.Query.source tf tr (I.donorForward x o) (I.donorLow x o) (s.backDigit I base x o) (s.tailStart base) sheet
    (v.forward x o) (v.low x o) (v.back x o) (fa x o) (fb x o)
    (s.static_forward I base m ok space) (s.static_return_key I base m ok space)
    (SignedPrefix.from_prior m sheet _ _ kept (access x o).1 (prior.1 x o))
    (SignedPrefix.from_prior m sheet _ _ kept (access x o).2 (prior.2 x o))
    (returnRead x o)
  simp_rw [v.measures_choice] at q
  have br (j:Fin s.routeTotal):=peerSource I.ports (bank c f (SourceReturn.RAM.parts j).2.1 (SourceReturn.RAM.parts j).2.2)
    (s.tailStart base) (early c f _ _) walks sheet mounted _ (reads (s.sourceAt c (SourceReturn.RAM.parts j).2.2) f _) (SourceReturn.RAM.parts j).1
  have done:=SourceReturn.RAM.run_sources walks (fun l r=>storage l (s.sourceAt c r) f) (v.choice x o)
    tk I.ports (fun l r=>bank c f l r) (s.routeQuery I base x o) (returned c f) sheet (geom c f)
    (s.static_return I base m ok space) q br (top c f)
  intro row
  let n:=DescentSIMDLookup.row s.priorHosts s.groups M row
  have read:=done.2.1 row
  rw [ProtocolRAMGeneratedWrite.read_image] at read
  refine (s.funded_return I base m ok space c f n).trans ?_
  simpa only [routed,ite_eq_left remote,n,x,o] using read

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
