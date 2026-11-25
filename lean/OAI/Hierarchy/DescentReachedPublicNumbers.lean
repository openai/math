import OAI.Hierarchy.DescentOriginalPublicEmitter
import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentReachedMixedHeaders
import OAI.Hierarchy.DescentOriginalSectorRetention
import OAI.Hierarchy.DescentResetStemOriginalSlots
import OAI.Hierarchy.DescentResetPublicParentPosted
import OAI.Hierarchy.DescentPhysicalRankSheetIntake

namespace OAI
/-! # Trunk and direct original numbers from the measured public fields and earlier signed donors -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

open DescentResetRankedWindows DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
local notation "s₀" => (v₀).sheets
variable (bound : used≤(s₀).hosts) (geo : PhysicalReset.DateInputs.SheetGeometry I)
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "gx" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "bx" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "cx" => geo.contacts.trans (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
local notation "px" => geo.privates.trans (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "meter" => DescentResetFieldAssembler.raw (s₀).metaBits


open DescentResetOriginalSlots
local notation "sx" => (v₀).sheets
local notation "area" => ((v₀).remap base₀).endAddress
local notation "o" => (sx).original area
local notation "blk" => 2^k
local notation "gt" => S.groupCount (i+1)
local notation "units" => originalBits D k n ht (A).cap (programCount ctl.board ht) g
local notation "T₀" => I.numbered.stemSide area
local notation "P₀" => I.numbered.publicSide area
local notation "D₀" => I.numbered.privateSide area
local notation:max "packed" x:arg j:arg => (.lookup (bank o (sx).rows (sx).candidates x j) .row:Expr)
local notation:max "start" m:arg => I.masked.image (I.privateResult m)
local notation:max "Pout" m:arg => (P₀).dst (I.numbered.prefixOutput area (start m))
local notation:max "Tout" m:arg => (T₀).image (Pout m)

variable (hx : (v₀).receiver.blocks=blk) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
local notation "groupAt" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockAt" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation:max "values" x:arg j:arg => (fun v g₀=>(actualParentNumber B rack₀ x j v g₀:Cell units))
local notation:max "word" x:arg j:arg => (fun v (gr:Fin (sx).groups)=>(actualParentNumber B rack₀ x j v (gr.cast groupAt):Cell units))
local notation:max "reg" x:arg j:arg => shaped hx hs hc hp I.sectors.original x j

open DescentResetPublicParentWord
local notation:max "pre" m:arg => I.numbered.prefixOutput area (start m)
local notation "orig₀" => I.numbered
local notation:max "xAt" x:arg => Fin.cast (blockAt).symm x
local notation:max "jAt" j:arg => Fin.cast hc.symm j
local notation "trunkIdx" => pos (.inr (.inl 0))
local notation:max "contactIdx" j:arg => pos (.inr (.inr (.inl j)))
local notation:max "trueZero" x:arg => (fun (_:Fin (sx).hosts) (gr:Fin (sx).groups)=>decide (gr.val=0 ∧ (x).val=0))
local notation:max "metaIn" x:arg j:arg => (fun (h:Fin (sx).hosts) (gr:Fin (sx).groups)=>actualMeta B rack₀ x j h (gr.cast groupAt))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
open DescentContactDonorSelection DescentParallelBase

private theorem publicValueRead {hosts groups bits₁ bits₂ batchSize wordSize : ℕ}
    {op : Expr} {states : Memory wordSize}
    (lhs rhs : Fin hosts → Fin groups → ℕ) (sameWidth : bits₁ = bits₂)
    (sameValue : ∀ v groupIx, lhs v groupIx = rhs v groupIx)
    (read : Source op (fun v groupIx => (lhs v groupIx : Cell bits₁)) batchSize states) :
    Source op (fun v groupIx => (rhs v groupIx : Cell bits₂)) batchSize states := by
  subst bits₂
  simpa only [sameValue] using read

set_option maxHeartbeats 800000 in
theorem trunk_original_output (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    (fn : (P₀).fn=publicFn B) (rb : I.numbered.resultBits=units) (mb : 0<(sx).metaBits) (zb : 0<(sx).zeroBits)
    (observed : ∀x:Fin blk,Source ((P₀).old.meta (xAt x) 0)
      (fun v groupIx=>DescentResetFieldAssembler.raw (sx).metaBits ((metaIn x trunkIdx) v groupIx)) (sx).lanes (pre m))
    (zero : ∀x:Fin blk,Source ((P₀).old.zero (xAt x))
      (fun v groupIx=>(((trueZero x) v groupIx).toNat:Cell (sx).zeroBits)) (sx).lanes (pre m))
    (halo palette : Fin blk→Fin (sx).hosts→Fin (sx).groups→Cell (sx).shortBits)
    (self : ∀x,Source ((P₀).old.self (xAt x)) (halo x) (sx).lanes (pre m))
    (shape : ∀x,Source ((P₀).old.shape (xAt x)) (palette x) (sx).lanes (pre m))
    (reads : ∀x v t,rack₀ v=some t→∀gr,
      let u:=((gr.cast groupAt,t),x)
      (halo x v gr).val=haloNumber B u (receiverRoot B u).1 ∧
      (palette x v gr).val=((Z).rawHostRank T vertex t).val%shelf) :
    ∀x:Fin blk,Source (packed x.val (I.numbered.publicShelf 0).val) (word x trunkIdx) (sx).lanes (Pout m):=by
  intro x
  have blank:(P₀).fn 0 0 0 0 0=0:=by rw [fn];rfl
  have seen:=(P₀).trunk_output ok.numbers.public_ (pre m) (xAt x) (metaIn x trunkIdx) (trueZero x)
    (halo x) (palette x) mb zb blank (observed x) (zero x) (self x) (shape x)
  have index : trunkIdx=trunkCandidate B:=Fin.ext (CandidateSheet.trunk_val ..)
  have value (v : Fin (sx).hosts) (gr : Fin (sx).groups) :
      (P₀).fn 0 ((metaIn x trunkIdx) v gr).live.toNat ((trueZero x) v gr).toNat
        (halo x v gr).val (palette x v gr).val=actualParentNumber B rack₀ x trunkIdx v (gr.cast groupAt):=by
    rw [fn,index];cases hv:rack₀ v with
    | none=>simp [actualMeta,actualParentNumber,hv,Meta.blank,publicFn,trunkWord]
    | some t=>
      obtain ⟨h₁,h₂⟩:=reads x v t hv gr
      have raster := trunk_raster_word B ((gr.cast groupAt,t),x)
      rw [public_zero B ((gr.cast groupAt,t),x)] at raster
      simp only [publicFn,ite_true,actualMeta,actualParentNumber,hv,Option.elim_some,h₁,h₂]
      exact raster
  exact publicValueRead
    (fun v gr => (P₀).fn 0 ((metaIn x trunkIdx) v gr).live.toNat ((trueZero x) v gr).toNat
      (halo x v gr).val (palette x v gr).val)
    (fun v gr => actualParentNumber B rack₀ x trunkIdx v (gr.cast groupAt)) rb value seen

private theorem visits_cast {N N' a b : ℕ} (axis : N=N') (d : ℕ) (own : Fin N→Cell a) (cargo : Fin N→Cell b) :
    visits d own cargo=visits d (fun j:Fin N'=>own (j.cast axis.symm)) (fun j:Fin N'=>cargo (j.cast axis.symm)):=by
  subst N';rfl

set_option maxHeartbeats 800000 in
theorem contact_original_output (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    (fn : (P₀).fn=publicFn B) (rb : I.numbered.resultBits=units) (mb : 0<(sx).metaBits) (zb : 0<(sx).zeroBits)
    (domain : I.numbered.signedSlots=L*(2*(A).cap))
    (request : ∀j,(P₀).req (jAt j)=donor_query B j)
    (observed : ∀(x:Fin blk)(j:Fin (contactCount B)),Source ((P₀).old.meta (xAt x) (jAt j).succ)
      (fun v gr=>DescentResetFieldAssembler.raw (sx).metaBits ((metaIn x (contactIdx j)) v gr)) (sx).lanes (pre m))
    (zero : ∀x:Fin blk,Source ((P₀).old.zero (xAt x))
      (fun v gr=>(((trueZero x) v gr).toNat:Cell (sx).zeroBits)) (sx).lanes (pre m))
    (own : Fin blk→Bool→Fin I.numbered.signedSlots→Fin (sx).hosts→Fin (sx).groups→Cell (sx).selectorBits)
    (cargo : Fin blk→Bool→Fin 2→Fin I.numbered.signedSlots→Fin (sx).hosts→Fin (sx).groups→Cell (sx).shortBits)
    (labels : ∀x side i,Source ((P₀).old.label (xAt x) side i) (own x side i) (sx).lanes (pre m))
    (cargos : ∀x side flag i,Source ((P₀).old.cargo (xAt x) side flag i) (cargo x side flag i) (sx).lanes (pre m))
    (origin : ∀x v t,rack₀ v=some t→∀(gr:Fin (sx).groups),
      let u:=((gr.cast groupAt,t),x)
      (∀side (i:Fin (L*(2*(A).cap))),(own x side (i.cast domain.symm) v gr).val=(originalDonor B u side i).elim 0
        (fun e=>(Z).senderJoint T side ((Z).placement.contact e))) ∧
      (∀side (i:Fin (L*(2*(A).cap))) e,originalDonor B u side i=some e→(cargo x side 0 (i.cast domain.symm) v gr).val=
        (Z).senderJoint T false ((Z).placement.contact e)) ∧
      ∀side (i:Fin (L*(2*(A).cap))) e,originalDonor B u side i=some e→(cargo x side 1 (i.cast domain.symm) v gr).val=
        haloNumber B u ((Z).rootVertex T ((Z).placement.owner false ((Z).placement.contact e)))+1)
    (ticket : ∀c,(Z).senderJoint T false c<2^(sx).shortBits)
    (room : ∀u c,haloNumber B u ((Z).rootVertex T ((Z).placement.owner false c))+1<2^(sx).shortBits) :
    ∀(x:Fin blk) (j:Fin (contactCount B)),Source (packed x.val (I.numbered.publicShelf (jAt j).succ).val)
      (word x (contactIdx j)) (sx).lanes (Pout m):=by
  intro x j
  let req:=(P₀).req (jAt j)
  let found:=fun c (v:Fin (sx).hosts) (gr:Fin (sx).groups)=>visits req.2 (fun i=>own x req.1 i v gr)
    (fun i=>cargo x req.1 c i v gr)
  have blank:(P₀).fn 1 0 0 0 0=0:=by rw [fn];rfl
  have seen:=(P₀).contact_output ok.numbers.public_ (pre m) (xAt x) (jAt j) (metaIn x (contactIdx j))
    (trueZero x) (own x req.1) (cargo x req.1) mb zb blank (observed x j) (zero x) (labels x req.1) (cargos x req.1)
  have index : contactIdx j=contactShelfIndex B j:=Fin.ext (CandidateSheet.contact_val j)
  have value (v : Fin (sx).hosts) (gr : Fin (sx).groups) :
      (P₀).fn 1 ((metaIn x (contactIdx j)) v gr).live.toNat ((trueZero x) v gr).toNat
        (found 1 v gr).val (found 0 v gr).val=actualParentNumber B rack₀ x (contactIdx j) v (gr.cast groupAt):=by
    rw [fn,index];cases hv:rack₀ v with
    | none=>simp [actualMeta,actualParentNumber,hv,Meta.blank,publicFn,directWord]
    | some t=>
      let u:=((gr.cast groupAt,t),x)
      obtain ⟨ownAt,payAt,haloAt⟩:=origin x v t hv gr
      have sample (c : (Z).placement.Contact) (live : active (blocks B) u (contactParent B c))
          (slot : contactDigit B u ⟨c,live⟩=j) :
          (found 1 v gr).val=haloNumber B u ((Z).rootVertex T ((Z).placement.owner false c))+1 ∧
          (found 0 v gr).val=(Z).senderJoint T false c:=by
        dsimp only [found,req]
        rw [request]
        rw [visits_cast domain,visits_cast domain]
        exact direct_observed B u j c live slot _ _ _ (ownAt _) (payAt _) (haloAt _) ticket (room u)
      have value₀:=contact_raster_word B u j ((found 1 v gr).val-1) (found 0 v gr).val (by
        intro c live key e pick
        obtain ⟨h₁,h₂⟩:=sample c live key
        exact ⟨by omega,h₂⟩)
      rw [public_zero B u] at value₀
      simp only [publicFn, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), actualMeta, actualParentNumber, hv, Option.elim_some]
      exact value₀
  exact publicValueRead
    (fun v gr => (P₀).fn 1 ((metaIn x (contactIdx j)) v gr).live.toNat ((trueZero x) v gr).toNat
      (found 1 v gr).val (found 0 v gr).val)
    (fun v gr => actualParentNumber B rack₀ x (contactIdx j) v (gr.cast groupAt)) rb value seen

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
