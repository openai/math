import OAI.Hierarchy.DescentOriginalScalarPrefix
import OAI.Hierarchy.DescentCalendarMeasuredChannels
import OAI.Hierarchy.DescentOriginalNumberSelfShape
import OAI.Hierarchy.DescentPhysicalRankSheetIntake
import OAI.Hierarchy.DescentResetSignedAll

namespace OAI
/-! # The four original number inputs on the reached pre-publication memory -/
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
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤ H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

open DescentPackedZip DescentResetPeerJointPacked DescentResetPeerJointRAM
local notation "s₀" => (v₀).sheets
variable (bound : used≤(s₀).hosts)
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "gx" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "bx" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck

local notation "menu" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "area" => ((v₀).remap base₀).endAddress
local notation "output" m => I.numbered.prefixOutput area (I.masked.image (I.privateResult m))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex

private theorem cast_value {N raw₀ raw₁ deg₀ deg₁ old₀ old₁ width₀ width₁ V : ℕ}
    (ps : raw₀=raw₁) (ds : deg₀=deg₁) (os : old₀=old₁) (qs : width₀=width₁)
    (name : Fin N→Fin raw₁) (old : Fin old₁→Fin deg₁→Option (Fin old₁))
    (neighbors : Fin raw₁→Fin 3→Option (Fin raw₁)) (v : Fin V) (j : Fin 4) :
    Aux.value width₀ (fun n=>(name n).cast ps.symm)
      (fun h i=>(old (h.cast os) (i.cast ds)).map (Fin.cast os.symm))
      (fun h i=>(neighbors (h.cast ps) i).map (Fin.cast ps.symm)) v j=
      Aux.value width₁ name old neighbors v j := by
  subst raw₁;subst deg₁;subst old₁;subst width₁
  simp

theorem reached_original_scalar_sources (ok : I.Ready) (m : Memory bw)
    (layoutAt : I.OriginalScalarLayout) (captured : PhysicalReset.DateInputs.CaptureRoom (menu) m) :
    ∃ self : Fin (s₀).hosts→Cell (s₀).shortBits,
    ∃ shape : Fin (s₀).hosts→Cell (s₀).shortBits,
    ∃ halo : Fin (s₀).hosts→Cell (s₀).haloBits,
      (∀x : Fin (2^k),Source (I.numbered.zero (x.cast (bx).symm))
        (fun (_ : Fin (s₀).hosts) (g : Fin (s₀).groups)=>((decide (g.val=0 ∧ x.val=0)).toNat:Cell (s₀).zeroBits))
        (s₀).lanes (output m)) ∧
      (∀x : Fin (2^k),Source (I.numbered.sources.zero (x.cast (bx).symm))
        (fun (_ : Fin (s₀).hosts) (g : Fin (s₀).groups)=>((decide (g.val=0 ∧ x.val=0)).toNat:Cell (s₀).zeroBits))
        (s₀).lanes (output m)) ∧
      (∀x : Fin (2^k),Source (I.numbered.sources.self (x.cast (bx).symm))
        (fun h (_ : Fin (s₀).groups)=>self h) (s₀).lanes (output m)) ∧
      (∀x : Fin (2^k),Source (I.numbered.sources.shape (x.cast (bx).symm))
        (fun h (_ : Fin (s₀).groups)=>shape h) (s₀).lanes (output m)) ∧
      (∀x : Fin (2^k),Source (I.numbered.halo (x.cast (bx).symm))
        (fun h (_ : Fin (s₀).groups)=>halo h) (s₀).lanes (output m)) ∧
      ∀v actor,rack₀ v=some actor→∀(grp : Fin (s₀).groups) (x : Block k),
        (self v).val=haloNumber B ((grp.cast gx,actor),x) (receiverRoot B ((grp.cast gx,actor),x)).1 ∧
        (shape v).val=((Z).rawHostRank T vertex actor).val%shelf ∧
        (halo v).val=haloNumber B ((grp.cast gx,actor),x) (receiverRoot B ((grp.cast gx,actor),x)).1 := by
  let digit := I.measuredScalar (menu) m captured
  let self := fun v : Fin (s₀).hosts=>(((digit 0 v).val-1:ℕ):Cell (s₀).shortBits)
  let shape := fun v : Fin (s₀).hosts=>(((digit 1 v).val/radix (peer₀).oldDegree:ℕ):Cell (s₀).shortBits)
  let halo := fun v : Fin (s₀).hosts=>(((digit 0 v).val-1:ℕ):Cell (s₀).haloBits)
  have actual:=I.original_prefix_sources (menu) m captured ok layoutAt.degree
  refine ⟨self,shape,halo,?_,?_,?_,?_,?_,?_⟩
  · intro x;rw [layoutAt.zero];exact actual.zero x.val
  · intro x;rw [layoutAt.publicZero];exact actual.zero x.val
  · intro x;rw [layoutAt.self];exact actual.self
  · intro x;rw [layoutAt.shape];exact actual.shape
  · intro x;rw [layoutAt.halo];exact actual.halo
  · intro v actor atRow gr x
    have whereAt:=rack_named B dense₀ v actor atRow
    have atRack : originalTrunkRack B v=some actor := by
      rw [←whereAt];exact (original_rack_order B pad bound).1 actor
    have earlier : (A).degree < 2^(s₀).haloBits := cal.oldDegree ▸ layoutAt.haloRoom
    have shorter : (A).degree < 2^(s₀).shortBits := cal.oldDegree ▸ layoutAt.selfRoom
    have full : shelf ≤ 2^(s₀).shortBits := cal.peerShapes ▸ layoutAt.shapeRoom
    have sem := original_number_self_shape B pad bound near earlier full v actor atRack (gr.cast gx) x
    have sem' := original_number_self_shape B pad bound near shorter full v actor atRack (gr.cast gx) x
    have origin (j : Fin 4) :
        (digit j v).val=Aux.value shelf (compactActorName B pad) (adj_) near v j :=
      cast_value cal.peerSlots cal.oldDegree cal.oldCount cal.peerShapes (compactActorName B pad) (adj_) near v j
    dsimp only [self,shape,halo]
    rw [origin 0,origin 1,cal.oldDegree]
    exact ⟨sem'.1,sem.2,sem.1⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
