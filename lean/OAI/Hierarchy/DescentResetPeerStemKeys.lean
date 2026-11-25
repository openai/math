import OAI.Hierarchy.DescentResetPeerCalibration
import OAI.Hierarchy.DescentResetStemKeyColumns
import OAI.Hierarchy.DescentResetStemIssuedWindows
import OAI.Hierarchy.DescentResetStemClosedWindow

namespace OAI
/-! # The physical predecessor's signed columns supply the three-port reset directory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage
open DescentFallbackPeriod DescentResetStemKey DescentResetStemPackedIssue DescentSharedBookScan
local notation "A" => input.placement
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "Y" => 2^(Z).n
local notation "OldHost" => Stage.Host (Fin (S.groupCount i)) input.V k
local notation "donors" => donor (S.resetInputDigits ctl.base ctl.radix i) B.frame.basis (B.frame.enough.trans (Nat.sub_le ..))
local notation "before" => input.order.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans Fin.valEmbedding))
local notation "signs" => signedPanel A before S input.valid names

/-- All signed keys are computed in one native pass. The same physical output supplies
each whole key word and the old edge selected at every genuine new host. -/
theorem peer_stem_keys {H t field M w : ℕ} (pad : Fintype.card input.V ≤ H)
    (value : OldHost→ℕ) (bound : ∀u,value u+1 < 2^field)
    (signBits : DescentSignedCableCodec.width D₀ (A).cap ≤ field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (values : Fin H→Fin J→Fin L→Cell t)
    (peers : Fin H→Fin D₀→Option (Fin H))
    (chips : Fin H→Fin J→Fin L→Fin (2*(A).cap)→Option (Live D₀ (A).cap))
    (own : ∀v b lo,(values ((input.vertex v).castLE pad) b lo).val=value (donors v b lo))
    (roster : ∀v j,peers ((input.vertex v).castLE pad) j=
      (hostRoster A (input.vertex.trans Fin.valEmbedding) v j).map (fun a=>(input.vertex a).castLE pad))
    (raw : ∀v b lo z,chips ((input.vertex v).castLE pad) b lo z=signs (donors v b lo) z)
    (ports : Ports D₀) (banks : Projected.Column L (A).cap→Bank) (base : ℕ) (m : Memory w)
    (fits : ∀a,(banks a).Fits w base) (size : ∀a,H*chunks J M ≤ (banks a).size)
    (access : ∀lo,Accessible ports (banks (.inl (1,lo))) H J M w base)
    (stored : Mounted ports peers m J M)
    (olds : ∀lo,Reads (banks (.inl (0,lo))) (fun v b=>((values v b lo).val:Cell field)) M m)
    (tags : ∀lo,Reads (banks (.inl (1,lo))) (fun v b=>((values v b lo).val+1:Cell field)) M m)
    (wires : ∀j lo,Reads (banks (.inr (j,lo))) (fun v b=>((DescentSignedCableCodec.encode (chips v b lo j)).val:Cell field)) M m)
    (room : Columns.stop base D₀ field M H J (stemsCount B) < 2^w) :
    let parser:=parse D₀ (A).cap field
    let side_:=DescentResetStemPackedIssue.side L (A).cap
    let src:=operands ports banks H
    let last:=Columns.output parser side_ src base M H J m
    (Columns.code parser side_ src base M H J w).Exec m last (Columns.ticks parser side_ src base M H J) ∧
    CheapCode (Columns.code parser side_ src base M H J w) ∧
    (∃keys : Fin (stemsCount B)→Fin H→Fin J→Cell (field+2),
       (∀j,Reads (Columns.bank base D₀ field M H J j.val) (keys j) M last) ∧
       ∀(u : Host) s t,(keys (stemAxis B (s,t)) (((Z).hostFields T ((vertex).trans (Fin.castLEEmb pad)) u.1.2).1) (peerLane B u)).val=
         DescentResetStemKey.code ((oldStemAt B u s t).map (stemTicket B s))) ∧
    ∀a,a < base ∨ Columns.stop base D₀ field M H J (stemsCount B) ≤ a → last a=m a := by
  intro parser side_ src last
  let rank:=fun (_ : Fin H) (_ : Fin (DescentSharedBookScan.width r Y D₀))=>0
  let dataAt:=fun v b=>inputs («r» := r) (n:=(Z).n) (field:=field) (fun h c j=>(values h c j).val) peers chips rank v b
  let readAt:=fun (j : Fin (stemsCount B)) v b=>
    let p:=((stemAxis B).symm j).2
    DescentResetStemKey.panel (dataAt v b) p.1 p.2
  obtain ⟨go,words,frame,cheap⟩:=Columns.run parser side_ src base m (parse_zero D₀ (A).cap field) readAt
    (fun j a=>readers_fit ports banks base fits access _ _ a)
    (fun j=>operand_sources ports banks base values peers chips rank m fits size access stored olds tags wires _ _) room
  refine ⟨go,cheap,⟨_,words,?_⟩,frame⟩
  intro u sign t'
  have genuine:=stem_projected_operand_key (field:=field) B value bound signBits onWire
    (input.vertex.trans (Fin.castLEEmb pad)) values peers chips rank own roster raw u sign t'
  change (word parser (((stemAxis B).symm ((stemAxis B) (sign,t'))).1)
    (readAt ((stemAxis B) (sign,t')) _ _)).val=_
  simp only [readAt,Equiv.symm_apply_apply]
  exact genuine

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
