import OAI.Hierarchy.DescentResetPeerPortfolio
import OAI.Hierarchy.DescentResetPrivatePortfolio
import OAI.Hierarchy.DescentResetStemPeerEvidence
import OAI.Hierarchy.DescentResetTrunkMarkers
import OAI.Hierarchy.DescentContactPortfolio

namespace OAI
/-! # Chronological coverage of all physical raw reset peer markers, including empty reservations -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentCompiler DescentColonies DescentDenseHostOrder DescentStageEdgeReceipt DescentSortedRoster
open DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup DescentGroupPeerOrder
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "J" => 2^(T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "Slot" => Fin (2^(m-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "D₀" => input.placement.degree
local notation "K" => 2*DescentFallbackShapeTable.rows r (2^(Z).n)
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))

def stemAxis : Bool×Slot≃Fin (stemsCount B) :=
  (Equiv.prodCongr finTwoEquiv.symm finProdFinEquiv).trans finProdFinEquiv

def peerReceiver (v : B.next.V) (g₀ : Fin J) : Host := (((digits g₀).1,v),(digits g₀).2)
def peerLane (u : Host) : Fin J := (digits).symm (u.1.1,u.2)

theorem receiver_lane (u : Host) : peerReceiver B u.1.2 (peerLane B u)=u := by
  rcases u with ⟨⟨g₀,v⟩,x⟩
  simp [peerReceiver,peerLane]
theorem lane_receiver (v : B.next.V) (g₀ : Fin J) : peerLane B (peerReceiver B v g₀)=g₀ := by
  simp [peerReceiver,peerLane]

variable {H keyBits outBits count : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "padded" => (vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
local notation "coords" => (Z).hostFields T vertex
local notation "pcoords" => (Z).hostFields T padded
local notation "pitch" => H*shelf
local notation "Family" => Axes.Fields (stemsCount B) (contactCount B) (privateCount B)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)
local notation "tpl" s:arg => fun j : Fin K=>DescentResetStemDecoder.localTemplate (Z).graph r height s j.val
set_option maxHeartbeats 1000000 in
/-- The four readbacks use only original measured fields: earlier signed keys, a structural
trunk occupancy bit, the previous signed donor's contact data and the five private header digits. -/
theorem measured_tickets
    (peers : Fin H→Fin D₀→Option (Fin H))
    (words : Family (Fin pitch→Fin J→Cell outBits))
    (rosterRead : ∀(v : input.V) j,peers ((input.vertex v).castLE pad) j=
      (DescentGroupPeerOrder.hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map
        (fun a=>(input.vertex a).castLE pad))
    (wide : (D₀+1)*shelf < 2^outBits)
    (keys : Host→Bool→Slot→Cell keyBits)
    (earlier : ∀u s t,(keys u s t).val=DescentResetStemKey.code ((oldStemAt B u s t).map (stemTicket B s)))
    (stem : ∀(u : Host) (s : Bool) (t : Slot),words.stem (stemAxis B (s,t)) (named u.1.2) (peerLane B u)=
      DescentResetStemPeerChip.bits (tpl s) D₀ ((pcoords u.1.2).2) (keys u s t))
    (actor : Host→Cell 1) (seen : ∀u,(actor u).val=1 ↔ trunkTest B u)
    (trunk : ∀(u : Host),words.trunk (named u.1.2) (peerLane B u)=
      DescentResetTrunkChip.bits (Z).graph r height D₀ ((finProdFinEquiv.symm (named u.1.2)).2) (actor u))
    (contact : ∀(u : Host) key don,(words.contact key don (named u.1.2) (peerLane B u)).val=contactSheet B u key don)
    (unit : 0 < (Z).unit) (panel : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel height count)
    (raw : Fin (Fintype.card input.V)→Fin J→Bool→(Z).RootTicket T→Fin capacity→Fin 5→ℕ)
    (numbers : ∀old hi s t (l : Fin capacity),raw old hi s t l=
      DescentPackedPrivateMenu.values (Z).graph r height count (Z).layerBits C (Z).width s l.val
        ((Z).rootsOf T vertex unit s (panel s) t old hi))
    (installed : ∀old hi s t l p,privateRawAt B old hi s t l p →
      (Z).expand T vertex p.1.2 (raw old hi s t l)=(Z).actualRecord T vertex (privateWire B p))
    (priv : ∀(v : B.next.V) hi key,(words.privateEdge key (named v) hi).val=
      privateSheet B (fun p=>PrivateEvidence.ticket D₀ shelf (coords v).2.val
        (raw (coords v).1 hi p.1 p.2.1 p.2.2)) key) :
    IssuedTickets B pad peers kind_ words.all := by
  apply family_receipt B pad peers words
  · intro v x
    refine Iff.trans ?_ (stem_ticket_evidence B pad peers v x keys earlier wide)
    constructor
    · rintro ⟨l,g₀,j,ptr,bit⟩
      obtain ⟨⟨sign,t⟩,rfl⟩:=(stemAxis B).surjective l
      let u:=peerReceiver B v g₀
      have read:=stem u sign t
      rw [show peerLane B u=g₀ from lane_receiver B v g₀] at read
      exact ⟨u,sign,t,j,rfl,ptr,(congrArg Fin.val read).symm.trans bit⟩
    · rintro ⟨u,sign,t,j,rfl,ptr,bit⟩
      exact ⟨stemAxis B (sign,t),peerLane B u,j,ptr,(congrArg Fin.val (stem u sign t)).trans bit⟩
  · intro v x
    let chip:=fun gp lo=>actor ((gp,v),lo)
    refine Iff.trans ?_ (trunk_marker_padded B pad peers v x chip (fun gp lo=>seen ((gp,v),lo)) wide)
    constructor
    · rintro ⟨g₀,j,ptr,bit⟩
      let u:=peerReceiver B v g₀
      have read:=trunk u
      rw [show peerLane B u=g₀ from lane_receiver B v g₀] at read
      exact ⟨j,u.1.1,u.2,ptr,(congrArg Fin.val read).symm.trans bit⟩
    · rintro ⟨j,gp,lo,ptr,bit⟩
      let u : Host:=((gp,v),lo)
      exact ⟨peerLane B u,j,ptr,(congrArg Fin.val (trunk u)).trans bit⟩
  · intro v x
    refine Iff.trans ?_ (contact_tickets B pad peers rosterRead v x)
    constructor
    · rintro ⟨l,don,g₀,j,ptr,bit⟩
      let u:=peerReceiver B v g₀
      have read:=contact u l don
      rw [show peerLane B u=g₀ from lane_receiver B v g₀] at read
      exact ⟨l,don,u.1.1,u.2,j,ptr,read.symm.trans bit⟩
    · rintro ⟨l,don,gp,lo,j,ptr,bit⟩
      let u : Host:=((gp,v),lo)
      exact ⟨l,don,peerLane B u,j,ptr,(contact u l don).trans bit⟩
  · intro v x
    let e:=coords v
    let code:=fun hi s t l=>PrivateEvidence.ticket D₀ shelf e.2.val (raw e.1 hi s t l)
    have authentic (hi s t l):=
      private_ticket_support B pad peers e.1 e.2 x hi s t l (raw e.1 hi s t l) unit (panel s)
        (numbers e.1 hi s t l) (installed e.1 hi s t l)
    have complete:=private_sheet_tickets B pad peers e.1 e.2 x code authentic
    constructor
    · rintro ⟨l,g₀,j,ptr,bit⟩
      exact complete.mp ⟨l,g₀,j,ptr,(priv v g₀ l).symm.trans bit⟩
    · intro edge
      obtain ⟨l,g₀,j,ptr,bit⟩:=complete.mpr edge
      exact ⟨l,g₀,j,ptr,(priv v g₀ l).trans bit⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
