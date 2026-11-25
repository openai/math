import OAI.Hierarchy.DescentRecordedRootSnapshot
import OAI.Hierarchy.DescentRecordedPublicActorDirectory
import OAI.Hierarchy.DescentNamedRootReindex
import OAI.Hierarchy.DescentResetCanvasIngressRoster
import OAI.Hierarchy.DescentFallbackActorWordRoom

namespace OAI
/-! # The reached receiver's original header on its numbered actor input -/
namespace Hierarchy.DescentSixParty.ClosedReset
open DescentCompiler DescentSIMDLookup DescentGL DescentColonies DescentFallbackPeriod.Projected
open DescentPackedZip DescentFallbackRankRAM DescentGroupPeerOrder DescentRelativeContacts DescentFallbackShapeTable
open DescentPaidResidentCount.Reset Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "r" => (Z).k-(T).commonDepth
local notation "H" => S.hostSize i
local notation "ht" => GroupStage.depthBound D n f g
variable {d₁ cap n₁ r₁ c₁ gr h₁ K R M N hm lb t field w nbits : ℕ}
  (X : Receiver.IndexedRoots d₁ cap N n₁ r₁ c₁ (S.hostSize i) gr K R M hm lb t field h₁ w)
  (dd : d₁=input.placement.degree) (capacity : cap=input.placement.cap) (nn : n₁=B.reset.n) (rr : r₁=B.reset.k-B.terminals.commonDepth)
  (coarse : c₁=B.terminals.commonDepth) (groups : gr=S.groupCount i) (height : h₁=GroupStage.depthBound D n f g)
local notation "Y" => X.reindex dd capacity nn rr coarse rfl groups height
local notation "fac" => 32*Nat.clog 2 (2*d₁)

/-- Changing the public high/low split preserves the packed source, including the padded host rows. -/
theorem real_panel_width {size M t w nbits : ℕ} (eqn : size=S.groupWidth k tail i+k)
    (basis : Layout size) (won : HEq basis B.frame.basis) (floor : ℕ) (m : Memory w)
    (original : PackedFlow.Padded.Published (h:=S.groupWidth k tail i) (l:=k) M t floor
      (input.vertex.trans (Fin.castLEEmb input.valid.host)) (Recorded.realPanel (reset:=B) rfl B.frame.basis nbits t) m) :
    ∃values : Fin H→Block (T).commonDepth→Block (size-(T).commonDepth)→Cell t,
      (∀z : Row H (2^(T).commonDepth) M,m (floor+(row _ _ _ z).val)=
        ((data (fun v hi=>encode t (2^(size-(T).commonDepth)) (values v hi)) z).val:Word w)) ∧
      ∀v hi j,values ((input.vertex.trans (Fin.castLEEmb input.valid.host)) v) hi j=
        Recorded.realPanel (reset:=B) eqn basis nbits t v hi j :=by
  subst size
  have equal : basis=B.frame.basis:=eq_of_heq won
  subst basis
  exact original

/-- All original header fields refer to the four arrays of the reindexed public receiver. -/
theorem original_header_on_public (pop raw line : Bank) (m : Memory w)
    (stage : Recorded.ActorPanelAt (B:=B) (M:=M) (t:=t) (nbits:=nbits) pop raw line X.book m)
    (catalog : X.book.fallbackDegree=fac ∧ X.book.hubBits=g ∧ X.book.loadBits=f ∧ X.book.shapes=2^h₁)
    (peers : X.book.previousNeighbors.Fits w X.receiver.origin) (hubs : X.book.previousHubs.Fits w X.receiver.origin)
    (peerSlots : H*d₁≤X.book.previousNeighbors.size) (hubSlots : H≤X.book.previousHubs.size)
    (hostsFit : H<2^w) (portsFit : d₁+1<2^w) (word : 0<w) (tall : h₁+2≤w)
    (names : actorWordBits r₁ fac g n₁≤w) (signed : DescentSignedCableCodec.width d₁ cap≤field)
    (ranks : h₁+2≤field) :
    OriginalHeader B input.valid.host (Y).receiver (Y).book m := by
  subst d₁; subst cap; subst n₁; subst r₁; subst c₁; subst gr; subst h₁
  refine ⟨catalog.1,catalog.2.1,catalog.2.2.1,catalog.2.2.2,peers,hubs,peerSlots,hubSlots,
    hostsFit,portsFit,?_,stage.hubs,word,tall,?_,?_,signed,ranks⟩
  · intro v j
    have seen:=stage.hosts v j
    rw [show PackedFlow.portAt (A) ((A).numberedHeader (S.resetInputDigits ctl.base ctl.radix i) input.vertex).site v j=
      hostRoster (A) ((input.vertex.trans (Fin.castLEEmb input.valid.host)).trans Fin.valEmbedding) v j from
      DescentResetCanvasIngress.original_port input v j] at seen
    exact seen
  · intro t side target inside
    exact actor_shape_fits names _ (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.sub_le_sub_right ((T).codeLegal t).2.1 (T).commonDepth) side target inside
  · intro t
    exact actor_endpoint_fits names _ (Nat.sub_le_sub_right ((T).codeLegal t).2.1 (T).commonDepth)
      (Nat.mod_lt _ (Nat.two_pow_pos _))

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
