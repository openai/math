import OAI.Hierarchy.DescentResetPeerOperands
import OAI.Hierarchy.DescentResetTrunkActorBits
import OAI.Hierarchy.DescentResetPrivateDigits

namespace OAI
/-! # Reading the four reset peer families from their original physical headers -/
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

variable {H field keyBits bits count : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "padded" => (vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
local notation "coords" => (Z).hostFields T padded
local notation "pitch" => H*shelf
variable (prior : PriorPeerWords B H field keyBits)
def priorStem (u : Host) (s : Bool) (t : Slot) :=
  prior.keys (stemAxis B (s,t)) (coords u.1.2).1 (peerLane B u)
def priorPrivate (old : Fin (Fintype.card input.V)) (l : Fin J) (s : Bool) (t : (Z).RootTicket T) (j : Fin capacity) :=
  PrivateEvidence.frame field capacity j (prior.privatePages s t (old.castLE pad) l)

variable (unit : 0 < B.reset.unit) (panel : Bool→B.reset.Fallback→DescentPackedFallbackTree.Panel (GroupStage.depthBound D n f g) count)

/-- The original input words are the signed predecessor keys, occupancy directory, and the
five-field records emitted by the private device catalog. -/
structure PeerOrigins : Prop where
  stem : ∀u s t,(priorStem B pad prior u s t).val=DescentResetStemKey.code ((oldStemAt B u s t).map (stemTicket B s))
  actors : ∀v hi,prior.actors (named v) hi=(Z).sparseActor T padded (named v) hi
  numbers : ∀old hi s t (l : Fin capacity),priorPrivate B pad prior old hi s t l=
    DescentPackedPrivateMenu.values (Z).graph r height count (Z).layerBits C (Z).width s l.val
      ((Z).rootsOf T vertex unit s (panel s) t old hi)
  installed : ∀old hi s t l p,privateRawAt B old hi s t l p →
    (Z).expand T vertex p.1.2 (priorPrivate B pad prior old hi s t l)=(Z).actualRecord T vertex (privateWire B p)

/-- Packed short markers agree with all and only the four families of original edges. -/
theorem peer_origins (origin : PeerOrigins B pad prior unit panel)
    (peers : Fin H→Fin D₀→Option (Fin H))
    (rosterRead : ∀(v : input.V) j,peers ((input.vertex v).castLE pad) j=
      (hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map (fun a=>(input.vertex a).castLE pad))
    (wide : (D₀+1)*shelf < 2^bits)
    (contact : Fin (contactCount B)→Fin (stemsCount B)→Fin pitch→Fin J→Cell bits)
    (contactRead : ∀u j donor,(contact j donor (named u.1.2) (peerLane B u)).val=contactSheet B u j donor) :
    IssuedTickets B pad peers kind_ (peerWords B H field keyBits bits prior contact).all := by
  let act:=fun u : Host=>if trunkTest B u then (1:Cell 1) else 0
  have seen (u : Host) : (act u).val=1 ↔ trunkTest B u := by
    by_cases h₀ : trunkTest B u <;> simp [act,h₀]
  refine measured_tickets B pad peers _ rosterRead wide (priorStem B pad prior) origin.stem ?_ act seen ?_
    contactRead unit panel (priorPrivate B pad prior) origin.numbers origin.installed ?_
  · intro u s t
    change DescentResetStemPeerChip.bits (peerTemplate B _) _ (finProdFinEquiv.symm (finProdFinEquiv (coords u.1.2))).2
      (prior.keys _ (finProdFinEquiv.symm (finProdFinEquiv (coords u.1.2))).1 _) = _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    rfl
  · intro u
    let mark : Cell 1 → Cell bits := DescentResetTrunkChip.bits (Z).graph r height D₀
      (finProdFinEquiv.symm (named u.1.2)).2
    have eqn:=trunk_actor_bits («D₀» := D₀) (b:=bits) B pad u.1.2 (peerLane B u)
    exact (congrArg mark (origin.actors u.1.2 (peerLane B u))).trans
      (eqn.trans (congrArg (fun point => mark (act point)) (receiver_lane B u)))
  · intro v hi j
    by_cases h₀ : ∃p,privateProbeId B p=j
    · simp only [peerWords,privateSheet,dite_eq_left h₀]
      change (PrivateEvidence.word D₀ shelf field capacity bits
        (finProdFinEquiv.symm (finProdFinEquiv (coords v))).2 _ (prior.privatePages _ _ (finProdFinEquiv.symm (finProdFinEquiv (coords v))).1 hi)).val=_
      rw [Equiv.symm_apply_apply]
      exact private_word_val B _ _ hi h₀.choose.1 h₀.choose.2.1 h₀.choose.2.2 _ unit (panel h₀.choose.1)
        (origin.numbers ..) (fun p hit => origin.installed _ _ _ _ _ p hit) wide
    · simp only [peerWords,privateSheet,dite_eq_right h₀]
      rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
