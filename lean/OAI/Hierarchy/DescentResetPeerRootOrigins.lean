import OAI.Hierarchy.DescentResetPeerRootPages
import OAI.Hierarchy.DescentResetPrivateOrigins
import OAI.Hierarchy.DescentResetPeerCalibration

namespace OAI
/-! # The private raw neighbor origins from the recorded reset and its actual root pages -/
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


open DescentPackedPrivateMenu DescentFallbackPeriod DescentResetHostSize DescentRotorRootPresence
open DescentFallbackPeriod.Projected.Receiver
local notation "cap" => input.placement.cap
local notation "L" => 2^r
local notation "count" => L*(2*cap)
local notation "leaf" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*cap)
local notation "layer" => DescentRecordedRotorLayers.width f cap
local notation "field" => fieldBits (Z).graph r height count layer C (Z).width

def privatePanelAt {b : ℕ} (eqn : leaf=b) (s : Bool) : (Z).Fallback→DescentPackedFallbackTree.Panel height b :=
  eqn ▸ privatePanelCatalog B s

theorem private_installed_at {b : ℕ} (eqn : leaf=b) (unit : 0 < (Z).unit)
    (old : Fin (Fintype.card input.V)) (hi : Block (T).commonDepth) (s : Bool)
    (t : (Z).RootTicket T) (j : Fin capacity) (p : PrivateOccurrence B) (raw : Fin 5→ℕ)
    (numbers : raw=values (Z).graph r height b (Z).layerBits C (Z).width s j.val
      ((Z).rootsOf T vertex unit s (privatePanelAt B eqn s) t old hi))
    (atSlot : privateRawAt B old hi s t j p) :
    (Z).expand T vertex p.1.2 raw=(Z).actualRecord T vertex (privateWire B p) := by
  subst b
  exact private_installed_of_values B unit s t old hi j p raw numbers atSlot

theorem private_count_eq : leaf=count := by rw [B.keyWidth]

variable {H a keyBits p : ℕ} (pad : Fintype.card input.V ≤ H) (recorded : B.Recorded p)
local notation "tall" => (vertex).trans (Fin.castLEEmb pad)
local notation "name" => (Z).rawHostRank T tall
local notation "arr" => privatePanelAt B (private_count_eq B)
variable (headers : Code (B.reset.k-B.terminals.commonDepth)→Fin H→Block B.terminals.commonDepth→Fin 3→Cell a)
    (packets : Bool→(Code (B.reset.k-B.terminals.commonDepth)×Option (Fin (2^B.reset.n)))→Fin H→Block B.terminals.commonDepth→
      Packet input.placement.degree (2^(B.reset.k-B.terminals.commonDepth)) input.placement.cap B.reset.n (B.reset.k-B.terminals.commonDepth) a)
local notation "word" => privatePageValue (Ht:=height) (board:=(Z).graph) (packet:=(Z).width) (C:=C)
  (layerBits:=layer) (f:=f) headers packets
variable (keys : Fin (stemsCount B)→Fin H→Block B.terminals.commonDepth→Cell keyBits)
    (actors : Fin (H*(DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth)
      (GroupStage.depthBound D n f g)).card)→Block B.terminals.commonDepth→Cell 1)

include recorded in
/-- The roots of the peer bank are the original root book's two numerical pages.
The old capacity fixes the layer count, while each side uses its own fallback arrivals. -/
theorem issued_page_origins (unit : 0 < (Z).unit)
    (stem : ∀(u : Host) s (t : Slot),(keys (stemAxis B (s,t)) (((Z).hostFields T tall u.1.2).1) (peerLane B u)).val=
      DescentResetStemKey.code ((oldStemAt B u s t).map (stemTicket B s)))
    (actorsAt : ∀(v : B.next.V) (hi : Block (T).commonDepth),actors (name v) hi=(Z).sparseActor T tall (name v) hi)
    (valuesAt : ∀(v : (Z).V) (hi : Block (T).commonDepth) (t : Code r),(headers t (tall v) hi 0).val=cap)
    (measuredDepth : ∀v hi t,(headers t (tall v) hi 1).val=(Z).placement.b v-(T).commonDepth+1)
    (shapeBad : ∀v hi t,(headers t (tall v) hi 2).val%2=Bool.toNat (decide ((Z).placement.hub v ∨
      (v,group ((Z).placement.b v) (DescentIssuedFallbackPanel.join (((T).commonLow v).trans ((Z).placement.depth v)) hi (sample t)))∈(Z).placement.keys)))
    (occupied : ∀s t,DescentFallbackPeriod.key (Ht:=height) (l:=(Z).layerBits) s
      ((Z).fallLabel T t,((T).code t).2.2) (packets s ((Z).fallLabel T t,((T).code t).2.2)
        (tall ((Z).rootVertex T (.inr t))) ((Z).rootBlock T (.inr t)))=(Z).fallbackKey T s t (arr s t))
    (empty : ∀s t v hi,(Z).atRoot T vertex (vertex v,hi,.inr t)=none →
      DescentFallbackPeriod.key (Ht:=height) (l:=(Z).layerBits) s t (packets s t (tall v) hi)=none) :
    PeerOrigins B pad (⟨keys,actors,word⟩ : PriorPeerWords B H field keyBits) unit arr := by
  let prior : PriorPeerWords B H field keyBits:=⟨keys,actors,word⟩
  let raw:=priorPrivate B pad prior
  have certificate (old : Fin (Fintype.card input.V)) (hi : Block (T).commonDepth)
      (s : Bool) (t : (Z).RootTicket T) (j : Fin capacity) : raw old hi s t j=values (Z).graph r height count (Z).layerBits C (Z).width s j.val
      ((Z).rootsOf T vertex unit s (arr s) t old hi) := by
    obtain ⟨v,rfl⟩:=((Fintype.bijective_iff_injective_and_card input.vertex).2 ⟨input.vertex.injective,by simp⟩).2 old
    let z:=B.frame.host v
    have index : vertex z=input.vertex v:=by simp [z]
    rw [←index]
    cases t with
    | inl t=>
      apply (Z).good_root_fields T vertex unit s (arr s) z hi t f (headers t (tall z) hi) _ _ j
      · let value:=fun lo=>Bool.toNat (decide ((Z).placement.hub z ∨
          (z,group ((Z).placement.b z) (DescentIssuedFallbackPanel.join (((T).commonLow z).trans ((Z).placement.depth z)) hi lo))∈(Z).placement.keys))
        have mode (lo) : value lo%2=value lo:=by
          exact Nat.mod_eq_of_lt (Bool.toNat_lt _)
        exact DescentIssuedGoodHeaders.root_fields (Z) T z hi t value mode _ _ (measuredDepth z hi t)
          ((shapeBad z hi t).trans (mode (sample t)).symm)
      · intro g _ _ _
        rw [valuesAt]
        exact DescentRecordedRotorLayers.from_prior_cap B recorded s g cap rfl
    | inr t=>
      apply (Z).fall_root_fields T vertex unit s (arr s) (vertex z) hi t (packets s t (tall z) hi) _ j
      exact (Z).fall_root_key T vertex unit s (arr s) (fun t v hi=>packets s t (tall v) hi)
        (occupied s) (fun v hi t=>empty s t v hi) z hi t
  exact ⟨stem,actorsAt,certificate,fun old hi s t j p observed=>
    private_installed_at B (private_count_eq B) unit old hi s t j p _ (certificate old hi s t j) observed⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
