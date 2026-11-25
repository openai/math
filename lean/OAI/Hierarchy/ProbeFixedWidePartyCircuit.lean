import OAI.Hierarchy.TaggedWideCalendarPartyPins
import OAI.Hierarchy.ProbeFixedWidePacketBody
import OAI.Hierarchy.TaggedWireStripTender
import OAI.Hierarchy.ProbeBroadcastReadout

namespace OAI
/-! # The two actual fixed menus of signed party circuits -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix.PartyPins
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open Tagged Probe AdaptiveProbe Strip ChosenPackets.RowRouting
open scoped BigOperators Classical
variable {F V A E : Type} [Field F] [Fintype V] [Fintype A] [Fintype E]
    {n k M D width p e digits : ℕ} (name : TreeSite n k≃Fin (Fintype.card (TreeSite n k)))
    (hk : 0<k)
local notation "sites" => Fintype.card (TreeSite n k)
local notation "G" => treeGraph name
local notation "U" => E⊕TreeLink n k

include name hk in
private theorem otherSite (i : Fin sites) : ∃j : Fin sites,i≠j := by
  let c:=(name.symm i).1
  let a:=name (c,none)
  let b:=name (c,some (⟨0,hk⟩,false))
  have ab:a≠b:=fun h=>by have eq:=congrArg Prod.snd (name.injective h);cases eq
  by_cases h:i=a
  · exact ⟨b,by simpa only [h] using ab⟩
  · exact ⟨a,h⟩

include hk in
theorem hasTap (w : ℕ) (i : Fin sites) :
    ∃t : (portGraph sites).Port i,w≤(treeGraph name).chordWidths (fun _=>w) t.val.1 := by
  obtain ⟨j,ne⟩:=otherSite name hk i
  exact incident_selector _ (actual_links G (tree_connected name) w) i j ne

def localRows (edge : E→Chord sites) : Fin (Fintype.card U)→Chord sites :=
  Sum.elim edge (fun b=>@DistinctPair.chord _ _ ⟨name⟩ (treeEnds n k b)) ∘ treeFirst E (TreeLink n k)

variable [Nonempty (Fin (Fintype.card (TreeSite n k)))] [Nonempty E]
    {edge : E→Chord (Fintype.card (TreeSite n k))} {req : A→E} {box : Set (E→ℝ)} {ε cost : ℝ} {min : ℕ}
    (menu : FixedMenu F edge req box ε cost min) (roles : Fintype.card (E ⊕ TreeLink n k)≤M)
    (old r : ℕ) (read : ℕ→ℕ→V⊕Bool)

/-- The original menu ordinal is the major part of the native tag. Its local
tree vertex is the minor part, exactly as in the published ballot word. -/
def menuParty (atom : menu.index) (i : Fin sites) : BitNetwork F (Fintype.card (Gathered V D width)) :=
  let P:=menu.packet atom
  let key:=hasTap name hk (r*P.selectorBits) i
  circuit (e:=e) (p:=p) (digits:=digits) old roles read P G i key.choose (localRows name edge) key.choose_spec

def menuParties (j : Fin (Fintype.card menu.index*sites)) : BitNetwork F (Fintype.card (Gathered V D width)) :=
  let c:=finProdFinEquiv.symm j
  menuParty (e:=e) (p:=p) (digits:=digits) name hk menu roles old r read ((Fintype.equivFin _).symm c.1) c.2

theorem menuParties_at (a : menu.index) (i : Fin sites) :
    menuParties (D:=D) (width:=width) (e:=e) (p:=p) (digits:=digits) name hk menu roles old r read
      (finProdFinEquiv (Fintype.equivFin _ a,i))=
    menuParty (D:=D) (width:=width) (e:=e) (p:=p) (digits:=digits) name hk menu roles old r read a i := by
  simp [menuParties]

end Hierarchy.WireTelescope.PassMatrix.PartyPins

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open WireTelescope.PassMatrix WireTelescope.PassMatrix.PartyPins
open AdaptiveProbe ProbeStage CoreBoard Strip StripChart StripDirectory
open ThreeFlat
open scoped Classical
variable {F V : Type} [Field F] [Fintype V] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "fs" => v.nativeFormats P h width
local notation "M" => v.widePacketRoles h
local notation "D" => v.widePacketDegree

def signedPartyCount (a : Attempt) :=
  (match a with | .outer ..=>Fintype.card (v.payloadPacketMenu N).index | .inner ..=>Fintype.card v.purchasePacketMenu.index)*
    v.wideBallotParties h a

/-- The concrete signed complete lookup table for both original public
repair dates, with the exact native batch size for that date. -/
def signedParty (a : Attempt) (neighborCap roleBits laneBits keyBits : ℕ) (read : ℕ→ℕ→V⊕Bool)
    (j : Fin (v.signedPartyCount h a)) : BitNetwork F (Fintype.card (Gathered V D neighborCap)) := by
  cases a with
  | outer phase trial =>
    let a:=Attempt.outer phase trial
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    letI : Nonempty (Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k))):=
      ⟨names (PayloadStrip.first N 0,none)⟩
    letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    exact menuParties («D»:=D) (width:=neighborCap) («M»:=M) (p:=roleBits) (e:=laneBits) (digits:=keyBits) names v.positive (v.payloadPacketMenu N)
      (Nat.le_max_left ..) (v.wideBallotShape P h width (.attempt a)).columns (fs a).histMass read
      j
  | inner phase trial layer tick =>
    let a:=Attempt.inner phase trial layer tick
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    letI : Nonempty (Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k))):=
      ⟨names (ChainStrip.inlet v.depth 0,none)⟩
    letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    exact menuParties («D»:=D) (width:=neighborCap) («M»:=M) (p:=roleBits) (e:=laneBits) (digits:=keyBits) names v.positive v.purchasePacketMenu
      (Nat.le_max_right ..) (v.wideBallotShape P h width (.attempt a)).columns (fs a).histMass read
      j

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
