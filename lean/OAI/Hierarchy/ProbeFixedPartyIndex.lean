import OAI.Hierarchy.ProbeFixedWidePartyCircuit
import OAI.Hierarchy.ProbeFixedPacketAtom

namespace OAI
/-! # Selecting the original native packet and local party in the fixed signed circuit table -/
noncomputable section
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

def partyIndex (a : Attempt) (at₀ : v.widePacketMenuIndex h a) (j : Fin (v.wideBallotParties h a)) :
    Fin (v.signedPartyCount h a) := by
  cases a with
  | outer ph tr => exact finProdFinEquiv ((Fintype.equivFin (v.payloadPacketMenu N).index) at₀,j)
  | inner ph tr sj ti => exact finProdFinEquiv ((Fintype.equivFin v.purchasePacketMenu.index) at₀,j)

def majorIndex (a : Attempt) (at₀ : v.widePacketMenuIndex h a) : Fin (v.menuCodes N) := by
  cases a with
  | outer ph tr => exact ((Fintype.equivFin (v.payloadPacketMenu N).index) at₀).castLE (Nat.le_max_left ..)
  | inner ph tr sj ti => exact ((Fintype.equivFin v.purchasePacketMenu.index) at₀).castLE (Nat.le_max_right ..)

theorem major_code (a : Attempt) (at₀ : v.widePacketMenuIndex h a) :
    (v.majorIndex h a at₀).val+1=v.widePacketNumber h a at₀ := by cases a <;> rfl

theorem compact_party (a : Attempt) (at₀ : v.widePacketMenuIndex h a) (j : Fin (v.wideBallotParties h a)) :
    (finProdFinEquiv (v.majorIndex h a at₀,j)).val=(v.partyIndex h a at₀ j).val := by cases a <;> rfl

def signedPartyAt (a : Attempt) (neighborCap roleBits laneBits keyBits : ℕ) (read : ℕ→ℕ→V⊕Bool)
    (atom : v.widePacketMenuIndex h a) (i : Fin (v.wideBallotParties h a)) :
    BitNetwork F (Fintype.card (Gathered V D neighborCap)) := by
  cases a with
  | outer ph tr =>
    let ev:=Attempt.outer ph tr
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    letI : Nonempty (Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k))):=⟨names (PayloadStrip.first N 0,none)⟩
    letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    exact menuParty («D»:=D) (width:=neighborCap) («M»:=M) (p:=roleBits) (e:=laneBits) (digits:=keyBits) names v.positive (v.payloadPacketMenu N)
      (Nat.le_max_left ..) (v.wideBallotShape P h width (.attempt ev)).columns (fs ev).histMass read atom i
  | inner ph tr sj ti =>
    let ev:=Attempt.inner ph tr sj ti
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    letI : Nonempty (Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k))):=⟨names (ChainStrip.inlet v.depth 0,none)⟩
    letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    exact menuParty («D»:=D) (width:=neighborCap) («M»:=M) (p:=roleBits) (e:=laneBits) (digits:=keyBits) names v.positive v.purchasePacketMenu
      (Nat.le_max_right ..) (v.wideBallotShape P h width (.attempt ev)).columns (fs ev).histMass read atom i

theorem signedParty_at (a : Attempt) (neighborCap roleBits laneBits keyBits : ℕ) (read : ℕ→ℕ→V⊕Bool)
    (atom : v.widePacketMenuIndex h a) (i : Fin (v.wideBallotParties h a)) :
    v.signedParty h width a neighborCap roleBits laneBits keyBits read (v.partyIndex h a atom i)=
      v.signedPartyAt h width a neighborCap roleBits laneBits keyBits read atom i := by
  cases a with
  | outer ph tr =>
    let ev := Attempt.outer ph tr
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) :=
      SiteNaming.labels
    let : Nonempty (Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k))) := ⟨names (PayloadStrip.first N 0,none)⟩
    let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    exact menuParties_at («D»:=D) (width:=neighborCap) («M»:=M) (p:=roleBits) (e:=laneBits) (digits:=keyBits)
      names v.positive (v.payloadPacketMenu N) (Nat.le_max_left ..)
      (v.wideBallotShape P h width (.attempt ev)).columns (fs ev).histMass read atom i
  | inner ph tr sj ti =>
    let ev := Attempt.inner ph tr sj ti
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) :=
      SiteNaming.labels
    let : Nonempty (Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k))) := ⟨names (ChainStrip.inlet v.depth 0,none)⟩
    let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    exact menuParties_at («D»:=D) (width:=neighborCap) («M»:=M) (p:=roleBits) (e:=laneBits) (digits:=keyBits)
      names v.positive v.purchasePacketMenu (Nat.le_max_right ..)
      (v.wideBallotShape P h width (.attempt ev)).columns (fs ev).histMass read atom i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
