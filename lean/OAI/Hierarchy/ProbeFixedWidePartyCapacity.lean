import OAI.Hierarchy.ProbeFixedWidePartyCircuit
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbePackedPartyRead

namespace OAI
/-! # Permanent widths of the two original signed party templates -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing Diagonal
open scoped Classical BigOperators
variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
    {k r : ℕ} [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E} (P : Packet F edge req)
def Packet.partyUnit (B : Type) [Fintype B] :=
  1+P.width*Fintype.card A+(∑t,∑e,P.count t e)+Fintype.card B*P.selectorBits+
    ∑i,P.aperturePerCopy B i

omit [Nonempty (Fin k)] in
theorem Packet.unit_aperture (i : Fin k) : P.aperturePerCopy B i≤P.partyUnit B := by
  have hi:=Finset.single_le_sum (f:=P.aperturePerCopy B) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  unfold Packet.partyUnit
  omega

omit [Nonempty (Fin k)] in
theorem Packet.unit_room (G : PortGraph (Fin k) B) (i : Fin k) (s : (portGraph k).Port i) (r : ℕ) :
    G.chordWidths (fun _=>r*P.selectorBits) s.val.1+
      r*SiteHardware.widthCap (SiteHardware.localWidth P i)≤r*P.partyUnit B :=
  (P.aperture_room G i s r).trans (Nat.mul_le_mul_left _ (P.unit_aperture i))

omit [Nonempty (Fin k)] in
theorem Packet.unit_middle (G : PortGraph (Fin k) B) (i : Fin k) (s : (portGraph k).Port i)
    (h : Diagonal.MotifOuterTerms.Histogram (Fin P.terms) r) :
    (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) s.val.1≤r*P.partyUnit B := by
  change P.outputWidths h s.val.1+G.chordWidths (fun _=>r*P.selectorBits) s.val.1≤_
  rw [Nat.add_comm]
  exact (Nat.add_le_add_left (P.output_socket_room h i s) _).trans (P.unit_room G i s r)

variable [Nonempty E] {box : Set (E→ℝ)} {ε c : ℝ} {N : ℕ} (menu : FixedMenu F edge req box ε c N)
def FixedMenu.signedFuel (B : Type) [Fintype B] : ℕ := Finset.univ.sup (fun a : menu.index=>(menu.packet a).partyUnit B)

theorem FixedMenu.signedFuel_at (a : menu.index) : (menu.packet a).partyUnit B≤ menu.signedFuel B :=
  Finset.le_sup (s:=Finset.univ) (f:=fun i=>(menu.packet i).partyUnit B) (Finset.mem_univ a)

end Hierarchy.Probe

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Probe ProbeStage CoreBoard AdaptiveProbe Strip StripChart StripDirectory
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
def signedPartyFuel (a : Attempt) :=
  match a with
  | .outer ..=>(v.payloadPacketMenu N).signedFuel (TreeLink (PayloadStrip.edgeCount N) k)
  | .inner ..=>v.purchasePacketMenu.signedFuel (TreeLink (ChainStrip.edgeCount v.depth) k)

def partyLaneBits (a : Attempt) (unitCost : ℕ) :=
  Nat.log 2 (max (v.wideNeighborCap width unitCost) ((v.nativeFormats P h width a).histMass*v.signedPartyFuel h a))+1
def partyRoleBits := Nat.log 2 (2*v.widePacketRoles h+v.widePacketDegree)+1
def partyKeyBits := Nat.log 2 v.widePacketDegree+1

private theorem cap_gt (x : ℕ) : x<2^(Nat.log 2 x+1) :=
  Nat.lt_pow_succ_log_self (by decide) _

theorem party_lane_room (a : Attempt) (unitCost : ℕ) :
    v.wideNeighborCap width unitCost<2^(v.partyLaneBits h width a unitCost) ∧
      (v.nativeFormats P h width a).histMass*v.signedPartyFuel h a<2^(v.partyLaneBits h width a unitCost) :=
  ⟨(Nat.le_max_left ..).trans_lt (cap_gt _),(Nat.le_max_right ..).trans_lt (cap_gt _)⟩

theorem party_role_room : 2*v.widePacketRoles h+v.widePacketDegree<2^(v.partyRoleBits h) := cap_gt _
theorem party_key_room : v.widePacketDegree<2^v.partyKeyBits := cap_gt _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
