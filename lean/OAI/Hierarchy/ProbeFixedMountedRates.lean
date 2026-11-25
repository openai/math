import OAI.Hierarchy.ProbeFixedQuoteDigits

namespace OAI
/-! # Mounted packet indices have the calibrated fixed physical rate and copy count -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StripDirectory
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def PacketConditions {J : Type*} (roles : ℕ) (terms widths rates : J → ℕ) (margin : ℝ) (width : ℕ) : Prop :=
  v.menu.margin ≤ margin ∧ ∀i,
    terms i ≤ v.menu.alphabet ∧
    (roles:ℝ)*v.menu.maximum*(1/(v.precision:ℝ)) ≤ widths i*v.menu.margin/2 ∧
    copied (v.copyScale*commonWidth v.menu.width) (widths i) width ≤ v.menu.copiesAt v.copyScale width ∧
    v.menu.copiesAt v.copyScale width ≤ copied v.copyScale (widths i) width ∧
    (∃ j : v.payloadPackets.index ⊕ v.boughtPackets.index,rates i=v.menu.rate j) ∧
    0<widths i ∧ 2*(v.actualK*widths i)≤width

theorem mounted_payload {N : ℕ} (count : N=publicStages v.W) (width : ℕ) (large : v.widthFloor ≤ width) :
    let m:=payloadMenu F N k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt v.geometry.cutoff.1
      v.cost.payload v.cost.payload_nonneg 0
    PacketConditions v (Fintype.card (PayloadRole N k)) (fun i=>(m.packet i).terms)
      (fun i=>(m.packet i).width) (fun i=>packetRate (m.packet i)) m.margin width := by
  subst N
  intro m
  refine ⟨min_le_left ..,?_⟩
  intro i
  have pair := ((v.copied_widths width large).2 (.inl i)).2
  exact ⟨v.menu.alphabet_ge (.inl i),v.payload_precision i,pair.1,pair.2,⟨Sum.inl i,rfl⟩,Nat.zero_lt_of_lt (v.payloadPackets.wide i),by
    rw [← Nat.mul_assoc]
    exact ((v.copied_widths width large).2 (.inl i)).1⟩

theorem mounted_purchased (width : ℕ) (large : v.widthFloor ≤ width) :
    let m:=v.boughtPackets
    PacketConditions v (Fintype.card (PurchasedRole v.depth k)) (fun i=>(m.packet i).terms)
      (fun i=>(m.packet i).width) (fun i=>packetRate (m.packet i)) m.margin width := by
  intro m
  refine ⟨min_le_right ..,?_⟩
  intro i
  have pair := ((v.copied_widths width large).2 (.inr i)).2
  exact ⟨v.menu.alphabet_ge (.inr i),v.bought_precision i,pair.1,pair.2,⟨Sum.inr i,rfl⟩,Nat.zero_lt_of_lt (v.boughtPackets.wide i),by
    rw [← Nat.mul_assoc]
    exact ((v.copied_widths width large).2 (.inr i)).1⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
