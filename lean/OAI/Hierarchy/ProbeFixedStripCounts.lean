import OAI.Hierarchy.ProbeFixedStripSizes

namespace OAI
/-! # Fixed strip copy masses and the word bounds of purchased socket walks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseFrozen PurchaseStage CatalystArchive
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- The installed catalogue of widths at an arbitrary stage count; both summands
retain their own packet widths. -/
def dateMenu (N : ℕ) :=
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  (PacketWidths.ofMenu (v.payloadPacketMenu N)).either (PacketWidths.ofMenu v.purchasePacketMenu)

variable (z : ℕ)
set_option quotPrecheck false
local notation "N" => Stages z (2^v.W)
local notation "bits" => wordBits z (2^v.W) copies

/-- Each row width and the complete key-by-path slice fit the original native
word, including the stage-by-axis stock table. -/
theorem purchased_table_room (late : v.stripHeight≤z) :
    let groups:=count z (2^v.W) k
    let span:=paths z v.sampler.degree v.depth
    groups≤2^bits ∧ (v.depth+1)*span≤2^bits ∧ groups*span≤2^bits ∧ PurchaseInventory.footprint z N k≤2^bits := by
  let G:=publicStages v.W*(2*k)
  let T:=v.sampler.degree^v.depth
  have stages : N=publicStages v.W := fixed_stage_count z v.W
  have groups_eq : count z (2^v.W) k=G := congrArg (·*(2*k)) stages
  have counter : v.purchaseCounterHeight≤z := (le_max_right ..).trans late
  change (1+G)+(v.depth+1)*T+G*T≤z at counter
  have stride:=linear_count z (2^v.W) copies ((v.depth+1)*T) (by omega)
  have all:=linear_count z (2^v.W) copies (G*T) (by omega)
  have stock:=linear_count z (2^v.W) copies (1+G) (by omega)
  have group : G≤2^bits := by
    have lg : G≤z := by omega
    have le : z≤bits := by rw [wordBits_linear]; omega
    exact (lg.trans le).trans Nat.lt_two_pow_self.le
  dsimp only
  rw [groups_eq,PurchaseInventory.footprint,stages]
  change G≤2^bits ∧ (v.depth+1)*(2^z*T)≤2^bits ∧ G*(2^z*T)≤2^bits ∧ (1+G)*2^z≤2^bits
  exact ⟨group,by simpa only [Nat.mul_left_comm] using stride.le,by simpa only [Nat.mul_left_comm] using all.le,
    by simpa only [Nat.mul_comm] using stock.le⟩

/-- The positive scale and both original copy cells give the very same compact-family denominator. -/
theorem date_copies (P : v.Placement) (width phase trial layer tick : ℕ) :
    let s:=v.nativeBoards P z width
    let menu:=v.dateMenu N
    0<v.copyScale ∧ (s.outer phase trial).copies=menu.copiesAt v.copyScale width ∧
      (s.inner phase trial layer tick).copies=menu.copiesAt v.copyScale width := by
  let outer:=v.ordinary_dimensions P z width (.outer phase trial)
  let inner:=v.ordinary_dimensions P z width (.inner phase trial layer tick)
  have joint : (v.dateMenu N).copiesAt v.copyScale width=v.menu.copiesAt v.copyScale width := by
    rw [show N=publicStages v.W from fixed_stage_count z v.W]
    rfl
  exact ⟨v.clock.base_pos,outer.2.trans joint.symm,inner.2.trans joint.symm⟩

/-- The actual padded market reserves at least the full height-indexed payload
prefix at each phase and each retry. -/
theorem date_market_rows (P : v.Placement) (width : ℕ) (a : Attempt) :
    2^z≤(v.nativeFormats P z width a).market.rows := by
  let s:=v.nativeBoards P z width
  have rows := candidate_count F v.mesh (v.privateArena P z width) P.joint.initial s a
  have positiveGroups : 0<count z (2^v.W) k := by
    rw [PurchaseFrozen.count_eq]
    exact Nat.mul_pos (by omega) (Nat.mul_pos (by decide) v.positive)
  have degree : 0<s.sampler.degree := v.sampler_live
  change 2^z≤((formats F v.mesh (v.privateArena P z width) P.joint.initial s) a).market.rows
  rw [rows,PurchaseFrozen.paths]
  calc
    2^z = 1*(2^z*1) := by rw [Nat.mul_one,Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul positiveGroups (Nat.mul_le_mul_left _ (pow_pos degree _))

/-- Even an unpadded payload scan has enough word space for its full row prefix. -/
theorem date_prefix_fit : 2^z<2^bits :=
  Nat.pow_lt_pow_right (by decide) (by rw [wordBits_linear]; omega)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
