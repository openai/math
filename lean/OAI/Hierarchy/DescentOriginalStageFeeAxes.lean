import OAI.Hierarchy.DescentEarnedStageInvoice
import OAI.Hierarchy.DescentTerminalFormatCalibration

namespace OAI
/-! # The common published dimensions used in the last host invoice -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentPrimitivePalette
open DescentResetGates Filter
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec) (drift t f g reset τ B h M:ℕ)
local notation "J_" => Nat.log 2 h/(2*B)
local notation "S_" => stageNumbers G t J_ f g reset M (tail τ J_)
local notation "k_" => groupBits t J_ (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "j_" => Nat.clog 2 (NativeBranch.localLimit G S_)
local notation "q_" => 2^j_*(G.b^(t*J_)*G.b)
local notation "W_" => NativeBranch.binLimit (k:=k_) S_
local notation "p_" => W_*(h/(16*(q_*W_)))
local notation "s_" => (S_).firstWidth G.b p_
local notation "K_" => NativeBranch.privateSlotCapacity G S_ drift
local notation "nodes_" => (S_).epochPower^(S_).localTokenExponent
local notation "sites_" => (S_).groupCount (S_).length*2^k_
local notation "tags_" => DescentBundleTagKeys.capacity (colors G s_ ((S_).grainAt G.b p_ 0) op)
  (max 8 (2^(S_).capGain)) K_ p_ drift

structure StageFeeAxes : Prop where
  mode : q_*p_≤ h+1
  keys : DescentTerminalChronologicalBooks.Keys q_ tags_ K_ nodes_ K_ p_ sites_ p_≤ M
  slots : 2^j_≤ scale J_ (localSocketRate G t g)
  bulk : h≤32*(2^j_*s_)
  dates : (S_).length≤ M
  inventory : ∀E,M*(h+1)*2^J_≤64*(((S_).copies*s_)*(M+2^J_*E))

set_option maxHeartbeats 1200000 in
theorem original_stage_fee_axes (branch:G.b≤2^(capRate G t g)) (large:20≤ B)
    (reserve:2*localSocketRate G t g≤τ)
    (pack:2*(localSocketRate G t g+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)≤ B)
    (routes:2*((τ+groupRate G t f g reset+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)≤ B)
    (shelves:2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤ B) :
    ∀ᶠ h:ℕ in atTop,∀M:ℕ,2^h≤ M→ StageFeeAxes G op drift t f g reset τ B h M:=by
  filter_upwards [paid_isa_inventory G t f g reset τ B large reserve pack,
    early_native_packing G t f g reset τ B large reserve pack,
    early_matrix_words G t f g reset τ B large,
    terminal_format_calibration_full G op drift t f g reset τ B branch (by omega) shelves routes] with h paid layout clocks menu
  intro M ambient
  have half:2^(h/2)≤ M:=(Nat.pow_le_pow_right (by decide) (Nat.div_le_self ..)).trans ambient
  have mode {bits fields : ℕ} (small : bits+2*fields ≤ h/2) : fields ≤ h+1 := by omega
  exact ⟨mode (menu M).1, (menu M).2.2.2.2.2.trans half,
    (native_socket_scale G t (Nat.log 2 h/(2*B)) f g reset M τ).2.2.1,
    (layout M).2.2.2.2, (clocks M).2.1.trans half, paid M⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
