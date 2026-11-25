import OAI.Hierarchy.ProbeFixedGlobalVotes
import OAI.Hierarchy.ProbeFixedNativeStockRun

namespace OAI
/-! # A uniform size cutoff and the two global tests of the original bounded-stock run -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

def globalHeight :=
  max (GlobalTests.kinds (publicStages v.W) k)
    (GlobalTests.unitBound ⟨0,0,0,v.precision⟩ (publicStages v.W) k (v.basePhase 0))

variable (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "layout" => JointHeader.scores P.joint z N k

theorem global_numeric (large : v.globalHeight≤z) (precision : P.joint.precision=v.precision) :
    GlobalTests.kinds N k≤z ∧ GlobalTests.unitBound layout N k (v.basePhase width)<2^W := by
  have hn : N=publicStages v.W := fixed_stage_count z v.W
  constructor
  · rw [hn]
    exact (le_max_left ..).trans large
  · have small : GlobalTests.unitBound layout N k (v.basePhase width)≤z := by
      rw [hn]
      change (∑i : Fin (GlobalTests.kinds (publicStages v.W) k),
        ⌊(P.joint.precision:ℝ)*GlobalTests.upper (v.basePhase width) i.val⌋₊)≤z
      rw [precision]
      exact (le_max_right ..).trans large
    apply small.trans_lt
    exact (Nat.lt_two_pow_self (n:=z)).trans_le
      (Nat.pow_le_pow_right (by decide) (by rw [wordBits_linear]; omega))

variable (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "freq" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
variable (mem : Memory (wordBits z (2^v.W) copies)) (S : StockBound.Run (v.nativeChart P z width r banks src tab dst owners) (v.stockBanks P z width) mem z (Stages z (2^v.W)) k (v.keepLimit*width))

include S in
theorem global_source_of_run («public» : (H).Resident mem) (prices : InitialPrices P.joint z N k freq (fun _=>0) mem)
    (precision : P.joint.precision=v.precision) (budget : P.joint.cap*P.joint.width=v.keepLimit*width)
    (large : v.globalHeight≤z) (fit : v.keepLimit*width+1≤2^z)
    (phase trial : ℕ) (hp : phase<v.mesh.inject+v.mesh.cool) (ht : trial<v.mesh.outerFuel) :
    let u:=Attempt.outer phase trial
    let pg:=DeadlineROM.scorePage v.mesh layout z N k u
    let s:=outerTime v.mesh v.finish phase
    GlobalTests.ReadStock A ((A).trial C mem phase trial) pg (f u).stockSource.old
      (GlobalTests.price A s (probeBonus v.W) (routeCap N v.radius) pg.precision)
      (prepared C u (trialState C mem phase trial)) := by
  dsimp only
  have bounds:=v.global_numeric P z width large precision
  have native:=v.stock_cap C rfl (v.privateArena P z width) f P.joint.initial
    (v.emptyReserve P z width).base width (v.issued P z width r banks src tab dst owners) mem S
  have stride : (layout).stride≤2^z := by
    change P.joint.cap*P.joint.width+1≤2^z
    rwa [budget]
  apply v.global_source P z width r banks src tab dst owners phase trial mem hp ht S.mounted_all «public» prices
    precision bounds.1 stride bounds.2
  intro i
  change ((A).trial C mem phase trial).bits i<P.joint.cap*P.joint.width+1
  rw [budget]
  exact Nat.lt_succ_of_le (native.1 phase hp trial ht.le i)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
