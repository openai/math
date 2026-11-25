import OAI.Hierarchy.ProbeFixedFeedWordRoom
import OAI.Hierarchy.ProbeFixedReplayFeed
import OAI.Hierarchy.ProbeFixedPurchaseEntry
import OAI.Hierarchy.ProbeFixedStockWindow

namespace OAI
/-! # Reserve feed acquired by the actual parent purchase and its common boot page -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open ThreeFlat.RAM
open StockCommit PurchaseStage
open scoped Fin.CommRing Classical BigOperators
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "stride" => v.keepLimit*width+1
local notation "table" => sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps stride
local notation "Good" => FeedLayout.Good z N k

/-- The native reserve-slice lookup comes from the finite common boot input,
including the physically last slice and the largest permitted saved amount. -/
theorem replay_slice_boot {jobs phases size : ℕ} (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (rest : Boot.Tape z (2^v.W)) (markets : Fin jobs→Market z (2^v.W) k) (layout : Boot.Layout markets size)
    (steps : P.joint.steps=v.mesh.reserveSteps) (digits : P.joint.cap*P.joint.width=v.keepLimit*width)
    (start : 2^z≤P.joint.initial) (heap : heapEnd z (2^v.W) copies≤P.joint.initial)
    (fits : JointHeader.stop P.joint z N k phases ≤ size)
    (before : ∀t,JointHeader.stop P.joint z N k phases≤Boot.low (markets t)) :
    let m:=Boot.booted markets size (JointHeader.words P.joint z (2^v.W) N k phase π (fun _=>0) rest)
    ∃ fixture : Memory W,∀x,(table).base≤x→x<(table).base+v.mesh.reserveSteps*stride →
      m x=feedAdvice table v.mesh.reserveSteps stride fixture x := by
  intro m
  let source := JointHeader.inventory P.joint z N k (fun _=>0) (Boot.permutationWords π rest)
  refine ⟨source,?_⟩
  have origin := (JointHeader.integer_origins («N»:=N) P.joint phase π (fun _=>0) rest markets layout
    Nat.one_le_two_pow start (heap.trans (Nat.le_add_right ..)) fits before).1
  simpa only [FeedROM.sliceBank,GlobalTests.rows,steps,digits] using origin

/-- Every physically executed purchase gives the three chronological
reserve cases of Acquisition. The two words of every clipped result, the
final account and the signed bill all refer to this same actual chart. -/
theorem replay_purchase_feed (mem fixture : Memory W)
    (stock : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (steps : P.joint.steps=v.mesh.reserveSteps) (digits : P.joint.cap*P.joint.width=v.keepLimit*width)
    (addressRoom : (G).endAddress v.mesh<2^W) (payload : width≤2^z) (dimension : 2*v.keepLimit+1≤2^z)
    (rom : ∃source : Memory W,∀x,(table).base≤x→x<(table).base+v.mesh.reserveSteps*stride→
      mem x=feedAdvice table v.mesh.reserveSteps stride source x)
    (u a : ℕ) (hu : u<v.mesh.inject+v.mesh.cool) (ha : a<v.mesh.outerFuel)
    (data : StockBound.TrialData C (.outer u a) (trialState C mem u a) fixture (f (.outer u a)).pricedArea
      (f (.outer u a)).stockSource (v.stamp P z width r banks src tab dst owners (.outer u a))
      v.keepLimit width ((G).base v.mesh (.attempt (.outer u a))))
    (buy : observedMode C mem u a=3) :
    ((A).inner C mem u a v.mesh.reserveSteps 0=(A).trial C mem u (a+1)) ∧
    ∀ j<v.mesh.reserveSteps,
      let before:=(A).inner C mem u a j v.mesh.innerFuel
      let finish:=(A).inner C mem u a (j+1) 0
      let req:=(A).bank.replayFeed v.mesh.reserveSteps j ((A).trial C mem u a) before
      (∀i : Good,finish.bits i=min (req i) (v.keepLimit*width)) ∧
        finish.paid=before.paid+pairing (bitStock width (spillBits v.keepLimit width req)) (A).box := by
  obtain ⟨source,sliceData⟩:=rom
  obtain ⟨_,head⟩:=outer_slot C mem u a hu ha stock.mounted_all
  have scheduled : Event.attempt (.outer u a)∈events (C).mesh := by rw [head.events];simp
  have original (i : Good) := (v.purchase_initial_stock P z width r banks src tab dst owners mem fixture u a
    scheduled head.currentReady data buy (fun g=>(stock.slot head).1 g) i).2.1
  have room:=v.replay_slice_room P z width steps digits
  have fits:=v.replay_headroom z width payload dimension
  refine ⟨v.replay_terminal P z width r banks src tab dst owners mem u a,?_⟩
  intro j hj before finish req
  exact ⟨fun i=>(v.replay_feed_words P z width r banks src tab dst owners mem source stock room addressRoom
    fits sliceData u a hu ha data.toTrialLayout buy original j hj i).1,
    v.replay_feed_paid P z width r banks src tab dst owners mem source stock room addressRoom fits
      sliceData u a hu ha data.toTrialLayout buy original j hj⟩

/-- The reserve readback on the original finite input, with all addressable
slices supplied by the same boot as the active stock and chronological prices. -/
theorem boot_replay_purchase {jobs phases size : ℕ} (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (rest : Boot.Tape z (2^v.W)) (markets : Fin jobs→Market z (2^v.W) k)
    (boot : Boot.Layout markets size) (steps : P.joint.steps=v.mesh.reserveSteps)
    (digits : P.joint.cap*P.joint.width=v.keepLimit*width) (start : 2^z≤P.joint.initial)
    (heap : heapEnd z (2^v.W) copies≤P.joint.initial) (fits : JointHeader.stop P.joint z N k phases ≤ size)
    (before : ∀t,JointHeader.stop P.joint z N k phases≤Boot.low (markets t))
    (room : (G).endAddress v.mesh<2^W) (payload : width≤2^z) (dimension : 2*v.keepLimit+1≤2^z)
    (fixture : Memory W) (u a : ℕ) (hu : u<v.mesh.inject+v.mesh.cool) (ha : a<v.mesh.outerFuel) :
    let mem:=Boot.booted markets size (JointHeader.words P.joint z (2^v.W) N k phase π (fun _=>0) rest)
    StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width) →
    StockBound.TrialData C (.outer u a) (trialState C mem u a) fixture (f (.outer u a)).pricedArea
      (f (.outer u a)).stockSource (v.stamp P z width r banks src tab dst owners (.outer u a))
      v.keepLimit width ((G).base v.mesh (.attempt (.outer u a))) →
    observedMode C mem u a=3 →
    ((A).inner C mem u a v.mesh.reserveSteps 0=(A).trial C mem u (a+1)) ∧
    ∀ j<v.mesh.reserveSteps,
      let pre:=(A).inner C mem u a j v.mesh.innerFuel
      let out:=(A).inner C mem u a (j+1) 0
      let req:=(A).bank.replayFeed v.mesh.reserveSteps j ((A).trial C mem u a) pre
      (∀i : Good,out.bits i=min (req i) (v.keepLimit*width)) ∧
        out.paid=pre.paid+pairing (bitStock width (spillBits v.keepLimit width req)) (A).box := by
  intro mem stock data buy
  exact v.replay_purchase_feed P z width r banks src tab dst owners mem fixture stock steps digits room payload
    dimension (v.replay_slice_boot P z width phase π rest markets boot steps digits start heap fits before)
    u a hu ha data buy

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
