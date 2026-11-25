import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProbeInstalledActivation

namespace OAI
/-! # Actual purchase census and replay energy in the fixed billed account -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe OuterBank ProbeStage ProbeStage.Native
open PurchaseCT PurchaseFrozen StripDirectory StripChart
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners

theorem activation_stock_floor (a : Attempt) :
    (f a).market.shelf.stockBase+PurchaseInventory.footprint z N k≤(G).base v.mesh (.attempt a) := by
  have lo:=(v.stock_source_lows P z width a).1
  change (f a).market.shelf.stockBase+(f a).pricedArea.goods≤(G).base v.mesh (.attempt a) at lo
  simpa only [v.stock_goods P z width a] using lo

theorem activation_guard_floor (a : Attempt) : (G).base v.mesh (.attempt a)≤(C).stopAt a :=
  (v.stock_order P z width a).2.2

/-- The parent sampler snapshot reads the preceding physical stock on both
sides of its stop guard and its discrepancy pass. -/
theorem activation_parent_floor (phase trial : ℕ) :
    let u:=Attempt.outer phase trial
    let sh:=v.frozenMarket P z width phase trial
    sh.shelf.stockBase+PurchaseInventory.footprint z N k≤(C).stopAt u ∧
      sh.shelf.stockBase+PurchaseInventory.footprint z N k ≤ sh.failures.base := by
  intro u sh
  have low:=v.activation_stock_floor P z width u
  exact ⟨low.trans (v.activation_guard_floor P z width r banks src tab dst owners u),
    low.trans (v.stock_order P z width u).1⟩

theorem activation_replay_protected (a : Attempt) (i : Commodity (Fin (2^z)) N k) :
    protected C ((f a).market.shelf.stockBase+PurchaseInventory.slot i) (.attempt a) :=
  (v.event_prefix P z width r banks src tab dst owners (.attempt a) _
    ((Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _).trans_le (v.activation_stock_floor P z width a))).1

/-- Prices at the frozen parent use the stock of the actual outer entry. -/
theorem activation_frozen_quotes (m : Memory W) (phase trial pay axis : ℕ) (s : PhasePrice) :
    let sh:=v.frozenMarket P z width phase trial
    stageQuotes (z:=z) (d:=2^v.W) (k:=k) s pay axis sh.shelf.stockBase
        (v.frozenInput P z width r banks src tab dst owners m phase trial)=
      stageQuotes s pay axis sh.shelf.stockBase (trialState C m phase trial) := by
  have floors:=v.activation_parent_floor P z width r banks src tab dst owners phase trial
  exact outer_frozen_quotes C m _ phase trial pay axis s floors.1 floors.2

/-- The potential optimizer at the real parent is the frozen clock's posted
signed price function on every commodity, including each payload row. -/
theorem activation_start_quote (m : Memory W) (phase trial : ℕ) :
    let t:=outerTime v.mesh v.finish phase
    let u:=Attempt.outer phase trial
    let sh:=v.frozenMarket P z width phase trial
    maximizer (A).a (A).M t (A).coefficient (A).box ((A).bank.units (A).payloadWidth ((A).trial C m phase trial))=
      stageQuotes (deadline v.mesh v.finish (v.basePhase width) u) 0 1 sh.shelf.stockBase
        (v.frozenInput P z width r banks src tab dst owners m phase trial) := by
  intro t u sh
  let bs:=v.issued P z width r banks src tab dst owners
  let seedCash:=coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius
  have phaseCount : 2*rounds (2^v.W)+1=publicStages v.W:=by unfold publicStages rounds;omega
  have coeff : (v.W:ℝ)⁻¹^4/((N:ℝ)*(probeHeat v.W)^2)=probeBonus v.W:=by
    rw [show N=publicStages v.W from fixed_stage_count z v.W];rfl
  have start:=native_live_quotes v.mesh G P.joint.initial (build F B)
    (fun a addr=>StripChart.capacity F B a addr P.joint.initial) (StripChart.source F B)
    width v.precision bs seedCash v.a v.radius v.W (probeHeat v.W) t u (trialState C m phase trial)
  dsimp only at start
  simp only [phaseCount,coeff] at start
  exact start.trans (v.activation_frozen_quotes P z width r banks src tab dst owners m phase trial 0 1
    (deadline v.mesh v.finish (v.basePhase width) u)).symm

/-- Payload coordinates are indexed by the original input rows under either
stage enumeration, so summing their frozen prices needs no stage casts. -/
theorem activation_start_payload (m : Memory W) (phase trial : ℕ) :
    let t:=outerTime v.mesh v.finish phase
    let u:=Attempt.outer phase trial
    let sh:=v.frozenMarket P z width phase trial
    let x:=maximizer (A).a (A).M t (A).coefficient (A).box ((A).bank.units (A).payloadWidth ((A).trial C m phase trial))
    (∑ i : Fin (2^z),x (.inl i)) =
      ∑ i : Fin (2^z),stockQuotes (z:=z) (d:=2^v.W) (k:=k)
        (deadline v.mesh v.finish (v.basePhase width) u) 0 1 sh.shelf.stockBase
        (v.frozenInput P z width r banks src tab dst owners m phase trial) (.inl i) :=
  congrArg (fun x : Commodity (Fin (2^z)) N k→ℝ=>∑i : Fin (2^z),x (.inl i))
    (v.activation_start_quote P z width r banks src tab dst owners m phase trial)

/-- Testing a reserve retry preserves every opening stock coordinate, including
the physical prices used by its replay check. -/
theorem activation_replay_word (m : Memory W) (phase trial layer tick : ℕ)
    (hp : phase<v.mesh.inject+v.mesh.cool) (hh : trial<v.mesh.outerFuel)
    (hj : layer<v.mesh.reserveSteps) (hb : tick<v.mesh.innerFuel)
    (installed : Calendar.mounted C (events (C).mesh) m) (i : Commodity (Fin (2^z)) N k) :
    let a:=Attempt.inner phase trial layer tick
    let x:=(f a).market.shelf.stockBase+PurchaseInventory.slot i
    replayScoreMemory C m phase trial layer tick x=innerState C m phase trial layer tick x := by
  obtain ⟨_,cut⟩:=inner_slot C m phase trial layer tick hp hh hj hb installed
  exact replay_prior C m phase trial layer tick _ cut.currentReady
    (v.activation_replay_protected P z width r banks src tab dst owners (.inner phase trial layer tick) i)

theorem activation_replay_quotes (m : Memory W) (phase trial layer tick pay axis : ℕ) (s : PhasePrice)
    (hp : phase<v.mesh.inject+v.mesh.cool) (hh : trial<v.mesh.outerFuel)
    (hj : layer<v.mesh.reserveSteps) (hb : tick<v.mesh.innerFuel)
    (installed : Calendar.mounted C (events (C).mesh) m) :
    let base:=(f (.inner phase trial layer tick)).market.shelf.stockBase
    stageQuotes (z:=z) (d:=2^v.W) (k:=k) s pay axis base (replayScoreMemory C m phase trial layer tick)=
      stageQuotes s pay axis base (innerState C m phase trial layer tick) := by
  apply stageQuotes_frame
  exact v.activation_replay_word P z width r banks src tab dst owners m phase trial layer tick hp hh hj hb installed

/-- The origin repair board allocates one rounded power-of-two bank for this
very count of group-by-path candidates. -/
theorem activation_padded (phase trial : ℕ) :
    (v.frozenMarket P z width phase trial).rows ≤ 2^(f (.outer phase trial)).batch.decisionBits := by
  let n:=count z (2^v.W) k*paths z v.sampler.degree v.depth
  change n≤2^(ProtocolRAMPurchaseSampler.bits n)
  exact (ProtocolRAMPurchaseSampler.lt_span n).le

/-- A genuine purchase identifies the account's opening count with the live
chains of that parent snapshot. The two temperatures use the stock actually
read at the parent and at this reserve retry. -/
theorem activation_coordinates (mem fixture : Memory W) (π : Equiv.Perm (Fin (2^z)))
    (phase trial layer tick : ℕ) (hp : phase<v.mesh.inject+v.mesh.cool)
    (hh : trial<v.mesh.outerFuel) (hj : layer<v.mesh.reserveSteps) (hb : tick<v.mesh.innerFuel)
    (archive : ArchiveRoom C mem (v.mesh.inject+v.mesh.cool)) (mountedAll : Calendar.mounted C (events (C).mesh) mem)
    (bought : observedMode C mem phase trial=3) :
    let sh:=v.frozenMarket P z width phase trial
    let frozen:=v.frozenInput P z width r banks src tab dst owners mem phase trial
    let replay:=Attempt.inner phase trial layer tick
    let tested:=replayScoreMemory C mem phase trial layer tick
    let s:=outerTime v.mesh v.finish phase
    let later:=publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W)
      (reserveTime v.mesh v.finish phase layer) width v.precision
    let live:=Fintype.card (LiveChains sh.sampler π sh.depth
      (actualMarks (k:=k) sh.shelf sh.phase sh.temperature sh.kind frozen))
    sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared sh.sampler sh.depth fixture i frozen) →
    ((2*((purchaseCount C mem phase trial:ℝ)*(Λ*(dyadicScale v.W)^p)+
      (2^z:ℕ)*probeDensity k v.W*purchaseReward k v.W/4) ≤
      s*divergence (A).a (A).M (A).coefficient
        (maximizer (A).a (A).M s (A).coefficient (A).box ((A).bank.units (A).payloadWidth ((A).trial C mem phase trial)))
        (maximizer (A).a (A).M (replayTime s (C).mesh.reserveSteps layer) (A).coefficient (A).box
          ((A).bank.units (A).payloadWidth ((A).inner C mem phase trial layer tick)))) ↔
     2*((live:ℝ)*(Λ*(dyadicScale v.W)^p)+(2^z:ℕ)*probeDensity k v.W*purchaseReward k v.W/4) ≤
       s*divergence v.a v.radius (bonus (probeBonus v.W))
         (stageQuotes (z:=z) (d:=2^v.W) (k:=k) sh.phase 0 1 sh.shelf.stockBase frozen)
         (stageQuotes (z:=z) (d:=2^v.W) (k:=k) later 0 1 (f replay).market.shelf.stockBase tested)) := by
  intro sh frozen replay tested s later live incoming prepared
  have floors:=v.activation_parent_floor P z width r banks src tab dst owners phase trial
  obtain ⟨_,atReplay⟩:=inner_slot C mem phase trial layer tick hp hh hj hb mountedAll
  have stageCount : 2*rounds (2^v.W)+1=publicStages v.W:=by unfold publicStages rounds; omega
  have coeff : (v.W:ℝ)⁻¹^4/((N:ℝ)*(probeHeat v.W)^2)=probeBonus v.W:=by
    rw [show N=publicStages v.W from fixed_stage_count z v.W]
    rfl
  let feeds:=feedColumns («N»:=N) v.mesh G f P.joint.initial width v.keepLimit
  let issued:=v.issued P z width r banks src tab dst owners
  let seedCash:=coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius
  have formula:=Calendar.live_activation_iff v.mesh G P.joint.initial (build F B)
    (fun a addr=>StripChart.capacity F B a addr P.joint.initial) (StripChart.source F B)
    v.finish v.a v.radius v.W rfl width v.precision (Λ*(dyadicScale v.W)^p) (probeDensity k v.W)
    (purchaseReward k v.W) seedCash issued feeds (P.catalogue.sink r banks src tab dst owners)
    P.catalogue.idBase (fun a=>(StripChart.header F B a).fieldTerm) (StripChart.id F B P.catalogue)
    mem fixture π phase trial layer tick (v.mesh.inject+v.mesh.cool)
  dsimp only at formula
  simp only [stageCount,coeff] at formula
  exact formula archive hp hh (v.activation_padded P z width phase trial) bought incoming prepared
    floors.1 floors.2 atReplay.currentReady (v.activation_replay_protected P z width r banks src tab dst owners replay)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
