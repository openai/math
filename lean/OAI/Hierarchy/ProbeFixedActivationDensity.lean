import OAI.Hierarchy.ProbeFixedActivationParent
import OAI.Hierarchy.ProbeFixedDiscrepancyCeilings
import OAI.Hierarchy.ProbeFixedGlobalRun
import OAI.Hierarchy.ProbeFixedGlobalVotes
import OAI.Hierarchy.ProbeFixedFailurePopulation
import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProtocolRAMCalendarEconomicHistory
import OAI.Hierarchy.ProbeFixedScalarQuoteCells
import OAI.Hierarchy.ProbeInstalledPayloadWords
import OAI.Hierarchy.ProbeMarketStockFrame
import OAI.Hierarchy.ProbeDiscrepancyBoot

namespace OAI
/-! # Mode three on the native outer ballot forces positive density on its frozen shelf -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseCT StripDirectory
open AttemptGate PurchaseStage PurchaseFrozen CoreBoard StripChart OuterBank
open ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing

private theorem restage_property {z d k w : ℕ} (phase : PhasePrice) (base : ℕ) (m : Memory w)
    (property : (L : ℕ) → (Commodity (Fin (2^z)) L k → ℝ) → Prop) :
    property _ (stageQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base m) ↔
      property _ (stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base m) := by
  let pull {n l : ℕ} (e : n=l) (x : Commodity (Fin (2^z)) l k → ℝ) :
      Commodity (Fin (2^z)) n k → ℝ
    | .inl p => x (.inl p)
    | .inr ((p,t),j) => x (.inr ((p,t.cast e),j))
  have changeStages {n l : ℕ} (e : n=l) (x : Commodity (Fin (2^z)) l k → ℝ) :
      property n (pull e x) ↔ property l x := by
    subst l
    have same : pull rfl x=x := by funext i; rcases i with p|⟨⟨p,t⟩,j⟩ <;> rfl
    rw [same]
  let len : (permutationFabric z d).shapes.length = 2*rounds d+1 :=
    template_length (radix z d) (radix_pos z d) (rounds d) Unit (2^z)
  let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base m
  have same : stageQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base m = pull len x := by
    funext i
    rcases i with p | ⟨⟨p,t⟩,j⟩ <;> rfl
  rw [same]
  exact changeStages len x

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

private theorem stage_trigger {w labels goods z L : ℕ} (C : Chart w labels goods) (mem : Memory w)
    (u h : ℕ) (stageCount : L=publicStages v.W) (space : TestRoom (repair C (.outer u h)) w)
    (buy : observedMode C mem u h=3) (s : ℝ) (hs : 0<s) (s1 : s≤1)
    (x : Commodity (Fin (2^z)) L k → ℝ)
    (quad : (v.a:ℝ)*(∑i,x i^2)/(2^z:ℕ)≤(v.W:ℝ)⁻¹^4)
    (box : ∀i,PayloadStrip.rowQuotes x i∈Set.Icc 0 (PayloadStrip.ceiling L k v.radius))
    (cut : (outerCheck C u h).bound=⌈4*v.toleranceAt*(2^z:ℕ)*v.precision⌉₊)
    (pick : Fin (2^z) ↪ Fin (outerCheck C u h).rows)
    (measured : ∀i,∀name : PayloadStrip.Naming L k,PayloadStrip.namedError F L k name v.radius
      (PayloadStrip.rowQuotes x i)≤((outerCheck C u h).score (outerScoreMemory C mem u h) (pick i):ℝ)/v.precision+v.toleranceAt)
    (vote : envelope v.W ((dyadicScale v.W)^8) s < score v.a v.radius (bonus (probeBonus v.W)) x/(2^z:ℕ) ∨
      s=1 ∧ (2^z:ℕ)<∑i,x (.inl i)) :
    (Fintype.card (Fin (2^z)×Fin L):ℝ)≤∑b,∑j : Fin k×Bool,s*(rise v.radius (x (.inr (b,j)))/probeHeat v.W)^2 := by
  subst L
  exact physical_trigger_of_votes C mem u h v.geometry space buy v.clock.precision_pos v.a s hs s1 x
    (fun _=>Fintype.equivFin _) quad box cut pick (fun i=>measured i _) vote

/-- The frozen shelf and the outer price instruction read identical retained stock cells.
Both instruction frames lie above the entire stock bank, including all signed directions. -/
theorem purchase_score_inputs (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
    (src tab dst : ℕ) (owners : Bank) (mem : Shelf.Mem z (2^v.W))
    (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel) (stock : ℕ→ℕ) :
    let C:=v.nativeChart P z width r banks src tab dst owners
    let A:=v.billedAccount P z width r banks src tab dst owners
    let a:=Attempt.outer u h
    let N:=Stages z (2^v.W)
    let w:=wordBits z (2^v.W) copies
    let g:=JointHeader.scores P.joint z N k
    let H:=v.publicHeader P z width
    let phase:=deadline v.mesh v.finish (v.basePhase width) a
    let sh:=v.frozenMarket P z width u h
    let fr:=v.frozenInput P z width r banks src tab dst owners mem u h
    let state:=outerScoreMemory C mem u h
    let b:=(v.nativeBoards P z width).outer u h
    let old:={b.old with base:=sh.shelf.stockBase}
    let bits:=PurchaseInventory.stock (h:=z) (stageCount:=N) (k:=k) sh.shelf.stockBase fr
    Calendar.mounted C (events C.mesh) mem → H.Resident mem →
    InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) stock mem →
    GlobalTests.rows z N k≤2^w → v.keepLimit*width<g.stride →
    (∀i,(A.trial C mem u h).bits i≤v.keepLimit*width) →
    QuoteCells phase state b.price (GlobalTests.offsets b.globalTests) old PurchaseInventory.slot PurchaseInventory.lane bits g.stride ∧
      H.payload.Resident state := by
  intro C A a N w g H phase sh fr state b old bits whole resident installed rows stride bounded
  let bills:=v.issued P z width r banks src tab dst owners
  let arena:=v.privateArena P z width
  let entry:=trialState C mem u h
  let B:=repair C a
  let page:=DeadlineROM.scorePage v.mesh g z N k a
  have ready:=outer_head_ready whole u.isLt h.isLt
  have first : H.stop≤arena.first:=(Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have order : H.Ordered:=by apply economic_ordered
  have keeps (e : Event) (x : ℕ) (hx : x<H.stop) : protected C x e :=
    (v.event_prefix P z width r banks src tab dst owners e x ((hx.trans_le first).trans_le (Nat.le_add_right ..))).1
  have live:=H.initialScore order C mem u h resident whole u.isLt h.isLt keeps
  have prior (x : ℕ) (lo : x<arena.base v.mesh (.attempt a)) : state x=entry x := by
    have safe:=(v.event_prefix P z width r banks src tab dst owners (.attempt a) x lo).1
    change B.tests.payload.after (B.tests.excess.after (prepared C a entry)) x=_
    rw [B.tests.payload.frame _ _ safe.2.2.2.1,B.tests.excess.frame _ _ safe.2.2.1,prepared_prior C a entry x ready safe]
  have scoreEnd : GlobalTests.stop page z N k≤H.ports.base := by
    change GlobalTests.stop (GlobalTests.page g z N k (DeadlineROM.index v.mesh a).val) z N k≤
      JointHeader.stop P.joint z N k (DeadlineROM.count v.mesh)
    rw [GlobalTests.page_stop]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (DeadlineROM.index v.mesh a).isLt) _
  have scores : GlobalTests.Resident page z N k ((DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (DeadlineROM.index v.mesh a)) state := by
    apply (installed.scores (DeadlineROM.index v.mesh a)).transport
    intro x _ high
    have hx:=((high.trans_le scoreEnd).trans_le (Nat.le_add_right ..)).trans_le (CatalystArchive.economic_ports_end H order)
    have fromEntry:=prior x ((hx.trans_le first).trans_le (Nat.le_add_right ..))
    have fromBoot:=run_frame C _ mem x (beforeTrial_mounted C mem u h whole u.isLt h.isLt.le) (fun e _=>keeps e x hx)
    rw [←trial_as_run] at fromBoot
    exact fromEntry.trans fromBoot
  let goods:=Commodity (Fin (2^z)) N k
  have addr (i : goods) : A.stockAt a i=sh.shelf.stockBase+PurchaseInventory.slot i :=
    v.stock_pointer P z width bills a i
  have upper (i : goods) : sh.shelf.stockBase+PurchaseInventory.slot i<arena.base v.mesh (.attempt a) :=
    (Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _).trans_le (v.activation_stock_floor P z width a)
  have floors:=v.activation_parent_floor P z width r banks src tab dst owners u h
  have readStock (i : goods) : bits i=(entry (A.stockAt a i)).val := by
    rw [addr]
    let cell:=sh.shelf.stockBase+PurchaseInventory.slot i
    have low:=Nat.add_lt_add_left (PurchaseInventory.slot_lt i) sh.shelf.stockBase
    change (sh.failures.pass.apply ((guard C a).apply entry) cell).val=_
    rw [sh.failures.frame _ _ (.inl (low.trans_le floors.2))]
    exact congrArg Fin.val (ProtocolRAMGeneratedWrite.frame_image (C.stopAt a) 1
      (stop C.mesh C.modeAt a) entry cell (.inl (low.trans_le floors.1)))
  have words:=v.row_quote_cells P z width bills a entry state u.isLt.le live.scalar scores rows
    (fun i=>by
      rw [v.stock_pointer P z width bills a i]
      exact prior _ (upper i)) (fun i=>(bounded i).trans_lt stride)
  refine ⟨?_,live.payload⟩
  constructor
  · intro i
    exact words.offset i
  · intro i
    rw [readStock i]
    exact words.stock i
  · intro i
    rw [readStock i]
    exact words.rom i

/-- All quote operands are read from the native outer score memory, using each original
payload row and the stock whose signed cells the parent shelf is about to mark. The two
chosen global calibrations retain their actual threshold projections. -/
theorem purchase_density_uniform :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank)
      (mem : Shelf.Mem z (2^v.W)) (π : Equiv.Perm (Fin (2^z)))
      (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel) (fixture : Shelf.Mem z (2^v.W)),
    let a:=Attempt.outer u h
    let sh:=v.frozenMarket P z width u h
    let C:=v.nativeChart P z width r banks src tab dst owners
    let state:=outerScoreMemory C mem u h
    let b:=(v.nativeBoards P z width).outer u h
    let old:={b.old with base:=sh.shelf.stockBase}
    let fr:=v.frozenInput P z width r banks src tab dst owners mem u h
    let s:=outerTime v.mesh v.finish u
    let phase:=deadline v.mesh v.finish (v.basePhase width) a
    let N:=Stages z (2^v.W)
    let t:=phase
    let x:=stageQuotes (z:=z) (d:=2^v.W) (k:=k) phase 0 1 sh.shelf.stockBase fr
    let B:=repair C a
    let raw:=prepared C a (trialState C mem u h)
    let bits:=PurchaseInventory.stock (stageCount:=N) (k:=k) (h:=z) sh.shelf.stockBase fr
    TestRoom B (wordBits z (2^v.W) copies) → observedMode C mem u h=3 →
    2^z<2^wordBits z (2^v.W) copies →
    QuoteCells t state b.price (GlobalTests.offsets b.globalTests) old PurchaseInventory.slot PurchaseInventory.lane bits
      (JointHeader.scores P.joint z N k).stride →
    (v.publicHeader P z width).payload.Resident state →
    (v.publicHeader P z width).payload.maxWord<2^wordBits z (2^v.W) copies →
    (∃ c,∃ X : SumCalibration B.tests.excess raw (score v.a v.radius (bonus (probeBonus v.W)) x) c,
      X.threshold=(2^z:ℕ)*(envelope v.W ((dyadicScale v.W)^8) s+3/8)) →
    (u.val<v.mesh.inject → ∃ c,∃ X : SumCalibration B.tests.payload (B.tests.excess.after raw) (∑i,x (.inl i)) c,
      X.threshold=(2^z:ℕ)*(1+3/8:ℝ)) →
    sh.shelf.Incoming (k:=k) v.sampler π v.depth phase (probeHeat v.W) 1 fr →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared v.sampler v.depth fixture i fr) →
    sh.shelf.flagsBase v.sampler z (2^v.W) k v.depth+count z (2^v.W) k*paths z v.sampler.degree v.depth<
      2^wordBits z (2^v.W) copies →
    (∀tile j,stockBits sh.shelf.stockBase k fr tile j<sh.shelf.table.size) →
    probeDensity k v.W*(2^z:ℕ)≤Fintype.card (LiveChains (k:=k) v.sampler π v.depth
      (actualMarks (k:=k) sh.shelf phase (probeHeat v.W) 1 fr)) := by
  filter_upwards [v.path_coverage] with z covered
  intro P width r banks src tab dst owners mem π u h fixture a sh C state b old fr s phase N t x B raw bits
    space buy room cells resident wordRoom excess payload incoming preparedRows flagRoom stockRoom
  let d:=2^v.W
  let T:=probeHeat v.W
  let n:=2^z
  have stageCount : N=publicStages v.W:=fixed_stage_count z v.W
  have countEq : 2*rounds d+1=publicStages v.W:=(template_length ..).symm.trans stageCount
  have priced : phase=publicPhase (2*rounds d+1) v.a v.radius v.W T s width v.precision := by rw [countEq]; rfl
  have hot : 0<(v.finish:ℝ):=by exact_mod_cast v.clock.finish_pos
  have hs : 0<s:=hot.trans_le (v.real_times u.isLt.le).1
  have s1 : s≤1 := by
    have cool : (v.finish:ℝ)≤1:=by exact_mod_cast v.clock.finish_le
    apply sub_le_self
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr cool)) (Nat.cast_nonneg _)
  have ha : 0<(v.a:ℝ):=by exact_mod_cast v.quadratic_pos
  have nn : 0<(n:ℝ):=by dsimp [n]; positivity
  let barrier:=envelope v.W ((dyadicScale v.W)^8) s
  have high : barrier < score v.a v.radius (bonus (probeBonus v.W)) x/n ∨ s=1 ∧ (n:ℝ)<∑i,x (.inl i) := by
    rcases observed_purchased C mem u h space buy with voted | ⟨inject,voted⟩
    · obtain ⟨_,X,threshold⟩:=excess
      have total:=X.high voted
      rw [threshold] at total
      left
      apply (lt_div_iff₀ nn).mpr
      change (n:ℝ)*(barrier+3/8)≤_ at total
      nlinarith
    · obtain ⟨_,X,threshold⟩:=payload inject
      have total:=X.high voted
      rw [threshold] at total
      refine Or.inr ⟨injection_time _ _ inject.le,?_⟩
      change (n:ℝ)*(1+3/8)≤_ at total
      linarith
  let stride:=(JointHeader.scores P.joint z N k).stride
  have board:=StripChart.payload_trigger_scores F v.mesh (v.privateArena P z width) P.joint.initial
    width v.keepLimit (v.nativeBoards P z width) v.finish (v.basePhase width) P.catalogue r banks src tab dst owners
    mem u h stride v.toleranceAt (pow_pos v.sampler_live _) room
  have words:=DiscrepancyROM.payload_read F N k v.mesh v.finish (v.basePhase width)
    (v.publicHeader P z width).payload.base v.digitRadix v.precision u h state u.isLt.le resident wordRoom
  have bonuses (i : Commodity (Fin n) N k) : 0≤phase.bonus (PurchaseInventory.lane i) := by
    rw [priced]; dsimp [publicPhase]; split <;> positivity
  have caps (i : Commodity (Fin n) N k) : 0≤phase.cap (PurchaseInventory.lane i) := by
    rw [priced]; dsimp [publicPhase]; split <;> positivity
  obtain ⟨_,bound,pick,measured⟩:=board bits rfl cells ha bonuses (Nat.cast_nonneg _) hs caps
    v.clock.precision_pos v.clock.precision_pos v.clock.precision_cutoff
    (fun i=>(v.scheduled_digit width u 0 h 0 _ (bits i) u.isLt.le).1)
    (fun key=>(words key).1) (fun key=>(words key).2)
  have post : (fun i : Commodity (Fin n) N k=>phase.quote (PurchaseInventory.lane i) (bits i))=x := by
    dsimp only [x]
    rw [priced]
    exact real_post_quote ..
  have boundQ : (v.a:ℝ)*(∑i,x i^2)/n≤(v.W:ℝ)⁻¹^4 := by
    apply (restage_property (z:=z) (d:=d) (k:=k) phase sh.shelf.stockBase fr
      (fun _ y=>(v.a:ℝ)*(∑i,y i^2)/n≤(v.W:ℝ)⁻¹^4)).2
    have scoreBound := v.small_score z d _ countEq T s hs width v.precision sh.shelf.stockBase fr
    simpa only [priced, countEq, n, Nat.cast_pow, Nat.cast_ofNat] using scoreBound
  have box : ∀i,PayloadStrip.rowQuotes x i∈Set.Icc 0 (PayloadStrip.ceiling N k v.radius) := by
    apply (restage_property (z:=z) (d:=d) (k:=k) phase sh.shelf.stockBase fr
      (fun l y=>∀i,PayloadStrip.rowQuotes y i∈Set.Icc 0 (PayloadStrip.ceiling l k v.radius))).2
    rw [priced]
    exact public_row_quotes ha (Nat.cast_nonneg _) hs width v.precision sh.shelf.stockBase fr
  have actualRadius : phase.M = (v.radius : ℝ) := congrArg PhasePrice.M priced
  have actualPrecision : ((v.nativeBoards P z width).outer u h).test.precision = v.precision := rfl
  have energy:=v.stage_trigger C mem u h stageCount space buy s hs s1 x boundQ box bound pick
    (fun i name => by
      have value := measured i name
      change PayloadStrip.namedError F N k name phase.M
        (PayloadStrip.rowQuotes (fun j : Commodity (Fin n) N k => phase.quote (PurchaseInventory.lane j) (bits j)) i) ≤
        ((outerCheck C u h).score (outerScoreMemory C mem u h) (pick i) : ℝ) /
          ((v.nativeBoards P z width).outer u h).test.precision + v.toleranceAt at value
      rwa [actualRadius, post, actualPrecision] at value) high
  have move:=(restage_property (z:=z) (d:=d) (k:=k) phase sh.shelf.stockBase fr
    (fun l y=>(Fintype.card (Fin n×Fin l):ℝ) ≤∑b,∑j : Fin k×Bool,s*(rise v.radius (y (.inr (b,j)))/T)^2)).1 energy
  rw [priced] at incoming move ⊢
  exact (covered π sh.shelf v.a s width v.precision fr fixture ha hs s1 incoming preparedRows flagRoom stockRoom move).2.2

theorem purchase_density (P : v.Placement) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank)
      (mem : Shelf.Mem z (2^v.W)) (π : Equiv.Perm (Fin (2^z)))
      (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel) (fixture : Shelf.Mem z (2^v.W)),
    let a:=Attempt.outer u h
    let sh:=v.frozenMarket P z width u h
    let C:=v.nativeChart P z width r banks src tab dst owners
    let state:=outerScoreMemory C mem u h
    let b:=(v.nativeBoards P z width).outer u h
    let old:={b.old with base:=sh.shelf.stockBase}
    let fr:=v.frozenInput P z width r banks src tab dst owners mem u h
    let s:=outerTime v.mesh v.finish u
    let phase:=deadline v.mesh v.finish (v.basePhase width) a
    let N:=Stages z (2^v.W)
    let t:=phase
    let x:=stageQuotes (z:=z) (d:=2^v.W) (k:=k) phase 0 1 sh.shelf.stockBase fr
    let B:=repair C a
    let raw:=prepared C a (trialState C mem u h)
    let bits:=PurchaseInventory.stock (stageCount:=N) (k:=k) (h:=z) sh.shelf.stockBase fr
    TestRoom B (wordBits z (2^v.W) copies) → observedMode C mem u h=3 →
    2^z<2^wordBits z (2^v.W) copies →
    QuoteCells t state b.price (GlobalTests.offsets b.globalTests) old PurchaseInventory.slot PurchaseInventory.lane bits
      (JointHeader.scores P.joint z N k).stride →
    (v.publicHeader P z width).payload.Resident state →
    (v.publicHeader P z width).payload.maxWord<2^wordBits z (2^v.W) copies →
    (∃ c,∃ X : SumCalibration B.tests.excess raw (score v.a v.radius (bonus (probeBonus v.W)) x) c,
      X.threshold=(2^z:ℕ)*(envelope v.W ((dyadicScale v.W)^8) s+3/8)) →
    (u.val<v.mesh.inject → ∃ c,∃ X : SumCalibration B.tests.payload (B.tests.excess.after raw) (∑i,x (.inl i)) c,
      X.threshold=(2^z:ℕ)*(1+3/8:ℝ)) →
    sh.shelf.Incoming (k:=k) v.sampler π v.depth phase (probeHeat v.W) 1 fr →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared v.sampler v.depth fixture i fr) →
    sh.shelf.flagsBase v.sampler z (2^v.W) k v.depth+count z (2^v.W) k*paths z v.sampler.degree v.depth<
      2^wordBits z (2^v.W) copies →
    (∀tile j,stockBits sh.shelf.stockBase k fr tile j<sh.shelf.table.size) →
    probeDensity k v.W*(2^z:ℕ)≤Fintype.card (LiveChains (k:=k) v.sampler π v.depth
      (actualMarks (k:=k) sh.shelf phase (probeHeat v.W) 1 fr)) :=
  v.purchase_density_uniform.mono (fun _ good=>good P)

/-- Starting with the original boot pages and capped stock run, an actual mode-three
ballot buys at least the public fraction of its original frozen sampler paths. -/
theorem dated_purchase_density_uniform :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (mem : Shelf.Mem z (2^v.W))
      (π : Equiv.Perm (Fin (2^z))) (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel),
    let a:=Attempt.outer u h
    let sh:=v.frozenMarket P z width u h
    let C:=v.nativeChart P z width r banks src tab dst owners
    let fr:=v.frozenInput P z width r banks src tab dst owners mem u h
    let phase:=deadline v.mesh v.finish (v.basePhase width) a
    let N:=Stages z (2^v.W)
    let w:=wordBits z (2^v.W) copies
    let _g:=JointHeader.scores P.joint z N k
    let H:=v.publicHeader P z width
    let G:=v.privateArena P z width
    let strata:=stratumHeader z (2^v.W) k v.sampler.degree v.depth ((v.nativeBoards P z width).stratumHeader u h)
    StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width) →
    H.Resident mem → InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (fun _=>0) mem →
    P.joint.precision=v.precision → P.joint.cap*P.joint.width=v.keepLimit*width →
    v.keepLimit*width+1≤2^z →
    Shelf.Geometry π mem → heapEnd z (2^v.W) copies≤G.first → strata.stop≤G.first → strata.Loaded mem →
    G.endAddress v.mesh<2^w → width≤2^z → observedMode C mem u h=3 →
    probeDensity k v.W*(2^z:ℕ)≤Fintype.card (LiveChains (k:=k) v.sampler π v.depth
      (actualMarks (k:=k) sh.shelf phase (probeHeat v.W) 1 fr)) := by
  filter_upwards [v.purchase_density_uniform,Filter.eventually_ge_atTop 2,Filter.eventually_ge_atTop v.globalHeight,v.discrepancy_word_room] with z densityAt large glarge discrepancy
  intro P width r banks src tab dst owners mem π u h a sh C fr phase N w H G strata stock «public» prices precision
    budget fitStride geometry heap keyRoom loaded space payload buy
  let _g:=JointHeader.scores P.joint z N k
  let bills:=v.issued P z width r banks src tab dst owners
  let A:=v.billedAccount P z width r banks src tab dst owners
  let entry:=trialState C mem u h
  let s:=outerTime v.mesh v.finish u
  let t:=probeHeat v.W
  let x:=stageQuotes (z:=z) (d:=2^v.W) (k:=k) phase 0 1 sh.shelf.stockBase fr
  obtain ⟨_,slot⟩:=outer_slot C mem u h u.isLt h.isLt stock.mounted_all
  have native:=v.stock_cap C rfl G (v.nativeFormats P z width) P.joint.initial (v.emptyReserve P z width).base
    width bills mem stock
  have bounded:=native.1 u u.isLt h h.isLt.le
  have strideLarge : v.keepLimit*width<_g.stride:=by
    change v.keepLimit*width<P.joint.cap*P.joint.width+1
    rw [budget]
    exact Nat.lt_succ_self _
  have digits:=(v.global_numeric P z width glarge precision).1
  have ready:=slot.currentReady
  have space_z : 2^z<2^w:=by
    simpa using GlobalTests.linear_room z (2^v.W) 1 (by omega)
  have four : 4≤2^w := (show 4≤2^z from (Nat.pow_le_pow_right (by decide : 0<2) large)).trans space_z.le
  have room:=v.score_room P z width r banks src tab dst owners a entry ready four
  have rows : GlobalTests.rows z N k<2^w := by
    rw [GlobalTests.rowCount,Nat.mul_comm]
    exact GlobalTests.linear_room z (2^v.W) _ digits
  obtain ⟨fixture,incoming,prepped,_⟩:=v.activation_parent P z width r banks src tab dst owners mem π u h
    u.isLt h.isLt stock.mounted_all geometry heap keyRoom loaded
  have fit:=v.activation_fit P z width r banks src tab dst owners mem u h u.isLt h.isLt payload stock
  have flags:=v.activation_flags_room P z width r banks src tab dst owners mem stock.mounted_all u h space u.isLt h.isLt
  obtain ⟨cells,resident⟩:=v.purchase_score_inputs P z width r banks src tab dst owners mem u h _ stock.mounted_all
    «public» prices rows.le strideLarge bounded
  have source:=v.global_source_of_run P z width r banks src tab dst owners mem stock «public» prices precision budget
    glarge fitStride u h u.isLt h.isLt
  have countStages : N=publicStages v.W:=fixed_stage_count z v.W
  have countWords : 2*rounds (2^v.W)+1=publicStages v.W:=(template_length ..).symm.trans countStages
  have phasePrice : phase=publicPhase (2*rounds (2^v.W)+1) v.a v.radius v.W t s width v.precision := by rw [countWords];rfl
  have oldPrice:=v.activation_frozen_quotes P z width r banks src tab dst owners mem u h 0 1 phase
  have ledger : maximizer A.a A.M s A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem u h))=x := by
    change _=stageQuotes phase 0 1 sh.shelf.stockBase fr
    rw [oldPrice]
    have post:=(real_post_quote (z:=z) (d:=2^v.W) (k:=k) v.a v.radius v.W t s width v.precision sh.shelf.stockBase entry)
    rw [←phasePrice] at post
    rw [←post]
    funext i
    change offer v.a (bonus (probeBonus v.W) i) v.radius s (((entry (A.stockAt a i)).val:ℝ)/width)
      (routeCap N v.radius (PurchaseInventory.lane i))=_
    have address : A.stockAt a i = sh.shelf.stockBase + PurchaseInventory.slot i :=
      v.stock_pointer P z width bills a i
    rw [address, phasePrice]
    rcases i with row|⟨⟨row,j⟩,axis⟩ <;>
      simp [PhasePrice.quote, publicPhase, bonus, probeBonus, routeCap, PurchaseInventory.lane,
        PurchaseInventory.stock, countStages, countWords, t]
  apply densityAt P width r banks src tab dst owners mem π u h fixture room buy space_z cells resident (discrepancy P width).1
    _ _ incoming prepped flags fit
  · let X:=v.cool_vote P z width r banks src tab dst owners mem u h precision source u.isLt.le
    have ht:=v.cool_vote_threshold P z width r banks src tab dst owners mem u h precision source u.isLt.le
    have result : ∃ c,∃ Z : SumCalibration _ _ (score A.a A.M A.coefficient
        (maximizer A.a A.M s A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem u h)))) c,
        Z.threshold=(2^z:ℕ)*(envelope v.W ((dyadicScale v.W)^8) s+3/8) := ⟨_,X,ht⟩
    rwa [ledger] at result
  · intro inject
    let Y:=v.payload_vote P z width r banks src tab dst owners mem u h precision source inject.le
    have ht:=v.payload_vote_threshold P z width r banks src tab dst owners mem u h precision source inject.le
    have equal : pairing (fun i=>(A.payload i:ℝ)) (maximizer A.a A.M 1 A.coefficient A.box
        (A.bank.units A.payloadWidth (A.trial C mem u h)))=∑i,x (.inl i) := by
      have time_one : s = 1 := injection_time v.mesh (v.finish : ℝ) inject.le
      have at_one := (congrArg (fun time : ℝ =>
        maximizer A.a A.M time A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem u h)))
        time_one.symm).trans ledger
      exact (congrArg (pairing (fun i => (A.payload i : ℝ))) at_one).trans (by
        change pairing (fun i => (payloadUnit i : ℝ)) x = _
        simp [pairing, Fintype.sum_sum_type, payloadUnit])
    have result : ∃ c,∃ Z : SumCalibration _ _ _ c,Z.threshold=(2^z:ℕ)*(1+3/8:ℝ):=⟨_,Y,ht⟩
    rwa [equal] at result

theorem dated_purchase_density (P : v.Placement) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (mem : Shelf.Mem z (2^v.W))
      (π : Equiv.Perm (Fin (2^z))) (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel),
    let a:=Attempt.outer u h
    let sh:=v.frozenMarket P z width u h
    let C:=v.nativeChart P z width r banks src tab dst owners
    let fr:=v.frozenInput P z width r banks src tab dst owners mem u h
    let phase:=deadline v.mesh v.finish (v.basePhase width) a
    let N:=Stages z (2^v.W)
    let w:=wordBits z (2^v.W) copies
    let _g:=JointHeader.scores P.joint z N k
    let H:=v.publicHeader P z width
    let G:=v.privateArena P z width
    let strata:=stratumHeader z (2^v.W) k v.sampler.degree v.depth ((v.nativeBoards P z width).stratumHeader u h)
    StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width) →
    H.Resident mem → InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (fun _=>0) mem →
    P.joint.precision=v.precision → P.joint.cap*P.joint.width=v.keepLimit*width →
    v.keepLimit*width+1≤2^z →
    Shelf.Geometry π mem → heapEnd z (2^v.W) copies≤G.first → strata.stop≤G.first → strata.Loaded mem →
    G.endAddress v.mesh<2^w → width≤2^z → observedMode C mem u h=3 →
    probeDensity k v.W*(2^z:ℕ)≤Fintype.card (LiveChains (k:=k) v.sampler π v.depth
      (actualMarks (k:=k) sh.shelf phase (probeHeat v.W) 1 fr)) :=
  v.dated_purchase_density_uniform.mono (fun _ good=>good P)

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
