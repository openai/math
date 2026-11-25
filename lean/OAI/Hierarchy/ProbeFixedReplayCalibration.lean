import OAI.Hierarchy.ProbeFixedActivationParent
import OAI.Hierarchy.ProbeFixedActivationQuotes
import OAI.Hierarchy.ProbeFixedFailurePopulation
import OAI.Hierarchy.ProbeStripChartTests
import OAI.Hierarchy.ProbeDiscrepancyBoot
import OAI.Hierarchy.ProbeInstalledReplayPayment

namespace OAI
/-! # Reading the first successful replay vote on the actual purchased strip and charged account -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open PurchaseStage PurchaseFrozen PurchaseCT StripDirectory StockCommit
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "market" => v.frozenMarket P z width
local notation "snap" => v.frozenInput P z width r banks src tab dst owners
local notation "surface[" u "," h "," j "," b "]" => (B).inner u h j b
local notation "header[" u "," h "]" => stratumHeader z (2^v.W) k v.sampler.degree v.depth ((B).stratumHeader u h)

/-- The same immutable vector table read at setup is read again at the later
replay deadline. The table address is the one emitted into the physical strip. -/
theorem replay_discrepancy (mem : Memory W) (resident : (H).Resident mem)
    (whole : Calendar.mounted C (events v.mesh) mem) (room : (H).bought.maxWord<2^W)
    (u h j b : ℕ) (hp : u<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel)
    (hj : j<v.mesh.reserveSteps) (hb : b<v.mesh.innerFuel) :
    let date:=Attempt.inner u h j b
    let test:=(surface[u,h,j,b]).test
    let later:=deadline v.mesh v.finish (v.basePhase width) date
    let state:=replayScoreMemory C mem u h j b
    ∀x,test.table.read state ((finFunctionFinEquiv x).val:Word W)=
      (discrepancyCode (depth:=v.depth) (k:=k) F later later.M test.precision test.radix x:Word W) ∧
      discrepancyCode (depth:=v.depth) (k:=k) F later later.M test.precision test.radix x<2^W := by
  intro date test later state
  have ord : (H).Ordered:=economic_ordered F (v.sized (v.seed P z width) width) v.cost v.mesh P.joint P.catalogue P.routes
    v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have first : (H).stop≤(G).first:=(Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have now:=(H).replayScore ord C mem u h j b resident whole hp hh hj hb
    (fun ev x small=>(v.event_prefix P z width r banks src tab dst owners ev x ((small.trans_le first).trans_le (Nat.le_add_right ..))).1)
  exact DiscrepancyROM.purchase_read F v.depth k v.mesh v.finish (v.basePhase width) (H).payload.stop
    v.digitRadix v.precision u h j b state hp.le hj.le now.bought room

/-- A successful replay of the actual archived chain family pays the full
outer purchase fee and calibrated bonus in measured divergence. -/
theorem purchase_activation_of_density (mem fixture : Memory W) (π : Equiv.Perm (Fin (2^z)))
    (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel)
    (j : Fin v.mesh.reserveSteps) (b : Fin v.mesh.innerFuel)
    (late : v.stripHeight≤z) (payload : width≤2^z)
    («public» : (H).Resident mem) (priceStock : ℕ→ℕ)
    (prices : InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) priceStock mem)
    (stock : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (stride : v.keepLimit*width<(JointHeader.scores P.joint z N k).stride)
    (boughtMax : (H).bought.maxWord<2^W) (keys : (header[u,h]).stop≤(G).first)
    (archive : ArchiveRoom C mem (v.mesh.inject+v.mesh.cool))
    (buy : observedMode C mem u h=3) (advance : observedInnerMode C mem u h j b=1) :
    let sh:=market u h
    let frozen:=snap mem u h
    let live:=Fintype.card (LiveChains v.sampler π v.depth
      (actualMarks (k:=k) sh.shelf sh.phase sh.temperature sh.kind frozen))
    let s:=outerTime v.mesh v.finish u
    sh.shelf.Incoming (k:=k) v.sampler π v.depth sh.phase sh.temperature sh.kind frozen →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared v.sampler v.depth fixture i frozen) →
    (header[u,h]).Loaded frozen → probeDensity k v.W*(2^z:ℕ)≤live →
    2*((purchaseCount C mem u h:ℝ)*(Λ*(dyadicScale v.W)^p)+(2^z:ℕ)*probeDensity k v.W*purchaseReward k v.W/4) ≤
      s*divergence (A).a (A).M (A).coefficient
        (maximizer (A).a (A).M s (A).coefficient (A).box ((A).bank.units (A).payloadWidth ((A).trial C mem u h)))
        (maximizer (A).a (A).M (OuterBank.replayTime s (C).mesh.reserveSteps j) (A).coefficient (A).box
          ((A).bank.units (A).payloadWidth ((A).inner C mem u h j b))) := by
  intro sh frozen live s incoming prepared loaded many
  have whole:=stock.mounted_all
  apply (v.activation_coordinates P z width r banks src tab dst owners mem fixture π u h j b
    u.isLt h.isLt j.isLt b.isLt archive whole buy incoming prepared).2
  let date:=Attempt.inner u h j b
  let raw:=surface[u,h,j,b]
  let tested:=replayScoreMemory C mem u h j b
  let stockBank:={raw.old with base:=(f date).market.shelf.stockBase}
  let t:=reserveTime v.mesh v.finish u j
  let global:=(Fintype.equivFin (ColumnSite (StageColumns z (2^v.W)) k)).toEmbedding
  have dims:=v.purchased_table_room z late
  have fit:=v.activation_fit P z width r banks src tab dst owners mem u h u.isLt h.isLt payload stock
  have saved:=v.activation_archive P z width r banks src tab dst owners mem fixture π u h j b
    u.isLt h.isLt j.isLt b.isLt whole keys incoming prepared loaded
  have quotes:=v.activation_quote_cells P z width r banks src tab dst owners mem u h j b
    u.isLt h.isLt j.isLt b.isLt «public» priceStock prices stock stride
  have words:=v.replay_discrepancy P z width r banks src tab dst owners mem «public» whole boughtMax u h j b
    u.isLt h.isLt j.isLt b.isLt
  have installed:=StripChart.bought_test F v.mesh G P.joint.initial B u h j b
  have stages : 2*rounds (2^v.W)+1=publicStages v.W:=by unfold publicStages rounds;omega
  have hot : 0<(v.finish:ℝ):=by exact_mod_cast v.clock.finish_pos
  have times:=v.real_times u.isLt.le
  have hs : 0<s:=hot.trans_le times.1
  have ht : 0<t:=(half_pos hot).trans_le (times.2 j)
  have s1 : s≤1 := by
    have cool : (v.finish:ℝ)≤1:=by exact_mod_cast v.clock.finish_le
    exact sub_le_self _ (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr cool)) (Nat.cast_nonneg _))
  have pp : 0<(v.a:ℝ):=by exact_mod_cast v.quadratic_pos
  have large : 4≤2^W:=Nat.le_trans (by decide : 4≤2^2)
    (Nat.pow_le_pow_right (by decide) (by unfold Native.wordBits;omega))
  have wide : 0<W:=by unfold Native.wordBits;omega
  have space:=v.score_room P z width r banks src tab dst owners date _ (inner_head_ready whole u.isLt h.isLt j.isLt b.isLt) large
  let feeds:=feedColumns («N»:=N) v.mesh G f P.joint.initial width v.keepLimit
  have payment:=Calendar.installed_replay_payment F v.geometry v.positive rfl v.mesh v.finish v.a pp width
    v.precision v.clock.precision_pos f feeds (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun a=>(StripChart.header F B a).fieldTerm) (StripChart.id F B P.catalogue) mem u h j b sh.shelf v.sampler π
    frozen ((B).stratumHeader u h) raw.test raw.price (GlobalTests.offsets raw.globalTests) stockBank
    (JointHeader.scores P.joint z N k).stride global (v.date_prefix_fit z).le dims.1 wide dims.2.2.2 fit
    v.clock.precision_pos hs s1 ht
  dsimp only at payment
  simp only [stages] at payment
  exact payment dims.2.1 dims.2.2.1 rfl v.clock.precision_cutoff installed saved quotes
    (fun i=>(v.scheduled_digit width u j h b _ _ u.isLt.le).2) words many space advance

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
