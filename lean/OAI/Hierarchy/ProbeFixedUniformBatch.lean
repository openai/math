import OAI.Hierarchy.ProbeStripRowWork
import OAI.Hierarchy.ProbeFixedUniformFailureExpr
import OAI.Hierarchy.ProbeFixedStripSizes

namespace OAI
/-! # A height-independent instruction bound for every actual padded calendar ballot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseStage PurchaseFrozen
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def ballotInputs := 10+v.stripHeight+v.quoteCount+v.quoteWork+v.coordinateWork+v.failureExprWork
def ballotWork := stripWork v.ballotInputs

variable (P : v.Placement) (z width : ℕ)
local notation "B" => v.nativeBoards P z width
local notation "N" => Stages z (2^v.W)
local notation "fm" => v.nativeFormats P z width

section
variable {K : Type*} [Field K] {height degree axes letters dep : ℕ}
local notation "nst" => CoreBoard.Stages height degree

private theorem outer_row_work
    (s : StripChart.Boards height degree axes letters dep) (phase trial stock limit : ℕ) :
    let ev := Attempt.outer phase trial
    let b := s.outer phase trial
    let ch := payloadChannels height nst axes
    let m := payloadMenu K nst axes s.positive s.radius s.radius_nonneg
      s.tolerance s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum
    let f := StripChart.build K s ev stock
    letters ≤ limit → Fintype.card m.index ≤ limit →
      Fintype.card (PayloadRole nst axes) ≤ limit →
      Fintype.card (PayloadStrip.Quotes nst axes) ≤ limit →
      b.maxWidth ≤ limit → b.report.work ≤ limit →
      (∀i, (ch.address i).work ≤ limit) →
      f.market.failures.test.work ≤ limit →
      (∀i, (quoted b.price (GlobalTests.offsets b.globalTests)
        {b.old with base := f.market.shelf.stockBase} ch.digit i).work ≤ limit) →
      RowWork f.board (stripWork limit) := by
  intro ev b ch m f arity codes ports digits maximum report coordinate failure quotes
  let placedMarket : Market height degree axes :=
    {b.market with sampler := s.sampler, depth := dep, shelf := {b.market.shelf with stockBase := stock}}
  exact placed_row_work ch m b placedMarket
    (max (Fintype.card (PayloadRole nst axes)) (Fintype.card (PurchasedRole dep axes)))
    (StripChart.start s ev) limit arity codes ports digits maximum report coordinate ⟨failure, quotes⟩

private theorem inner_row_work
    (s : StripChart.Boards height degree axes letters dep) (phase trial layer tick stock limit : ℕ) :
    let ev := Attempt.inner phase trial layer tick
    let b := s.inner phase trial layer tick
    let ch := purchasedChannels (z:=height) (d:=degree) (k:=axes)
      (s.outer phase trial).market.shelf s.sampler dep (s.stratumHeader phase trial)
    let m := purchasedMenu K dep axes s.positive s.radius s.radius_nonneg
      s.tolerance s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum
    let f := StripChart.build K s ev stock
    letters ≤ limit → Fintype.card m.index ≤ limit →
      Fintype.card (PurchasedRole dep axes) ≤ limit →
      Fintype.card (ChainStrip.Axes dep axes) ≤ limit →
      b.maxWidth ≤ limit → b.report.work ≤ limit →
      (∀i, (ch.address i).work ≤ limit) →
      f.market.failures.test.work ≤ limit →
      (∀i, (quoted b.price (GlobalTests.offsets b.globalTests)
        {b.old with base := f.market.shelf.stockBase} ch.digit i).work ≤ limit) →
      RowWork f.board (stripWork limit) := by
  intro ev b ch m f arity codes ports digits maximum report coordinate failure quotes
  let placedMarket : Market height degree axes :=
    {b.market with sampler := s.sampler, depth := dep, shelf := {b.market.shelf with stockBase := stock}}
  exact placed_row_work ch m b placedMarket
    (max (Fintype.card (PayloadRole nst axes)) (Fintype.card (PurchasedRole dep axes)))
    (StripChart.start s ev) limit arity codes ports digits maximum report coordinate ⟨failure, quotes⟩

end

set_option maxHeartbeats 1000000 in
theorem native_row_work (a : Attempt) : RowWork (fm a).board v.ballotWork := by
  let u:=v.ballotInputs
  let count:=publicStages v.W
  let sig:=(catalogue F (v.configured (v.seed P z width)) v.cost).alphabet
  have menu:=v.catalogue_words (v.seed P z width) width
  have arity : sig≤u := by
    change (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet ≤ _
    rw [menu.1]
    have room:=le_max_left (v.stripPorts count+v.menu.alphabet+(1+v.menuCodes count)+v.menu.maximum)
      v.purchaseCounterHeight
    dsimp only [u,ballotInputs,stripHeight,count] at *
    omega
  have scalar : v.stripPorts N≤u ∧ v.menuCodes N≤u ∧ v.menu.maximum≤u := by
    rw [show N=count from fixed_stage_count ..]
    have room:=le_max_left (v.stripPorts count+v.menu.alphabet+(1+v.menuCodes count)+v.menu.maximum)
      v.purchaseCounterHeight
    dsimp only [u,ballotInputs,stripHeight,count] at *
    omega
  have tiny : 1≤u := by dsimp only [u,ballotInputs]; omega
  have digits : v.quoteCount≤u := by dsimp only [u,ballotInputs]; omega
  have price : v.quoteWork≤u := by dsimp only [u,ballotInputs]; omega
  have axis : v.coordinateWork≤u := by dsimp only [u,ballotInputs]; omega
  have formula : (fm a).market.failures.test.work≤u := by
    apply (v.failure_expr_work P z width a).trans
    dsimp only [u,ballotInputs]
    omega
  let incoming := resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (StripChart.build F B)
  cases a with
  | outer p a =>
    let t:=Attempt.outer p a
    have ar : Fintype.card (PayloadStrip.Quotes N k)≤v.quoteCount := by
      rw [show N=publicStages v.W from fixed_stage_count ..]
      exact le_max_left ..
    change RowWork (StripChart.build F B (.outer p a) (incoming t)).board (stripWork u)
    exact outer_row_work (K:=F) B p a (incoming t) u arity
      ((le_max_left ..).trans scalar.2.1) ((le_max_left ..).trans scalar.1)
      (ar.trans digits) (menu.2.1.le.trans scalar.2.2) tiny
      (fun i => (v.payload_coordinate z i).trans axis) formula
      (fun i => (v.payload_test_quotes_work P z width p a i).trans price)
  | inner p a j b' =>
    let t:=Attempt.inner p a j b'
    change RowWork (StripChart.build F B (.inner p a j b') (incoming t)).board (stripWork u)
    exact inner_row_work (K:=F) B p a j b' (incoming t) u arity
      ((le_max_right ..).trans scalar.2.1) ((le_max_right ..).trans scalar.1)
      ((le_max_right ..).trans digits) (menu.2.1.le.trans scalar.2.2) tiny
      (fun i => (v.purchased_coordinate z _ _ _ i).trans axis) formula
      (fun i => (v.purchase_test_quotes_work P z width p a j b' i).trans price)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
