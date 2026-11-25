import OAI.Hierarchy.ProbeFixedStripCounts

namespace OAI
/-! # Population of the outer payload's physical failure-live column -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "f" => v.nativeFormats P z width

/-- The full padded market is already bounded by the native group-by-path
table whose address width was established for the fixed strip menu. -/
theorem market_rows_fit (late : v.stripHeight≤z) (a : Attempt) : (f a).market.rows≤2^W := by
  have size : (f a).market.rows=PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth :=
    candidate_count F v.mesh (v.privateArena P z width) P.joint.initial (v.nativeBoards P z width) a
  rw [size]
  exact (v.purchased_table_room z late).2.2.1

/-- A positive live flag in the original outer ballot implies an unpadded row
ordinal. This is independent of all private memory words. -/
theorem payload_live_lt (phase trial : ℕ) (m : Memory W)
    (i : Fin (f (.outer phase trial)).market.rows) (rowFit : i.val<2^W)
    (entered : (f (.outer phase trial)).market.failures.live.eval m (i.val:Word W)≠0) :
    i.val<2^z := by
  change (Expr.branch .lt .row (.lit (2^z)) (.lit 1) (.lit 0)).eval m (i.val:Word W)≠0 at entered
  by_contra outside
  apply entered
  simp only [Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,Fin.lt_def,decide_eq_true_eq,
    Fin.val_cast_of_lt rowFit,Fin.val_cast_of_lt (v.date_prefix_fit z),ite_eq_right outside]; rfl

theorem payload_population_of_room (phase trial : ℕ) (m : Memory W)
    (room : (f (.outer phase trial)).market.rows≤2^W) :
    (Finset.univ.filter (fun i : Fin (f (.outer phase trial)).market.rows =>
      (f (.outer phase trial)).market.failures.live.eval m (i.val:Word W)≠0)).card≤2^z := by
  let market:=(f (.outer phase trial)).market
  let active:=Finset.univ.filter (fun i : Fin market.rows=>market.failures.live.eval m (i.val:Word W)≠0)
  let ordinal (i : ↥active) : Fin (2^z):=
    ⟨i.val.val,v.payload_live_lt P z width phase trial m i.val (i.val.isLt.trans_le room) (Finset.mem_filter.mp i.property).2⟩
  have inj : Function.Injective ordinal:=by
    intro i j same
    have ordVal := congrArg (fun l : Fin (2^z) => l.val) same
    exact Subtype.ext (Fin.ext ordVal)
  change active.card≤2^z
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective ordinal inj

theorem payload_population (phase trial : ℕ) (m : Memory W) (late : v.stripHeight≤z) :
    (Finset.univ.filter (fun i : Fin (f (.outer phase trial)).market.rows =>
      (f (.outer phase trial)).market.failures.live.eval m (i.val:Word W)≠0)).card≤2^z :=
  v.payload_population_of_room P z width phase trial m (v.market_rows_fit P z width late _)

/-- A mounted attempt supplies the same no-wrap condition directly from the
actual repair-mask scan. The word array whose population is queried may be any snapshot. -/
theorem payload_population_of_ready (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (phase trial : ℕ) (entry snapshot : Memory W)
    (ok : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (.outer phase trial)) entry) :
    (Finset.univ.filter (fun i : Fin (f (.outer phase trial)).market.rows =>
      (f (.outer phase trial)).market.failures.live.eval snapshot (i.val:Word W)≠0)).card≤2^z := by
  let C:=v.nativeChart P z width r banks src tab dst owners
  let a:=Attempt.outer phase trial
  have span : (repair C a).repairBits.base+(f a).market.rows<2^W:=ok.2.2.2.2.2.1
  exact v.payload_population_of_room P z width phase trial snapshot (by change (f a).market.rows≤2^W; omega)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
