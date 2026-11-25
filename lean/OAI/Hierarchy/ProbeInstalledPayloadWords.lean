import OAI.Hierarchy.ProbePayloadWords
import OAI.Hierarchy.ProbePhysicalTrigger
import OAI.Hierarchy.ProtocolRAMCalendarPriced
import OAI.Hierarchy.ProtocolRAMCalendarStripChart

namespace OAI
/-! # The installed outer gate reads the scores of the original payload strips -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage StripDirectory
open scoped Classical Fin.CommRing

variable {z d k N q goods r edges : ℕ}
local notation "W" => wordBits z d copies
local notation "Q" => PayloadStrip.Quotes N k
local notation "U" => Commodity (Fin (2^z)) N k

/-- The time-stamped chart tests the same mounted failure field that the
dense strip evaluator reads, in the state after the excess and payload
checks. Its two cutoffs are respectively the printed floor and ceiling. -/
theorem installed_payload_scores (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)]
    (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (initial : Memory W) (phase trial : ℕ)
    (test : StripTest (Fintype.card Q)) (price offsets stocks : Bank) (stride : ℕ)
    (bits : U→ℕ) (cutoff : ℝ) (tol : test.tolerance=cutoff) (room : 2^z<2^W) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    let s := deadline c finish prices (.outer phase trial)
    let m := outerScoreMemory C initial phase trial
    let check := checkedPayload z N k test price offsets stocks
    let native := outerCheck C phase trial
    let post := fun i : U => s.quote (PurchaseInventory.lane i) (bits i)
    2^z ≤ (format (.outer phase trial)).market.failures.rows →
    (format (.outer phase trial)).market.failures.effective = check.failure.effective →
    (format (.outer phase trial)).market.failures.cut = check.failure.cut →
    (format (.outer phase trial)).market.failures.globalBound = check.failure.globalBound →
    QuoteCells s m price offsets stocks PurchaseInventory.slot PurchaseInventory.lane bits stride →
    0<s.a → (∀ i : U,0≤ s.bonus (PurchaseInventory.lane i)) → 0≤ s.M → 0<s.time →
    (∀ i : U,0≤ s.cap (PurchaseInventory.lane i)) → 0<s.precision → 0<test.precision →
    1/(s.precision:ℝ)+1/(test.precision:ℝ) ≤ cutoff →
    (∀ i : U,s.word (PurchaseInventory.lane i) (bits i)<test.radix) →
    (∀ v,test.table.read m ((finFunctionFinEquiv v).val:Word W) =
      (payloadDiscrepancyCode (N:=N) (k:=k) F s test.precision test.radix v:Word W)) →
    (∀ v,payloadDiscrepancyCode (N:=N) (k:=k) F s test.precision test.radix v<2^W) →
    (format (.outer phase trial)).market.failures.cut = ⌊2*cutoff*test.precision⌋₊ ∧
    native.bound = ⌈4*cutoff*(2^z:ℕ)*test.precision⌉₊ ∧
    ∃ pick : Fin (2^z) ↪ Fin native.rows, ∀ (p : Fin (2^z)) (name : PayloadStrip.Naming N k),
      PayloadStrip.namedError F N k name s.M (PayloadStrip.rowQuotes post p) ≤
        (native.score m (pick p):ℝ)/test.precision+cutoff := by
  intro C s m check native post roomRows effective low high cell pos bonus hM time cap qp sp resolution digit rom fit
  have count : native.rows = (format (.outer phase trial)).market.failures.rows := rfl
  have term : native.term = (format (.outer phase trial)).market.failures.effective := rfl
  have thresh : native.bound = (format (.outer phase trial)).market.failures.globalBound := rfl
  rw [effective] at term
  rw [high] at thresh
  have rows : 2^z≤native.rows := by rw [count]; exact roomRows
  let pick : Fin (2^z) ↪ Fin native.rows := Fin.castLEEmb rows
  have read (p : Fin (2^z)) : native.score m (pick p) = check.failure.value m p := by
    change (native.term.eval m (p.val:Word W)).val = _
    exact congrArg (fun e : Expr => (e.eval m (p.val:Word W)).val) term
  have scored := payload_scores F s m test price offsets stocks stride bits cell room pos bonus hM time cap
    qp sp digit rom fit
  refine ⟨?_,?_,pick,fun p name => ?_⟩
  · rw [low]
    change ⌊2*test.tolerance*test.precision⌋₊ = _
    rw [tol]
  · rw [thresh]
    change ⌈4*test.tolerance*(2^z:ℕ)*test.precision⌉₊ = _
    rw [tol]
  · rw [read]
    exact (scored p name).trans (add_le_add le_rfl resolution)

namespace StripChart

/-- The one-element input to the public sampler already forces a positive
row degree, so every power appearing in the padded board is positive. -/
theorem paths_positive (S : PurchaseSampler) {δ : ℝ} (mix : S.Mixes δ) (small : δ≤1)
    (depth : ℕ) : 0<S.degree^depth := by
  have enough : ⌈δ*(1:ℕ)⌉₊ ≤ (Finset.univ : Finset (Fin 1)).card := by
    rw [Finset.card_univ,Fintype.card_fin]
    apply Nat.ceil_le.mpr
    simpa using small
  obtain ⟨x,_,y,_,edge⟩ := mix 1 (by decide) Finset.univ Finset.univ enough enough
  exact pow_pos ((List.length_pos_of_mem edge).trans_le (S.out_degree 1 x)) _

/-- The padded original market uses the dense input guard and its two
thresholds at every real source row. Its additional DFS rows occur after
those sources and do not alter the population in the global threshold. -/
theorem payload_gate {depth : ℕ} (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (c : Mesh) (arena : Arena) (initial : ℕ) (boards : Boards z d k q depth)
    (phase trial : ℕ) (pathsPos : 0<boards.sampler.degree^depth) :
    let fmt := formats F c arena initial boards (.outer phase trial)
    let b := boards.outer phase trial
    let dense := checkedPayload z (permutationFabric z d).shapes.length k b.test b.price
      (GlobalTests.offsets b.globalTests) {b.old with base:=fmt.market.shelf.stockBase}
    2^z ≤ fmt.market.failures.rows ∧ fmt.market.failures.effective = dense.failure.effective ∧
      fmt.market.failures.cut = dense.failure.cut ∧ fmt.market.failures.globalBound = dense.failure.globalBound := by
  refine ⟨?_,rfl,rfl,rfl⟩
  change 2^z ≤ PurchaseFrozen.count z d k*PurchaseFrozen.paths z boards.sampler.degree depth
  rw [PurchaseFrozen.count_eq,PurchaseFrozen.paths]
  have keys : 0 < (2*rounds d+1)*(2*k) := Nat.mul_pos (by omega) (by have := boards.positive; omega)
  exact (Nat.le_mul_of_pos_right _ pathsPos).trans (Nat.le_mul_of_pos_left _ keys)

/-- On the instantiated strip chart all mounting and padding properties are
witnessed by the format constructor. Only the physical replay tables and
their numerical encoding are read from the current state. -/
theorem payload_trigger_scores {depth : ℕ} (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (c : Mesh) (arena : Arena) (initial width limit : ℕ) (boards : Boards z d k q depth)
    (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board) (r : ℕ)
    (banks : RouteSettlement.Banks) (source table destination : ℕ) (owners : Bank)
    (mem : Memory W) (phase trial stride : ℕ) (cutoff : ℝ) (pathsPos : 0<boards.sampler.degree^depth)
    (room : 2^z<2^W) :
    let N := (permutationFabric z d).shapes.length
    let fmt := formats F c arena initial boards (.outer phase trial)
    let b := boards.outer phase trial
    let stocks := {b.old with base:=fmt.market.shelf.stockBase}
    let C := chart F c arena initial width limit boards finish prices catalogue r banks source table destination owners
    let s := deadline c finish prices (.outer phase trial)
    let m := outerScoreMemory C mem phase trial
    let native := outerCheck C phase trial
    ∀ bits : Commodity (Fin (2^z)) N k → ℕ,
    let post := fun i => s.quote (PurchaseInventory.lane i) (bits i)
    b.test.tolerance=cutoff →
    QuoteCells s m b.price (GlobalTests.offsets b.globalTests) stocks PurchaseInventory.slot PurchaseInventory.lane bits stride →
    0<s.a → (∀ i,0≤ s.bonus (PurchaseInventory.lane (i : Commodity (Fin (2^z)) N k))) → 0≤ s.M → 0<s.time →
    (∀ i,0≤ s.cap (PurchaseInventory.lane (i : Commodity (Fin (2^z)) N k))) → 0<s.precision → 0<b.test.precision →
    1/(s.precision:ℝ)+1/(b.test.precision:ℝ) ≤ cutoff →
    (∀ i,s.word (PurchaseInventory.lane i) (bits i)<b.test.radix) →
    (∀ v,b.test.table.read m ((finFunctionFinEquiv v).val:Word W) =
      (payloadDiscrepancyCode (N:=N) (k:=k) F s b.test.precision b.test.radix v:Word W)) →
    (∀ v,payloadDiscrepancyCode (N:=N) (k:=k) F s b.test.precision b.test.radix v<2^W) →
    fmt.market.failures.cut = ⌊2*cutoff*b.test.precision⌋₊ ∧
    native.bound = ⌈4*cutoff*(2^z:ℕ)*b.test.precision⌉₊ ∧
    ∃ pick : Fin (2^z) ↪ Fin native.rows, ∀ (p : Fin (2^z)) (name : PayloadStrip.Naming N k),
      PayloadStrip.namedError F N k name s.M (PayloadStrip.rowQuotes post p) ≤
        (native.score m (pick p):ℝ)/b.test.precision+cutoff := by
  intro N fmt b stocks C s m native bits post tol
  obtain ⟨many,term,localCut,globalCut⟩ := payload_gate F c arena initial boards phase trial pathsPos
  let layouts := formats F c arena initial boards
  exact installed_payload_scores F c finish prices layouts (feedColumns (N:=N) c arena layouts initial width limit)
    (catalogue.sink r banks source table destination owners) catalogue.idBase
    (fun a => (header F boards a).fieldTerm) (id F boards catalogue) mem phase trial b.test b.price
    (GlobalTests.offsets b.globalTests) stocks stride bits cutoff tol room many term localCut globalCut

end StripChart

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
