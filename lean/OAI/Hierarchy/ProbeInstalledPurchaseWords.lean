import OAI.Hierarchy.ProbeInstalledPayloadWords
import OAI.Hierarchy.ProbePurchaseArchiveReads
import OAI.Hierarchy.ProbePhysicalPayment
import OAI.Hierarchy.ProbeStripReplayWords

namespace OAI
/-! # Reading the installed replay score at the actual chronological inner gate -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen StripDirectory
open scoped Classical Fin.CommRing
variable {z d k J depth q goods r edges : ℕ}
local notation "W" => Native.wordBits z d Native.copies
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "U" => Commodity (Fin (2^z)) N k

/-- A replay checks the original bought row in the score RAM *after* the two
preceding threshold scans. Both price rounding and discrepancy rounding are
charged once per actual selected chain. -/
theorem priced_replay_words (F : Type*) [Field F] [SiteNaming (ChainStrip.Site depth k)]
    (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (initial : Memory W)
    (phase trial slice bid : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (start : ℕ) (hk : 0< k) (outer : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d)
    (test : StripTest (Fintype.card (ChainStrip.Axes depth k))) (price offsets stocks : Bank) (stride : ℕ)
    (bits : U→ℕ) (cutoff : ℝ) (tol : test.tolerance=cutoff) (global : ColumnSite (StageColumns z d) k ↪Fin J)
    (keys : count z d k≤2^W) (room : (depth+1)*paths z S.degree depth≤2^W)
    (whole : count z d k*paths z S.degree depth≤2^W) (wide : 0< W)
    (stock : PurchaseInventory.footprint z N k≤2^W) :
    let C:=pricedInstalled c finish prices format feeds sink idBase role ids
    let u:=Attempt.inner phase trial slice bid
    let s:=deadline c finish prices u
    let m:=replayScoreMemory C initial phase trial slice bid
    let checked:=checkedPurchase (z:=z) (d:=d) sh S start test price offsets stocks
    let native:=replayCheck C phase trial slice bid
    let marked:=actualMarks sh outer T kind frozen (k:=k)
    let post:=fun i : U=>s.quote (PurchaseInventory.lane i) (bits i)
    (format u).market.failures=checked.failure →
    ArchiveReads sh S π depth start outer T kind frozen m k →
    QuoteCells s m price offsets stocks PurchaseInventory.slot PurchaseInventory.lane bits stride →
    0< s.a → (∀i : U,0≤ s.bonus (PurchaseInventory.lane i)) → 0≤ s.M → 0< s.time →
    (∀i : U,0≤ s.cap (PurchaseInventory.lane i)) → 0< s.precision → 0< test.precision →
    1/(s.precision:ℝ)+1/(test.precision:ℝ)≤ cutoff →
    (∀i : U,s.word (PurchaseInventory.lane i) (bits i)< test.radix) →
    (∀v,test.table.read m ((finFunctionFinEquiv v).val:Word W)=
      (discrepancyCode (depth:=depth) (k:=k) F s s.M test.precision test.radix v:Word W)) →
    (∀v,discrepancyCode (depth:=depth) (k:=k) F s s.M test.precision test.radix v<2^W) →
    (format u).market.failures.cut=⌊2*cutoff*test.precision⌋₊ ∧
    native.bound=⌈4*cutoff*(2^z:ℕ)*test.precision⌉₊ ∧
    ∃pick : LiveChains S π depth marked ↪Fin native.rows,∀path,
      ChainStrip.namedError F depth k (namedStrip S π depth marked global path).name s.M
        (postQuote S π depth marked path post)≤(native.score m (pick path):ℝ)/test.precision+cutoff := by
  intro C u s m checked native marked post mounted archive cells pos bonus hm time cap qp sp resolution digit rom fit
  have size : native.rows=(format u).market.failures.rows := rfl
  have term : native.term=(format u).market.failures.effective := rfl
  have bound : native.bound=(format u).market.failures.globalBound := rfl
  rw [mounted] at size term bound
  let lift : Fin checked.rows↪Fin native.rows := (finCongr size.symm).toEmbedding
  have read (i : Fin checked.rows) : native.score m (lift i)=checked.failure.value m i := by
    change (native.term.eval m (i.val:Word W)).val=_
    rw [term]
    rfl
  obtain ⟨pick,scored⟩ := bought_scores F sh S π start hk outer s T kind frozen m test price offsets stocks stride bits
    cells archive.tiles archive.flags archive.header keys room whole wide stock global pos bonus hm time cap qp sp digit rom fit
  refine ⟨?_,?_,pick.trans lift,fun path=>?_⟩
  · rw [mounted]
    change ⌊2*test.tolerance*test.precision⌋₊=_
    rw [tol]
  · rw [bound]
    change ⌈4*test.tolerance*(2^z:ℕ)*test.precision⌉₊=_
    rw [tol]
  · change _≤(native.score m (lift (pick path)):ℝ)/test.precision+cutoff
    rw [read]
    linarith only [scored path,resolution]

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
