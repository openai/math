import OAI.Hierarchy.ProbeStripScore
import OAI.Hierarchy.ProbeStripThreshold

namespace OAI
/-! # Measured discrepancy on all retained strips of the actual purchased board -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen AttemptGate
open scoped Classical Fin.CommRing

variable {z d k J depth : ℕ}
local notation "W" => Native.wordBits z d Native.copies
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "U" => Commodity (Fin (2^z)) N k
local notation "I" => ChainStrip.Axes depth k

def checkedPurchase (sh : Shelf) (S : PurchaseSampler) (start : ℕ) (test : StripTest (Fintype.card I))
    (price offsets stocks : Bank) : StripTest (Fintype.card I) :=
  let header := stratumHeader z d k S.degree depth start
  let c := purchasedChannels (z:=z) (d:=d) sh S depth start (k:=k)
  tested {test with live:=c.live,rows:=header.count,population:=2^z} price offsets stocks c.digit

def phaseGrid (s : PhasePrice) (M : ℝ) (radix : ℕ) (v : Fin (Fintype.card I)→Fin radix) :=
  ChainStrip.prices depth k M (gridAxes radix s.precision v)

def discrepancyCode (F : Type*) [Field F] [SiteNaming (ChainStrip.Site depth k)]
    (s : PhasePrice) (M : ℝ) (Q radix : ℕ) (v : Fin (Fintype.card I)→Fin radix) :=
  discrepancyWord F (ChainStrip.wires depth k) (ChainStrip.demands depth k) (phaseGrid s M radix) Q v

/-- The three RAM reads at each genuine signed commodity determine the
rounded price. Each retained chain occupies its own affirmative row in
the tested board and inherits the true ordering of its named physical sites. -/
theorem bought_scores (F : Type*) [Field F] [SiteNaming (ChainStrip.Site depth k)]
    (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (start : ℕ) (hk : 0<k) (outer s : PhasePrice) (T : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z d)
    (test : StripTest (Fintype.card I)) (price offsets stocks : Bank) (stride : ℕ) (bits : U→ℕ)
    (cell : QuoteCells s m price offsets stocks PurchaseInventory.slot PurchaseInventory.lane bits stride)
    (tiles : ∀ key : Key z d k, ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth key).source (Shelf.pathRows S π depth key) m)
    (flags : StoredFlags sh S π depth outer T kind frozen m k)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k≤2^W) (room : (depth+1)*paths z S.degree depth≤2^W)
    (whole : count z d k*paths z S.degree depth≤2^W) (wide : 0<W)
    (stock : PurchaseInventory.footprint z N k ≤ 2^W)
    (global : ColumnSite (StageColumns z d) k ↪ Fin J)
    (pos : 0<s.a) (bonus : ∀ i : U,0≤ s.bonus (PurchaseInventory.lane i)) (M : 0≤ s.M)
    (time : 0<s.time) (cap : ∀ i : U,0≤ s.cap (PurchaseInventory.lane i)) (qp : 0<s.precision)
    (sp : 0<test.precision) (digit : ∀ i : U,s.word (PurchaseInventory.lane i) (bits i)<test.radix)
    (rom : ∀ v,test.table.read m ((finFunctionFinEquiv v).val:Word W)=
      (discrepancyCode (depth:=depth) (k:=k) F s s.M test.precision test.radix v:Word W))
    (fit : ∀ v,discrepancyCode (depth:=depth) (k:=k) F s s.M test.precision test.radix v<2^W) :
    let check := checkedPurchase (z:=z) (d:=d) sh S start test price offsets stocks
    let marked := actualMarks sh outer T kind frozen (k:=k)
    let post := fun i : U=>s.quote (PurchaseInventory.lane i) (bits i)
    ∃ pick : LiveChains S π depth marked ↪ Fin check.rows, ∀ path,
      ChainStrip.namedError F depth k (namedStrip S π depth marked global path).name s.M
        (postQuote S π depth marked path post) ≤ (check.failure.value m (pick path):ℝ)/test.precision+
          (1/s.precision+1/test.precision) := by
  intro check marked post
  obtain ⟨pick,physical⟩ := liveEmbedding sh S π depth start hk outer T kind frozen m tiles flags loaded keys room whole wide stock
  refine ⟨pick,fun p=>?_⟩
  let name := (namedStrip S π depth marked global p).name
  let slot := fun i : I=>stripAddress S π depth marked p i
  let code (i : I) : Fin test.radix := ⟨s.word (PurchaseInventory.lane (slot i)) (bits (slot i)),digit _⟩
  let v (j : Fin (Fintype.card I)) := code ((Fintype.equivFin I).symm j)
  let y := gridAxes test.radix s.precision v
  have real (j : Fin (Fintype.card I)) :
      (check.quoted j).eval m ((pick p).val:Word W)=((v j).val:Word W) :=
    cell.read _ j _ (slot ((Fintype.equivFin I).symm j)) ((physical p).2 _)
  have observed : check.failure.value m (pick p) =
      ⌊(test.precision:ℝ)*ChainStrip.namedError F depth k name s.M y⌋₊ :=
    named_score check s.M s.precision name m (pick p) v (physical p).1 real (rom v) (fit v)
  apply measured_named check s.M name m (pick p) (postQuote S π depth marked p post) y (by positivity) _ sp observed
  intro i
  have approx := s.approx (PurchaseInventory.lane (slot i)) (bits (slot i)) pos (bonus _) M time (cap _) qp
  change |post (slot i)-((v (Fintype.equivFin I i)).val:ℝ)/s.precision|≤1/s.precision
  dsimp only [v,code,post]
  rw [Equiv.symm_apply_apply,abs_of_nonneg (sub_nonneg.mpr approx.1)]
  exact approx.2.le

/-- The installed gate sums exactly the resident effective test field.
This identity applies at the actual chronological replay memory. -/
theorem tested_score {q goods digits : ℕ} (s : StripTest digits) (b : PurchaseStage.Repair q goods)
    (m : Memory W) (i : Fin s.rows) :
    (Calendar.testedBoard s.failure b).tests.discrepancy.score m i=s.failure.value m i := rfl

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
