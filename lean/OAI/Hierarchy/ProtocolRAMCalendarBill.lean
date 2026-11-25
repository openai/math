import OAI.Hierarchy.ProtocolRAMCalendarHardware

namespace OAI
/-! # Linear-time accounting for the concrete strata, histograms and settlement -/

namespace Hierarchy.ProtocolRAM.Calendar
open PurchaseStage ProbeStage ProbeStage.Native
open scoped BigOperators

variable {q d z k stageWidth : ℕ}

def marketFactor (m : Market z stageWidth k) (r : ℕ) :=
  passFactor r m.failures.pass+PurchaseFrozen.Shelf.timeFactor stageWidth m.sampler.degree m.depth k

theorem market_bill (m : Market z stageWidth k) (r : ℕ) (geom : 1≤ stageWidth)
    (rows : m.failures.rows≤2^z * r) :
    m.prefix.ticks≤2^z * marketFactor m r := by
  change m.failures.pass.clock+m.shelf.clock m.sampler z stageWidth k m.depth≤_
  rw [marketFactor,Nat.mul_add]
  exact Nat.add_le_add (pass_bill (Nat.two_pow_pos _) _ rows)
    ((m.shelf.clock_linear m.sampler z stageWidth k m.depth geom).trans_eq (Nat.mul_comm _ _))

def stockFactor (s : StockCommit) (rows r : ℕ) (b : Batch q d) :=
  4+((s.charges b rows).map (passFactor r)).sum+
    (35+r*(4*(RepairHistogram.pair s.columns).work+20)+r*(8*s.plan.mode.work+242))

theorem stock_bill (s : StockCommit) (w rows n r : ℕ) (b : Batch q d) (positive : 0<n)
    (occ : s.occurrences≤n*r) (goods : s.goods≤n*r)
    (charges : ∀ p∈s.charges b rows,p.rows≤n*r) :
    (s.native w rows b).ticks≤n*stockFactor s rows r b := by
  have first := columns_bill positive (s.charges b rows) charges
  have sites := Nat.mul_le_mul_right (4*(RepairHistogram.pair s.columns).work+20) occ
  have coords := Nat.mul_le_mul_right (8*s.plan.mode.work+242) goods
  have overhead : 35≤n*35 := by nlinarith
  change clock _ + RepairHistogram.commitTicks s.occurrences s.goods s.columns s.plan≤_
  rw [RepairHistogram.commitTicks_eq]
  unfold stockFactor
  simp only [Nat.mul_add,Nat.mul_assoc] at *
  omega

/-- The supplied quantities are physical row cardinalities and the bounded texts
of compiled opcodes. They contain neither a time trajectory nor a native-step estimate. -/
structure Extents (v : Market z stageWidth k) (s : StockCommit) (B : Repair q d) (r : ℕ) : Prop where
  strata : 1≤ stageWidth
  failureRows : v.failures.rows≤2^z*r
  candidates : v.layout.candidates≤2^z*r
  excessRows : B.tests.excess.rows≤2^z*r
  payloadRows : B.tests.payload.rows≤2^z*r
  discrepancyRows : B.tests.discrepancy.rows≤2^z*r
  reported : ∀p∈writes v.layout B,p.rows≤2^z*r
  occurrences : s.occurrences≤2^z*r
  commodities : s.goods≤2^z*r
  archives : ∀p∈s.charges (enabledBatch v.layout B) v.rows,p.rows≤2^z*r

def attemptFactor (v : Market z stageWidth k) (s : StockCommit) (B : Repair q d) (r : ℕ) (g : Pass) :=
  passFactor r g+marketFactor v r+postFactor B v.layout r+
    stockFactor s v.rows r (enabledBatch v.layout B)

theorem attempt_bill (v : Market z stageWidth k) (s : StockCommit) (B : Repair q d) (r : ℕ)
    (g : Pass) (inputs : Extents v s B r) (guardRows : g.rows≤2^z*r) :
    g.clock+(v.prefix.ticks+(postTicks v.layout B+(s.native (wordBits z stageWidth copies) v.rows
        (enabledBatch v.layout B)).ticks))≤2^z * attemptFactor v s B r g := by
  have guard := pass_bill (Nat.two_pow_pos z) g guardRows
  have frozen := market_bill v r inputs.strata inputs.failureRows
  have repair := post_bill B v.layout (2^z) r (Nat.two_pow_pos _) inputs.candidates inputs.excessRows
    inputs.payloadRows inputs.discrepancyRows inputs.reported
  have stock := stock_bill s (wordBits z stageWidth copies) v.rows (2^z) r _
    (Nat.two_pow_pos _) inputs.occurrences inputs.commodities inputs.archives
  simp only [attemptFactor,Nat.mul_add]
  omega

/-- The final directed route reporter uses a single pass over routed occurrences, then
one constant-size packet per edge. Including accepted and rejected terms gives the same bill. -/
theorem sink_bill {r edges : ℕ} (s : Sink r edges) (n u : ℕ) (positive : 0<n)
    (paths : r≤n*u) (links : edges≤n*u) :
    s.clock≤n*(42+276*u+passFactor (8*u)
      (report s.table edges s.owners (RouteSettlement.fields s.banks s.geometry))+117*u) := by
  have packedRows : 8*edges≤n*(8*u) := by
    calc
      _ ≤ 8*(n*u) := Nat.mul_le_mul_left _ links
      _ = _ := by ring
  have reportBound := pass_bill positive (report s.table edges s.owners (RouteSettlement.fields s.banks s.geometry)) packedRows
  have po := Nat.mul_le_mul_left 276 paths
  have ed := Nat.mul_le_mul_left 117 links
  have base : 38≤n*42 := by nlinarith
  rw [show 276*(n*u)=n*(276*u) by ring] at po
  rw [show 117*(n*u)=n*(117*u) by ring] at ed
  simp only [Sink.clock,RouteSettlement.ticks_eq,ProtocolRAM.clock,Nat.mul_add]
  omega

end Hierarchy.ProtocolRAM.Calendar

end OAI
