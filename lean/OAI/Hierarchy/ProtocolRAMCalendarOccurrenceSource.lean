import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceFormat
import OAI.Hierarchy.ProtocolRAMCalendarBuyMask

namespace OAI
/-! # Bind the mutable occurrence gate after the real repair-mask addresses have been placed -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage ProbeStage.Native PurchaseStage RepairHistogram StockCommit
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k q goods w r edges : ℕ}

/-- A physical mode-3 purchase has zero native occurrence deltas for the actual
priced board. Only the original immutable port directory must be loaded. -/
theorem occurrence_buy_idle (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (header : Attempt→ℕ) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (m : Memory (wordBits z d copies)) (p a : ℕ) :
    let x := Attempt.outer p a
    let f := F x
    let formats := fun y=>(F y).withOccurrenceHeader (header y)
    let C := pricedInstalled c finish prices formats feeds sink idBase role ids
    let L := C.layout x
    let B := repair C x
    let v := prepared C x (trialState C m p a)
    let out := postOutput L B v
    let g := f.labelSource sink idBase (role x) (ids x)
    let src := (formats x).stockSource
    let width := wordBits z d copies
    ready C (.attempt x) (trialState C m p a) → observedMode C m p a=3 →
    4≤2^width → f.market.rows≤2^f.indexBits →
    f.occurrences=(f.occurrenceHeader (header x)).count →
    (f.occurrenceHeader (header x)).Loaded out → (f.occurrenceHeader (header x)).stop≤g.out →
    goods≤2^width → q≤2^width → f.histMass<2^width → q*f.histMass<2^width →
    ∀ e : Fin f.occurrences, delta (f.pricedArea.columns src)
      ((f.pricedArea.seed src).apply ((g.pass f.occurrences).apply out)) e=0 := by
  intro x f formats C L B v out g src width run buy wide padded count loaded mounted dFit qFit copyFit sumFit
  have space := priced_mask_space c finish prices formats feeds sink idBase role ids x padded
  have order : g.out≤f.pricedArea.start := Nat.le_add_right ..
  have lo : B.repairBits.base+L.candidates≤g.out := by
    change f.maskStart+f.market.rows≤PostLayout.column f.maskStart f.indexBits _ _ + 1
    unfold PostLayout.column PostLayout.startColumns
    omega
  have rowRoom : L.candidates≤2^width := by
    have head : B.repairBits.base+L.candidates < 2^width := run.2.2.2.2.2.1
    exact (Nat.le_add_left L.candidates B.repairBits.base).trans head.le
  have mode : AttemptGate.actual B.policy (postSnapshot L B v)≠2 := by
    change observedMode C m p a≠2
    omega
  have old := f.occurrenceLoaded (header x) g out loaded mounted order
  exact buy_idle L B space v f.pricedArea src g wide rowRoom padded run.2.2.2.2.2.2.1 mode lo order
    (f.occurrencePlan (header x) _ count old dFit qFit copyFit sumFit)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
