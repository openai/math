import OAI.Hierarchy.ProtocolRAMCalendarMountedScores
import OAI.Hierarchy.ProtocolRAMCalendarStockAt

namespace OAI
/-! # Installing the phase-wide price tables in the launched physical chart -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage ProbeStage.Native PurchaseStage AdaptiveProbe AdaptiveProbe.OuterBank AttemptGate
open scoped Classical
noncomputable section
variable {z d k q goods N : ℕ}

/-- The two price sums share the actual incoming stock used by the frozen market
and the labeled sparse commit. Only the check outputs move in the native layout. -/
def Format.scored (p : Format z d k q goods) (N : ℕ) (l : GlobalTests.Layout) (baseline : ℝ) :
    Format z d k q goods :=
  let stock : Bank := ⟨p.market.shelf.stockBase,l.indexBits⟩
  {p with batch:={p.batch with tests:=GlobalTests.board l z N k p.batch.tests stock baseline}}

theorem Format.score_excess (p : Format z d k q goods) (l : GlobalTests.Layout) (baseline : ℝ) :
    let f := p.scored N l baseline
    f.board.tests.excess=GlobalTests.check l z N k false f.board.tests.excess.out
      (GlobalTests.bound l z baseline) ⟨p.market.shelf.stockBase,l.indexBits⟩ := rfl

theorem Format.score_payload (p : Format z d k q goods) (l : GlobalTests.Layout) (baseline : ℝ) :
    let f := p.scored N l baseline
    f.board.tests.payload=GlobalTests.check l z N k true f.board.tests.payload.out
      (GlobalTests.bound l z 1) ⟨p.market.shelf.stockBase,l.indexBits⟩ := rfl

/-- Score checks are assigned counts before public archive heights, and their
actual stock address is substituted after physical predecessor assignment. The
immutable input row layout and both emitted budgets are unchanged by this pass. -/
def scoredFormats (c : Mesh) (arena : Arena) (initial : ℕ) (raw : Attempt→Format z d k q goods)
    (N : ℕ) (page : Attempt→GlobalTests.Layout) (baseline : Attempt→ℝ) (x : Attempt) :
    Format z d k q goods :=
  let preliminary := fun a=>(raw a).scored N (page a) (baseline a)
  let root := previousStock c initial (publishedStock c arena preliminary) (.attempt x)
  ((raw x).withStock root).scored N (page x) (baseline x)

theorem scoredFormats_area (c : Mesh) (arena : Arena) (initial : ℕ) (raw : Attempt→Format z d k q goods)
    (N : ℕ) (page : Attempt→GlobalTests.Layout) (baseline : Attempt→ℝ) (x : Attempt) :
    (scoredFormats c arena initial raw N page baseline x).pricedArea=
      ((raw x).scored N (page x) (baseline x)).pricedArea := rfl

theorem scoredFormats_published (c : Mesh) (arena : Arena) (initial : ℕ) (raw : Attempt→Format z d k q goods)
    (N : ℕ) (page : Attempt→GlobalTests.Layout) (baseline : Attempt→ℝ) :
    publishedStock c arena (scoredFormats c arena initial raw N page baseline)=
      publishedStock c arena (fun a=>(raw a).scored N (page a) (baseline a)) := by
  funext e
  cases e with
  | attempt a => rfl
  | feed b => rfl

theorem scoredFormats_stock (c : Mesh) (arena : Arena) (initial : ℕ) (raw : Attempt→Format z d k q goods)
    (N : ℕ) (page : Attempt→GlobalTests.Layout) (baseline : Attempt→ℝ) (x : Attempt)
    (i : Commodity (Fin (2^z)) N k) :
    let f := scoredFormats c arena initial raw N page baseline
    stockAt c arena f initial x i=(f x).market.shelf.stockBase+PurchaseInventory.slot i := by
  dsimp only
  rw [stockAt,scoredFormats_published]
  rfl

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
