import OAI.Computability.BorderVNP.DiagonalWiredReturnedReportRows
import OAI.Computability.BorderVNP.PackedSeedUseBankPrefix
import OAI.Computability.BorderVNP.CubePhysicalRetainedBottom

/-! # Reading retained report bundles before and after a native return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports Inherited
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open BorderVNP.Cube.Physical.NativeAssignments CellAddresses
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {N leaves : ℕ} (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    {copies : ℕ} (slot base : Fin N → ℕ)

attribute [local instance] reportDeckEq

variable {D' C ns : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (net : Network D' P bits) (cell : net.Site → Fin C) (siteID : net.Site ↪ Fin ns) (programs : Site.Programs net)
    (host : Fin leaves × (Fin q → Deck (depth+2)) ↪ net.Site)
    (width : ∀ z, (programs (host z)).birth.work=copies*(W.seedSlab position code sites edges ports z.2).stride)

local notation3 (prettyPrint := false) "size" => placedSize net programs
local notation3 (prettyPrint := false) "home" j => cell (host (origin j))
include width in
/-- Every selected operand lies inside the retained work slab in its true host's native
private bank. Appending the complete returned report preserves the whole source bundle. -/
theorem retainedBundle_host_bank_append (guessed : ∀ c, Fin (guessedSize net cell c) → Bool)
    (staged : ∀ c, Fin (siteSize net cell c (placedSize net programs)) → Bool)
    (supplied : ∀ c, Fin (suppliedSize net cell c) → Bool)
    (address : ∀ j, base j=siteBase net cell (home j) siteID size ⟨host (origin j),rfl⟩)
    (tail : Fin C → List Bool) (j : Fin N) :
    W.retainedBundle (copies:=copies) position origin code sites edges ports channels groups slot base
      (fun i => lookup ((CellAddresses.bank net cell (home i) (placedSize net programs)
        (guessed (home i)) (staged (home i)) (supplied (home i)))++tail (home i))) j =
    W.retainedBundle (copies:=copies) position origin code sites edges ports channels groups slot base
      (fun i => lookup (CellAddresses.bank net cell (home i) (placedSize net programs)
        (guessed (home i)) (staged (home i)) (supplied (home i)))) j := by
  apply W.seedUseBundle_append
  rw [address j]
  let x := host (origin j)
  have privateLength : copies*(W.seedSlab position code sites edges ports (origin j).2).stride ≤ size x := by
    rw [←width (origin j)]
    exact (programs x).retention.work_le.trans (Nat.le_add_right _ _)
  have room := siteBase_fits net cell (home j) siteID size ⟨x,rfl⟩
  let c₀ := cell x
  have bankLength : guessedSize net cell c₀+siteSize net cell c₀ size ≤
      (CellAddresses.bank net cell c₀ (placedSize net programs) (guessed c₀) (staged c₀) (supplied c₀)).length := by
    simp only [CellAddresses.bank,List.length_append,List.length_ofFn]
    omega
  exact (Nat.add_le_add_left privateLength _).trans (room.trans bankLength)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
