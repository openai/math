import OAI.Computability.BorderVNP.CubeRoutePinnedSchedule
import OAI.Computability.BorderVNP.CubeRouteCommonDemands
import OAI.Computability.BorderVNP.CubeRouteCommonOwners

/-! # Identifying native writer receipts across the physical teams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical Transmission Packing.Directory

variable {w R : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout}
variable {pp lp pp' lp' : ℕ → ℕ × ℕ} {owner owner' : ℕ → Fin (R+1)}
variable {decl : LengthDeclaration a.n a.header.d} {group group' : Fin a.header.d → Fin (R+1)}
variable {pins : Pins.Layout} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}
variable {H : WriterHistory a.n (Tally.selectorWidth a.n a.K a.h) pub mac r m es t mt}

/-- Receipts use only the genuine compacted delivery rows, the physical cells and the
greedy symbol owners. They transport to a common representative across all teams. -/
theorem ReturnedWriters.congr_tables (src : ReturnedWriters a D pp lp owner decl group pins H)
    (directory : D.directory pp lp = D.directory pp' lp')
    {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {width : I → ℕ}
    (placement : BankPlacement D pp' lp' I cell id width) (bounds : D.DestinationBounds)
    (same : ∀ c < a.cells, owner c = owner' c) (symbols : group = group') :
    ReturnedWriters a D pp' lp' owner' decl group' pins H := by
  subst group'
  have demand := DemandInput.congr_owner a R (src.emission.demand.congr_directory directory) placement bounds same
  have size := congrArg List.length directory
  refine ⟨⟨demand,src.emission.pinLayout,?_,?_,?_⟩,src.low,?_⟩
  · simpa only [← size] using src.emission.sharedFields
  · simpa only [← size] using src.emission.sharedFit
  · simpa only [← size] using src.emission.symbols
  · simpa only [← size] using src.written

/-- Every admitted local public schedule has a concrete return, with its own native entry
memories, precise choice of receiving cells and chronological clock. -/
theorem PublicSchedule.joint_forward {Team : Type*} {pp lp : Team → ℕ → ℕ × ℕ}
    {owner : Team → ℕ → Fin (R+1)} {group : Team → Fin a.header.d → Fin (R+1)} {pins : Team → Pins.Layout}
    {pub : Team → Arg → Word w} {mac : Team → TeamOpcode.Macros w 8} {reg : Team → Bank w} {mem : Team → Memory w}
    {ticks : Team → ℕ} {pass : Team → Prop}
    (schedule : ∀ u, PublicSchedule a D (pp u) (lp u) (owner u) decl (group u) (pins u) (pub u) (mac u)
      (reg u) (mem u) (ticks u) (pass u)) (allowed : ∀ u, pass u) :
    ∃ (log : Team → List (TeamRAM.Event w)) (regs : Team → Bank w) (final : Team → Memory w),
      ∃ H : ∀ u, WriterHistory a.n (Tally.selectorWidth a.n a.K a.h) (pub u) (mac u) (reg u) (mem u) (log u) (regs u) (final u),
      ∀ u, ReturnedWriters a D (pp u) (lp u) (owner u) decl (group u) (pins u) (H u) ∧ traceCost (log u) ≤ ticks u := by
  choose logs regs final histories result using fun u => (schedule u).1 (allowed u)
  exact ⟨logs,regs,final,histories,result⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
