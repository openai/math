import OAI.Computability.VPVNP.PairSimulationMapEntryTable
import OAI.Computability.VPVNP.PairSimulationMapEntry
import OAI.Computability.VPVNP.PairSimulationEntryWork

/-!
# Native execution of the grouped motif map

The concrete table runs on arbitrary incident bit strings in a prepared workspace.
A successful map increments the histogram at the emitted ordinals; a malformed
map reaches the actual reject instruction with the original counters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapEntryTable.Allocation

open MotifGrid MotifBlocks MotifSelector MotifDemandPadding MotifConversion MotifEntry
open BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k u w t : ℕ} (A : Allocation B z j r k)

/-- The complete fixed machine computes exactly the grouped-map entry, with one
private tick prefix on every path and the stated linear-in-copies budget. -/
theorem native (demand : D → ℕ) (v : E → ℕ) (d : DemandBits src dst demand j)
    (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t)
    (X : MapEntry.Program.Workspace (A.program A.locations) demand v d x t w)
    (c : Config w (Nat.card A.Address) r) (hc : (A.program A.locations).Ready X c) :
    let P := A.program A.locations
    let M := A.machine fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w))
    P.Runs M c X.hist (MapNativeClock.cap B z j u)
      ((MapStream.evaluate src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).map (List.map ord)) := by
  dsimp only
  rw [MapStream.evaluate_eq_run]
  exact (A.program A.locations).native X _ (A.template_linked _) (A.separate A.locations)
    sel ord fb fd fs (A.machine_public fb fd fs sel _) c hc

/-- The shrinking and refreshing node records supply exactly these concrete demand
and supply half-wire words. The machine returns the interpreter result at that call. -/
theorem native_entryInput (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (alloc : Allocation B (demandGrid B hp I.demand) I.party r k)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B (demandGrid B hp I.demand) e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) :
    let demand := demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ inputBits) I.supplyBits
    let P := alloc.program alloc.locations
    let M := alloc.machine fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w))
    ∀ (X : MapEntry.Program.Workspace P I.demand I.payload demand supply t w)
      (c : Config w (Nat.card alloc.Address) r), P.Ready X c →
      P.Runs M c X.hist (MapNativeClock.cap B (demandGrid B hp I.demand) I.party
        (repetitions B I.demand))
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  intro demand supply P M X c ready
  exact (alloc.program alloc.locations).native X _ (alloc.template_linked _)
    (alloc.separate alloc.locations) sel ord fb fd fs (alloc.machine_public fb fd fs sel _) c ready

end PairSimulation.MapEntryTable.Allocation

end VPVNP
end Computability
end OAI
