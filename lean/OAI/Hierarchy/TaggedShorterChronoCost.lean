import OAI.Hierarchy.TaggedShorterChronoArray
import OAI.Hierarchy.TaggedShorterPullCost

namespace OAI
/-! # Cell count of the chronological memory record array -/

noncomputable section
namespace Hierarchy.TaggedShorterChronoArray
open ThreeFlat Routing Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open TaggedShorterChronoRow
open scoped Classical BigOperators
variable {F : Type*} [Zero F] [One F] {S f u w r m : ℕ}

private theorem row_cells (hw : 3≤w+1) (j : Fin (2^m)) (o : Origin S f u w) :
    (row (F:=F) (r:=r) hw j o).cells≤20000*(w+1) := by
  cases o with
  | clock i t =>
    change (Tagged.RadixStage.pullPins (TaggedShorterChronoRow.network hw t) _).cells≤_
    rw [Tagged.RadixStage.pullPins_cells]
    exact (Nat.le_add_right ..).trans (TaggedShorterChronoRow.size (F:=F) (r:=r) hw t)
  | _ =>
    change (TypedWiring.glue _ _).cells≤_
    rw [TypedWiring.glue_cells]
    simp only [Tagged.RadixStage.pullPins_cells,TypedWiring.localTable,TableCompiler.localTableNetwork_cells,
      Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Out,Fintype.card_prod]
    change (7*(w+1))*16 ≤ 20000*(w+1)
    omega

theorem chrono_cells (hw : 3≤w+1) (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1))
    (addr : Fin u → Word (w+1)) :
    (network (F:=F) (r:=r) (m:=m) hw hs ht addr).cells≤2^m*(20000*(w+1)) := by
  rw [network,TypedWiring.glue_cells]
  simpa using Finset.sum_le_sum (s:=Finset.univ) fun j _=>row_cells (F:=F) (r:=r) hw j (origin hs ht addr j.val)

end Hierarchy.TaggedShorterChronoArray

end
end OAI
