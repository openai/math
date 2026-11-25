import OAI.Hierarchy.TaggedShorterPullCost
import OAI.Hierarchy.TaggedShorterClock
import OAI.Hierarchy.TaggedShorterCPUCost
import OAI.ThreeFlat.Diagonal.TraceRowCostLemmas

namespace OAI
/-! # Gate count of the physical clock array -/

noncomputable section
namespace Hierarchy.TaggedShorterClock
open ThreeFlat Routing Diagonal TraceRows TracePair TraceBanks TraceWords TraceIssue
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TaggedShorterCheapCPU
open scoped Classical BigOperators

variable {F : Type*} [CommRing F] {w p r k f : ℕ}

def initialPrice (w r : ℕ) := 4*((r+4)*((w+1)*10+2)+6)+1
def unitPrice (w p r : ℕ) :=
  initialPrice w r + (TraceUniformRow.canonicalCost w p r+1) + TaggedShorterCPURow.price w p r

private theorem test_cells {σ : Type} [Fintype σ] (v : TraceCompose.Packet σ)
    (f : σ → Pin w r f ⊕ Bool) :
    (Tagged.RadixStage.pullPins (TraceCircuit.localNetwork (fun _ : Fin 1 => v)
      (Fintype.equivFin _) (fun _ b => if b then (1:F) else 0)) f).cells = v.1+1 := by
  simp [TraceCircuit.localNetwork_cells]

theorem clock_cells (M : Machine w p r k) (ok : ∀ i,Cheap (M.code i))
    (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w) :
    (network (F:=F) (f:=f) M hw hp st).cells≤(f+1)*unitPrice w p r := by
  let P := pieces (F:=F) (f:=f) M hw hp st
  have ini : (P none).cells ≤ initialPrice w r := by
    change (Tagged.RadixStage.pullPins (TraceCircuit.localNetwork _ _ _) _).cells ≤ _
    rw [test_cells]
    apply Nat.add_le_add_right
    exact (formulaPacket_size_le _).trans (Nat.mul_le_mul_left 4
      (initialCheck_size hp M.entry _ _ (fun _=>le_rfl) (fun _=>le_rfl)))
  have step (i : Fin f) : (P (some (i,false))).cells+(P (some (i,true))).cells ≤
        (TraceUniformRow.canonicalCost w p r+1)+TaggedShorterCPURow.price w p r := by
    apply Nat.add_le_add
    · change (Tagged.RadixStage.pullPins (TraceCircuit.localNetwork _ _ _) _).cells ≤ _
      rw [test_cells]
      exact Nat.add_le_add_right (TraceUniformRow.canonical_bound hw hp) 1
    · change (Tagged.RadixStage.pullPins (TaggedShorterCPURow.network M) _).cells≤_
      simpa using (TaggedShorterCPURow.cells (F:=F) M ok)
  have all := Finset.sum_le_sum (s:=Finset.univ) fun i _=>step i
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at all
  rw [network,TypedWiring.glue_cells,Fintype.sum_option,Fintype.sum_prod_type]
  change (P none).cells + ∑ i, ∑ b : Bool, (P (some (i,b))).cells ≤ _
  simp_rw [Fintype.sum_bool]
  rw [Finset.sum_congr rfl (fun i _ => Nat.add_comm (P (some (i,true))).cells (P (some (i,false))).cells)]
  apply (Nat.add_le_add ini all).trans
  have a : initialPrice w r ≤ unitPrice w p r := by unfold unitPrice; omega
  have b : (TraceUniformRow.canonicalCost w p r+1)+TaggedShorterCPURow.price w p r ≤
      unitPrice w p r := by unfold unitPrice; omega
  calc
    _ ≤ unitPrice w p r+f*unitPrice w p r := Nat.add_le_add a (Nat.mul_le_mul_left f b)
    _ = _ := by ring

theorem unitPrice_le (w p r : ℕ) : unitPrice w p r ≤ (w+1)*unitPrice 1 p r := by
  have budget (z : ℕ) : instructionBudget z r =
      2*(8+(z*10+1)+(r*((z*10+1)+1)+1)+2)+2*((z+1)*10+1)+10 := rfl
  simp only [unitPrice,initialPrice,TraceUniformRow.canonicalCost,TaggedShorterCPURow.price,budget]
  ring_nf
  omega

end Hierarchy.TaggedShorterClock

end
end OAI
