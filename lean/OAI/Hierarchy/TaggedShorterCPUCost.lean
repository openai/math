import OAI.Hierarchy.TaggedShorterCPURow
import OAI.ThreeFlat.BitNetwork.UsedHidden

namespace OAI
/-! # Cell accounting of the actual CPU row verifier -/

noncomputable section
namespace Hierarchy.TaggedShorterCPURow
open ThreeFlat Routing Diagonal TracePair TraceIssue TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM
open TaggedShorterCPURead TaggedShorterCheapCPU
open scoped Classical BigOperators

variable {F : Type*} [CommRing F] {w p r k : ℕ}

theorem flags_count (p : ℕ) : Fintype.card (Flag p)=10+3*p := by
  rw [←Fintype.card_congr (Flag.proxyTypeEquiv p)]
  have tags : Fintype.card Tag=7 := by decide
  simp [Fintype.card_sigma,tags]
  ring

/-- For a fixed program, its register count and number of program counters
are constants, while the native word length may grow. -/
def price (w p r : ℕ) :=
  80*(3*p+4*w+2*r*w+p*w+11)+4*(p*(instructionBudget w r+3)+32)+1 +
    (10+3*p)*(800*(w+1)+1)+p*(317*w+12)

private theorem alu_size (M : Machine w p r k) (i : Fin p) (ok : Cheap (M.code i)) :
    (part (F:=F) M (some (some i))).cells ≤ 317*w+12 := by
  have cellPart : (part (F:=F) M (some (some i))).cells ≤
    (part (F:=F) M (some (some i))).cells+(part (F:=F) M (some (some i))).internal :=
      Nat.le_add_right ..
  apply cellPart.trans
  change (TaggedShorterBoolBatch.network _ _ _).cells+(TaggedShorterBoolBatch.network _ _ _).internal≤_
  rw [TaggedShorterBoolBatch.size]
  cases hop : M.code i with
  | binary op dst a b next =>
    have good : op=.add ∨ op=.sub ∨ op=.bitAnd := by
      cases op <;> simp_all [Cheap]
    have h := TaggedShorterALU.size (F:=F) op good a b
      (fun _ : Raw w r => (0 : Fin 1)) (fun _ : Fin w => (0 : Fin 1))
    simpa only [alu,TaggedShorterALU.network,TaggedShorterBoolBatch.size] using h
  | _ => change 2*0+w≤_; omega

theorem cells (M : Machine w p r k) (ok : ∀ i, Cheap (M.code i)) :
    (network (F:=F) M).cells≤price w p r := by
  rw [network,TypedWiring.glue_cells,Fintype.sum_option,Fintype.sum_option]
  have residualBound : (part (F:=F) M none).cells≤
      80*(3*p+4*w+2*r*w+p*w+11)+4*(p*(instructionBudget w r+3)+32)+1 := by
    simpa [part] using Nat.add_le_add_right (residual_size M) 1
  have sizeFlags : (flags M).size≤(10+3*p)*(400*(w+1)) := by
    rw [flags,TraceCompose.gather_size]
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      (formulaPacket_size_le (predicate M ((Fintype.equivFin _).symm i))).trans
        (Nat.mul_le_mul_left 4 (predicate_size M ((Fintype.equivFin _).symm i))))
    have count : (∑ _ : Fin (Fintype.card (Flag p)),4*(100*(w+1)))=(10+3*p)*(400*(w+1)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,flags_count,Nat.cast_id]
      ring
    exact hs.trans_eq count
  have flagBound : (part (F:=F) M (some none)).cells≤(10+3*p)*(800*(w+1)+1) := by
    change (flags M).size+Fintype.card (Flag p)≤_
    calc
      _ ≤ (10+3*p)*(400*(w+1))+(10+3*p) := Nat.add_le_add sizeFlags (flags_count p).le
      _ = (10+3*p)*(400*(w+1)+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have aluBound : (∑ i, (part (F:=F) M (some (some i))).cells)≤p*(317*w+12) := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => alu_size M i (ok i))
  unfold price
  omega

theorem normalized_size (M : Machine w p r k) (ok : ∀ i, Cheap (M.code i)) :
    (network (F:=F) M).compactHidden.cells+(network (F:=F) M).compactHidden.internal≤4*price w p r+1 :=
  (BitNetwork.compactHidden_size _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (cells M ok)) 1)

end Hierarchy.TaggedShorterCPURow

end
end OAI
