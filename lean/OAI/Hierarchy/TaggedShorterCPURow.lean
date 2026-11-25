import OAI.Hierarchy.TaggedShorterALU
import OAI.Hierarchy.TaggedShorterCheapCPU
import OAI.Hierarchy.TaggedShorterCPURead
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # A physical linear-size step check with shared ALU and comparison buses -/

noncomputable section
namespace Hierarchy.TaggedShorterCPURow
open ThreeFlat Routing Diagonal TracePair TraceIssue TraceWords TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open TaggedShorterCPURead
open scoped Classical BigOperators

variable {F : Type*} [CommRing F] {w p r k : ℕ}
abbrev Aux (w p : ℕ) := Flag p ⊕ (Fin p × Fin w)
abbrev Gates (p : ℕ) := Option (Option (Fin p))

private def line (word : Fin w → Bool) : TraceCompose.Batch (Raw w r) (Fin w) :=
  ⟨0,.nil, fun j => .const (word j)⟩

private theorem line_eval (word : Fin w → Bool) (x : Raw w r → Bool) (j : Fin w) :
    (line word).eval x j = word j := rfl

def alu (pub : Fin k → Word w) : Instr w p r k → TraceCompose.Batch (Raw w r) (Fin w)
  | .constant _ v _ => line (bits v)
  | .publicWord _ i _ => line (bits (pub i))
  | .binary op _ a b _ => TaggedShorterALU.batch op a b
  | _ => line (fun _ => false)

theorem alu_eval (pub : Fin k → Word w) (a : Instr w p r k) (x : Raw w r → Bool) (j : Fin w) :
    (alu pub a).eval x j=(aluPacket pub j a).2.eval x := by
  cases a <;> simp only [alu,aluPacket,line_eval,formulaPacket_eval,
    BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
    TaggedShorterALU.batch,TaggedShorterBoolBatch.wordBatch_eval,TraceBoolNet.outputCircuit_eval]

def flags (M : Machine w p r k) : TraceCompose.Batch (Raw w r) (Fin (Fintype.card (Flag p))) :=
  TraceCompose.gather (fun i => formulaPacket (predicate M ((Fintype.equivFin _).symm i)))

private def numbered (s : Raw w r) : Fin (Fintype.card (Pins w p r)) := Fintype.equivFin _ (.inl s)

def part (M : Machine w p r k) : Gates p → BitNetwork F (Fintype.card (Pins w p r))
  | none => TraceCircuit.localNetwork (fun _ : Fin 1 => residual M) (Fintype.equivFin _)
      (fun _ b => if b then 1 else 0)
  | some none => TaggedShorterBoolBatch.network (flags M) numbered
      (fun i => Fintype.equivFin _ (.inr (.inl ((Fintype.equivFin _).symm i))))
  | some (some i) => TaggedShorterBoolBatch.network (alu M.publicData (M.code i)) numbered
      (fun j => Fintype.equivFin _ (.inr (.inr (i,j))))

def network (M : Machine w p r k) : BitNetwork F (Fintype.card (Raw w r)) :=
  TypedWiring.glue (part M) (fun _ t => (t : Raw w r ⊕ Aux w p))

private def auxValue (M : Machine w p r k) (x : Raw w r → Bool) : Aux w p → Bool :=
  fun t => assigned M x (.inr t)

private theorem residual_value (M : Machine w p r k) (x : Raw w r → Bool) (a : Aux w p → Bool) :
    TypedWiring.value (part (F:=F) M none) (Sum.elim x a) =
      if (residual M).2.eval (Sum.elim x a) then 1 else 0 := by
  simp [TypedWiring.value,part,TraceCircuit.localNetwork_eval,Function.comp_def]

private theorem flag_value (M : Machine w p r k) (x : Raw w r → Bool) (a : Aux w p → Bool) :
    TypedWiring.value (part (F:=F) M (some none)) (Sum.elim x a) =
      if ∀ f, auxValue M x (.inl f)=a (.inl f) then 1 else 0 := by
  unfold TypedWiring.value part
  rw [TaggedShorterBoolBatch.eval]
  simp only [numbered,Function.comp_def,Equiv.symm_apply_apply,flags,TraceCompose.gather_eval,
    formulaPacket_eval,Sum.elim_inl,Sum.elim_inr,auxValue,assigned]
  congr 1
  apply propext
  constructor
  · intro all f
    simpa only [Equiv.symm_apply_apply] using all ((Fintype.equivFin (Flag p)) f)
  · intro all i
    exact all _

private theorem alu_value (M : Machine w p r k) (x : Raw w r → Bool) (a : Aux w p → Bool) (i : Fin p) :
    TypedWiring.value (part (F:=F) M (some (some i))) (Sum.elim x a) =
      if ∀ j, auxValue M x (.inr (i,j))=a (.inr (i,j)) then 1 else 0 := by
  unfold TypedWiring.value part
  rw [TaggedShorterBoolBatch.eval]
  simp only [Function.comp_def,numbered,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,auxValue,assigned,alu_eval]
  by_cases yes : ∀ j, (aluPacket M.publicData j (M.code i)).2.eval x = a (.inr (i,j))
  · exact (ite_eq_left yes).trans (ite_eq_left yes).symm
  · exact (ite_eq_right yes).trans (ite_eq_right yes).symm

theorem eval (M : Machine w p r k) (x : Raw w r → Bool) :
    TypedWiring.value (network (F:=F) M) x =
      if (pairCircuit M).2.eval x then 1 else 0 := by
  let : DecidableEq (Aux w p) := Classical.decEq _
  rw [network,TypedWiring.glue_value,Finset.sum_eq_single (auxValue M x)]
  · have inp : Sum.elim x (auxValue M x) = assigned M x := by funext i; cases i <;> rfl
    simp only [Fintype.prod_option,residual_value,flag_value,alu_value]
    rw [inp,residual_eval]
    simp
  · intro a _ ne
    obtain ⟨s,bad⟩ := Function.ne_iff.mp ne
    cases s with
    | inl f =>
      apply Finset.prod_eq_zero (Finset.mem_univ (some none))
      rw [flag_value]
      exact ite_eq_right (fun h => bad (h f).symm)
    | inr s =>
      obtain ⟨i,j⟩ := s
      apply Finset.prod_eq_zero (Finset.mem_univ (some (some i)))
      rw [alu_value]
      exact ite_eq_right (fun h => bad (h j).symm)
  · simp

theorem checks (M : Machine w p r k) (h : 3≤w+1) (hp : p≤2^(w+1)) (x y : Record w p r) :
    TypedWiring.value (network (F:=F) M) (packed h hp x y) =
      if TraceRows.pair (exposed M) x y then 1 else 0 := by
  rw [eval]
  have ok := pairCircuit_correct h hp M x y
  by_cases t : TraceRows.pair (exposed M) x y <;> simp [←ok] at *

end Hierarchy.TaggedShorterCPURow

end
end OAI
