import OAI.ThreeFlat.Diagonal.TracePortCardinality
import OAI.ThreeFlat.Diagonal.TraceStaticTable
import OAI.ThreeFlat.Diagonal.TraceRowCostLemmas

namespace OAI
/-! # Polynomial ROM footprint of the common trace gate table and control ports -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM TraceWords TraceRows TraceBanks TraceCompose TraceRowPackets TraceProgram TracePair TraceIssue
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
variable {F : Type*} [CommRing F] [Fintype F] {w p r k d : ℕ}

set_option maxHeartbeats 1200000 in
/-- The controls in the repeated table add one constant-size Boolean
multiplexer per checked branch. -/
theorem template_size (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base f : ℕ) (st : Word w) (a : TraceUniformRow.Check F w p k) :
    (template (r:=r) (d:=d) hF hw hp base f st a).1 ≤ packetBound (Fintype.card F) w p r k d := by
  classical
  have hs (j : Outer w p k) (b : Packet (Port w p r k d)) (default : Bool) :
      (select (flag j) b (literal default)).1 ≤ b.1+100 := by
    simpa [flag,TraceRowPackets.read,literal] using select_count (flag j) b (literal default)
  unfold packetBound TraceUniformRow.checkCost
  rcases a with ((u|⟨s,j|i⟩)|(u|⟨j,b⟩))
  · cases u
    rw [template,liftPort_count]
    exact (staticMemory_size (r:=r) (d:=d) hw).trans (by omega)
  · fin_cases j
    · change (select (flag _) _ _).1 ≤ _
      apply (hs ..).trans
      simp only [substituteFintype_size,TraceRowPackets.read,Finset.sum_const_zero,zero_add]
      have hc := TraceUniformRow.canonical_bound (r:=r) hw hp
      omega
    · change (select (flag _) _ _).1 ≤ _
      apply (hs ..).trans
      simp only [liftPort_count,substituteFintype_size,TraceUniformRow.joint_size,Finset.sum_const_zero,zero_add]
      have hc := uniformPair_size_le w p r k
      omega
    · change (select (flag _) _ _).1 ≤ _
      apply (hs ..).trans
      rw [liftPort_count]
      have hc := TraceUniformRow.first_bound (r:=r) (k:=k) (d:=d) hp s st
      omega
  · rw [template]
    apply (hs ..).trans
    simp only [substituteFintype_size,TraceRowPackets.read,Finset.sum_const_zero,zero_add]
    have hc := TraceUniformRow.terminal_bound (r:=r) hF hw i
    omega
  · cases u
    change (select (flag _) _ _).1 ≤ _
    apply (hs ..).trans
    rw [liftPort_count]
    have hc := headerCircuit_size_le w p k
    omega
  · cases b
    all_goals
      change (select (flag _) _ _).1 ≤ _
      apply (hs ..).trans
      apply Nat.add_le_add_right
      apply (TracePair.formulaPacket_size_le _).trans
      simp only [same_size,Expr.size]
      omega

theorem gateTable_size (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base f : ℕ) (st : Word w) :
    (gateTable hF hw hp base f st r k d).cells ≤ cellsBound (Fintype.card F) w p r k d := by
  rw [gateTable,TracePacketArray.one_count,TracePacketArray.one_internal]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => template_size (r:=r) (d:=d) hF hw hp base f st
    (a : TraceUniformRow.Check F w p k))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  unfold cellsBound
  calc
    _ ≤ Fintype.card (TraceUniformRow.Check F w p k) * packetBound (Fintype.card F) w p r k d + _ := Nat.add_le_add_right h _
    _ = _ := by rw [TraceUniformRow.card_check]; exact (Nat.mul_succ _ _).symm

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
