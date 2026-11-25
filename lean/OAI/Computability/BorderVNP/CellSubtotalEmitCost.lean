import OAI.Computability.BorderVNP.CellSubtotalInputs
import OAI.Computability.BorderVNP.CellEmitSequenceCost
import OAI.Computability.BorderVNP.CellCQFPrimitiveCosts

/-! # Aggregate native clock of the reported subtotal pass

The indexed mapper is charged at the actual list entries. The retained output of
one pass over all boxes is bounded by the compact serialization of the complete
directory, independently of the time spent computing that output. This avoids
squaring the exponent of the inner box scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram CellMacro.Generator

private theorem reports_length (D : Directory) : (reportsCode D.reportedCounts).length ≤ (Typed.directory D).length := by
  simp only [Typed.directory,prodCode,pairBits_length,reportsCode]
  omega

private noncomputable def reportSource := getReports.comp (Procedure.identity Typed.directory)

private theorem reportSource_meter (D : Directory) :
    reportSource.meter D ≤ (reportSource.bound.eval 1+3)*((Typed.directory D).length+1) := by
  have h := reportSource.cost_pow D (d := 1) (by unfold reportSource; cqf_degree)
  have hr := reports_length D
  rw [pow_one] at h
  change reportSource.cost D + (Typed.directory D).length + (reportsCode D.reportedCounts).length+1 ≤ _
  rw [Nat.add_mul]; omega

set_option maxHeartbeats 2000000 in
/-- One additional factor of the local load pays for all reported IDs. The input,
output and report-count bounds come from the compact directory. The child meter
is evaluated only on reports that occur, including zero and empty counts. -/
theorem subtotalGuards_meter_of_rows (B e j : ℕ) (he : 18 ≤ e) :
    ∃ K : ℕ, ∀ (D : Directory) (p X L : ℕ), 1 ≤ X → 1 ≤ L →
      D.reportedCounts.length ≤ B*X → (Typed.directory D).length ≤ B*X^2*L^j →
      (serialized 8 (D.program p)).length ≤ B*X^2*L^j →
      (∀ i : Fin D.reportedCounts.length, reportRow.meter (D,i.val,D.reportedCounts[i]) ≤ B*X^e*L^j) →
      (subtotalGuardsStmt (Procedure.identity Typed.directory)).meter D ≤ K*X^(e+1)*L^(j*9) := by
  obtain ⟨Q,hQ⟩ := meter_sequenceMapIdx Typed.directory Typed.naturals []
  let A := B+1
  let G := reportSource.bound.eval 1+3
  let C := B+(4*A)^9+(8*A^2)^2+1
  refine ⟨Q*(G*A+A*C),?_⟩
  intro D p X L hX hL hn hd hp hr
  let Y := L^j
  let Z := X^e*Y^9
  let n := D.reportedCounts.length
  let raw := (prodCode Typed.directory reportsCode (D,D.reportedCounts)).length
  let words := B*X^2*Y
  let span := Procedure.tabSpan (prodCode Typed.directory reportsCode) n (D,D.reportedCounts) words
  have hA : 1 ≤ A := Nat.succ_pos _
  have hY : 1 ≤ Y := Nat.one_le_pow j L hL
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.one_le_pow _ _ hX) (Nat.one_le_pow _ _ hY)
  have hpow (k q : ℕ) (hk : k ≤ e) (hq : q ≤ 9) : X^k*Y^q ≤ Z :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hX hk) (Nat.pow_le_pow_right hY hq)
  have hxy : 1 ≤ X^2*Y := Nat.mul_pos (Nat.one_le_pow _ _ hX) hY
  have hw : words+1 ≤ A*(X^2*Y) := by
    dsimp [words,A]
    rw [Nat.succ_mul,Nat.mul_assoc]
    omega
  have hnm : n+1 ≤ A*X := by
    change D.reportedCounts.length+1 ≤ (B+1)*X
    rw [Nat.succ_mul]; omega
  have hraw : raw+1 ≤ (4*A)*(X^2*Y) := by
    have hv := reports_length D
    change (Typed.directory D).length ≤ words at hd
    simp only [raw,prodCode,pairBits_length]
    rw [Nat.mul_assoc]
    omega
  have hspan : span ≤ (8*A^2)*(X^3*Y) := by
    have hpair := Nat.mul_le_mul hnm hw
    rw [show (A*X)*(A*(X^2*Y)) = A^2*(X^3*Y) by ring] at hpair
    have h₀ : A*(X^2*Y) ≤ A^2*(X^3*Y) := Nat.mul_le_mul (Nat.le_self_pow (by decide) _)
      (Nat.mul_le_mul_right Y (Nat.pow_le_pow_right hX (by decide)))
    have h₁ : A*X ≤ A^2*(X^3*Y) := by
      apply Nat.mul_le_mul (Nat.le_self_pow (by decide) _)
      exact (Nat.le_self_pow (by decide) X).trans (Nat.le_mul_of_pos_right _ hY)
    change raw+n+(n+1)*(words+1)+1 ≤ _
    rw [Nat.mul_assoc] at hraw ⊢
    omega
  have h₀ : B*X^e*Y ≤ B*Z := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by simpa using hpow e 1 le_rfl (by decide))
  have h₁ : (raw+1)^9 ≤ (4*A)^9*Z := by
    apply (Nat.pow_le_pow_left hraw 9).trans
    rw [Nat.mul_pow (4*A) (X^2*Y), Nat.mul_pow (X^2) Y,← Nat.pow_mul]
    exact Nat.mul_le_mul_left _ (hpow 18 9 he le_rfl)
  have h₂ : span^2 ≤ (8*A^2)^2*Z := by
    apply (Nat.pow_le_pow_left hspan 2).trans
    rw [Nat.mul_pow (8*A^2) (X^3*Y),Nat.mul_pow (X^3) Y,← Nat.pow_mul]
    exact Nat.mul_le_mul_left _ (hpow 6 2 (by omega) (by decide))
  have hbody : B*X^e*Y+(raw+1)^9+span^2+1 ≤ C*Z := by
    dsimp [C]; rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.one_mul]; omega
  have hout (i : Fin n) : (serialized 8 (Gadget.row D i D.reportedCounts[i])).length ≤ words :=
    (reportRow_output_length D p i).trans hp
  have hchild (i : Fin n) : reportRow.cost (D,i.val,D.reportedCounts[i]) ≤ B*X^e*Y :=
    (Procedure.cost_le_meter _ _).trans (hr i)
  have htotal := hQ (f := Gadget.row) reportSource reportRow D hout hchild
  change (subtotalGuardsStmt (Procedure.identity Typed.directory)).meter D ≤
    Q*(reportSource.meter D+(n+1)*(B*X^e*Y+(raw+1)^9+span^2+1)) at htotal
  have hprep := reportSource_meter D
  have hdir : (Typed.directory D).length+1 ≤ A*Z :=
    (Nat.add_le_add_right hd 1).trans (hw.trans (Nat.mul_le_mul_left _ (by simpa using hpow 2 1 (by omega) (by decide))))
  have hprep' := hprep.trans (Nat.mul_le_mul_left G hdir)
  have hpre : G*(A*Z) ≤ G*A*(X*Z) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hX)
  have hrows := Nat.mul_le_mul hnm hbody
  rw [show (A*X)*(C*Z) = A*C*(X*Z) by ring] at hrows
  apply htotal.trans
  have hsum := Nat.add_le_add (hprep'.trans hpre) hrows
  rw [← Nat.add_mul] at hsum
  calc _ ≤ Q*((G*A+A*C)*(X*Z)) := Nat.mul_le_mul_left _ hsum
       _ = _ := by dsimp [Z,Y]; rw [Nat.pow_succ, Nat.pow_mul]; ring

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
