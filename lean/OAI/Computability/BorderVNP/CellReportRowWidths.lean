import OAI.Computability.BorderVNP.CellReportRowSource
import OAI.Computability.BorderVNP.CellLocalSweepWidth
import OAI.Computability.BorderVNP.CellCQFMeasured

/-! # Binary sizes of the local procedures used by one indexed subtotal row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open CellMacro.Generator ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

/-- The prefix cap, its scratch rectangle and the binary gadget index have
at most a constant times the largest raw field's bit length. -/
theorem report_params_width (D : Directory) (i : Fin D.reportedCounts.length) {p U : ℕ}
    (raw : RawFields D p U) :
    Local.ParamsWidth (D.visitCount,(D.visitCount+1)*(D.visitCount+1),i.val) (17*(U.size+1)) := by
  obtain ⟨h,_⟩ := report_params_bound D i (B := 1) (j := 1) (n := U) raw (by simp)
  have small (x : ℕ) (hx : x ≤ 3^6*(U+2)^6) : x.size+1 ≤ 17*(U.size+1) := by
    have h := size_of_polynomial_field hx
    rw [show (3^6 : ℕ).size = 10 by decide] at h
    omega
  exact ⟨small _ h.1,small _ h.2.1,small _ h.2.2⟩

private theorem scalar_meter {T : Type} {enc : T → List Bool} {f : ℕ → T} (p : Procedure Nat.bits enc f) :
    ∃ C d : ℕ, ∀ n, p.meter n ≤ C*(n.size+1)^d := by
  let d := p.bound.natDegree+1
  obtain ⟨C,h⟩ := Measured.of_degree Nat.size d (Nat.succ_pos _) p id
    (Nat.le_succ _) (H := 1) (by intro n; simp [Nat.size_eq_bits_len])
  exact ⟨C,d,h⟩

/-- After the true visit count is computed, the scalar initialization and
rectangle computation each run on its canonical binary encoding. -/
theorem scalarRow_polylog (B j : ℕ) : ∃ C k : ℕ, ∀ cap L : ℕ, 0 < L →
    cap.size+1 ≤ B*L^j → gadgetRectangle.meter cap + gadgetInit.meter cap ≤ C*L^k := by
  obtain ⟨P,d,hp⟩ := scalar_meter gadgetRectangle
  obtain ⟨Q,e,hq⟩ := scalar_meter gadgetInit
  refine ⟨P*B^d+Q*B^e,j*(d+e),fun cap L hL hc => ?_⟩
  have grow (a i : ℕ) (h : a ≤ i) : L^(j*a) ≤ L^(j*i) :=
    Nat.pow_le_pow_right hL (Nat.mul_le_mul_left _ h)
  have h₁ := (hp cap).trans (Nat.mul_le_mul_left P (Nat.pow_le_pow_left hc d))
  have h₂ := (hq cap).trans (Nat.mul_le_mul_left Q (Nat.pow_le_pow_left hc e))
  rw [Nat.mul_pow,← pow_mul,← Nat.mul_assoc] at h₁ h₂
  rw [Nat.add_mul]
  exact Nat.add_le_add (h₁.trans (Nat.mul_le_mul_left _ (grow d (d+e) (by omega))))
    (h₂.trans (Nat.mul_le_mul_left _ (grow e (d+e) (by omega))))

/-- The localized terminal printer is polynomial in the global logarithmic
width, for every original report whose address count has that scale. -/
theorem terminalRow_polylog (B j R k : ℕ) : ∃ C e : ℕ, ∀ (D : Directory) (p U L : ℕ)
    (i : Fin D.reportedCounts.length), 0 < L → RawFields D p U → U.size+1 ≤ B*L^j →
    D.reportedCounts[i].length ≤ R*L^k →
    Finish.printer.meter (0,(D.visitCount+1)*(D.visitCount+1),D.visitCount,D.reportedCounts[i]) ≤ C*L^e := by
  obtain ⟨C,e,h⟩ := Finish.printer_polylog (17*B+R+1) (j+k)
  refine ⟨C,e,fun D p U L i hL raw hu hr => ?_⟩
  have plus : L-1+1 = L := by omega
  have hj := Nat.pow_le_pow_right hL (Nat.le_add_right j k)
  have hk := Nat.pow_le_pow_right hL (Nat.le_add_left k j)
  have hwidth := report_params_width D i raw
  have hnum : 17*(U.size+1) ≤ (17*B+R+1)*L^(j+k) := by
    calc _ ≤ 17*(B*L^j) := Nat.mul_le_mul_left _ hu
         _ = 17*B*L^j := (Nat.mul_assoc ..).symm
         _ ≤ _ := Nat.mul_le_mul (by omega) hj
  have he := h (0,(D.visitCount+1)*(D.visitCount+1),D.visitCount,D.reportedCounts[i]) (L-1)
  rw [plus] at he
  apply he
  · exact hr.trans (Nat.mul_le_mul (by omega) hk)
  · exact Nat.zero_le _
  · rw [Nat.size_eq_bits_len]; exact (Nat.le_succ _).trans (hwidth.2.1.trans hnum)
  · rw [Nat.size_eq_bits_len]; exact (Nat.le_succ _).trans (hwidth.1.trans hnum)
  · intro a ha
    have hu' := Nat.size_le_size ((raw.reports _ (List.getElem_mem i.isLt)).2 _ ha)
    rw [Nat.size_eq_bits_len]
    exact hu'.trans (by omega)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
