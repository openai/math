import OAI.Computability.BorderVNP.CellReportRowWidths
import OAI.Computability.BorderVNP.CellLocalSweepStatic

/-! # Mixed local-load and global-bit-width clock for every actual subtotal row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open CellMacro.Generator ExactQuantumFactoring.BitStackProgram

/-- The true installed child of the native subtotal traversal has degree at most
62 in the local incidence load. The widths of the scalar identifiers and of each
announced subtotal enter only in a fixed polynomial in the separate bit scale. -/
theorem reportRow_meter_static_width (A T B j R k : ℕ) :
    ∃ C e : ℕ, 0 < C ∧ 0 < e ∧ ∀ (D : Directory) (p M U L : ℕ) (i : Fin D.reportedCounts.length),
      0 < L → D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U →
      U.size+1 ≤ B*L^j → (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      (∀ bs ∈ D.reportedCounts, bs.length ≤ R*L^k) →
      reportRow.meter (D,i.val,D.reportedCounts[i]) ≤ C*(M+1)^62*L^e := by
  obtain ⟨G,_,hg⟩ := getVisitCount_meter_static_width A B j
  obtain ⟨S,s,_,_,hs⟩ := Local.sweepPrinter_meter_static_width .gadget A T (17*B) j
  obtain ⟨Q,q,hq⟩ := scalarRow_polylog (17*B) j
  obtain ⟨F,t,hf⟩ := terminalRow_polylog B j R k
  let P := (300*(8*A+4)+8*A)*B
  let C := P+G+Q+S+F+scopedGlue+1
  let e := j+j*30+s+q+t+1
  refine ⟨10^149*C,e,Nat.mul_pos (by norm_num) (Nat.succ_pos _),Nat.succ_pos _,?_⟩
  intro D p M U L i hL st store raw hu tables width
  let X := M+1
  let bs := D.reportedCounts[i]
  let c := D.visitCount
  let aux := (c+1)*(c+1)
  let params : Local.Params := (c,aux,i.val)
  let Z := X^62*L^e
  have hx : 1 ≤ X := Nat.succ_pos M
  have grow (b a : ℕ) (hb : b ≤ 62) (ha : a ≤ e) : X^b*L^a ≤ Z :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hx hb) (Nat.pow_le_pow_right hL ha)
  have pure (a : ℕ) (ha : a ≤ e) : L^a ≤ Z := by simpa only [pow_zero,one_mul] using grow 0 a (by decide) ha
  have one : 1 ≤ Z := by simpa only [pow_zero] using pure 0 (Nat.zero_le _)
  have hc := report_params_width D i raw
  have enlarge : 17*(U.size+1) ≤ (17*B)*L^j := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hu
  have hh : Local.ParamsWidth params ((17*B)*L^j) :=
    ⟨hc.1.trans enlarge,hc.2.1.trans enlarge,hc.2.2.trans enlarge⟩
  have hr : U.size+1 ≤ (17*B)*L^j := hu.trans (Nat.mul_le_mul_right _ (by omega))
  have heG := hg D p M U L hL st store raw hu
  have heS := hs params D p M U L hL st store raw hr hh tables
  have heQ := hq c L hL hh.1
  have heF := hf D p U L i hL raw hu (width _ (List.getElem_mem i.isLt))
  have heP : (Typed.directory D).length ≤ P*Z := by
    have hdir : (Typed.directory D).length ≤ blockSpan D := Nat.le_add_right ..
    apply hdir.trans ((blockSpan_static_width D p st store raw).trans ?_)
    calc (300*(8*A+4)+8*A)*(M+1)^2*(U.size+1) ≤ (300*(8*A+4)+8*A)*X^2*(B*L^j) := Nat.mul_le_mul_left _ hu
         _ = P*(X^2*L^j) := by dsimp only [P]; ring
         _ ≤ P*Z := Nat.mul_le_mul_left _ (grow 2 j (by decide) (by dsimp [e]; omega))
  have g : getVisitCount.meter D ≤ G*Z := heG.trans (by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (grow 60 (j*30) (by decide) (by dsimp [e]; omega)))
  have sw : (Local.sweepPrinter .gadget).meter (params,D) ≤ S*Z := heS.trans (by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (grow 62 s (by decide) (by dsimp [e]; omega)))
  have scalar : gadgetRectangle.meter c+gadgetInit.meter c ≤ Q*Z := heQ.trans
    (Nat.mul_le_mul_left _ (pure q (by dsimp [e]; omega)))
  have term : Finish.printer.meter (0,aux,c,bs) ≤ F*Z := heF.trans
    (Nat.mul_le_mul_left _ (pure t (by dsimp [e]; omega)))
  have glue : scopedGlue ≤ scopedGlue*Z := Nat.le_mul_of_pos_right _ one
  have charge : (Typed.directory D).length+scopedGlue+rowCharge D i bs+1 ≤ C*Z := by
    change (Typed.directory D).length+scopedGlue+
      (getVisitCount.meter D+gadgetRectangle.meter c+gadgetInit.meter c+
        (Local.sweepPrinter .gadget).meter (params,D)+Finish.printer.meter (0,aux,c,bs))+1 ≤ _
    dsimp only [C]; simp only [Nat.add_mul,Nat.one_mul]
    omega
  apply (reportRow_meter_components D i).trans
  rw [show (10^149*C)*(M+1)^62*L^e = 10^149*(C*Z) by dsimp [Z,X]; ring]
  exact Nat.mul_le_mul_left _ charge

/-- If every raw scalar is polynomial in a numeric size parameter, its binary
width condition follows from the size of that parameter. -/
theorem reportRow_meter_static (A T B j R k : ℕ) :
    ∃ C e : ℕ, 0 < C ∧ 0 < e ∧ ∀ (D : Directory) (p M U n L : ℕ) (i : Fin D.reportedCounts.length),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U →
      U ≤ B*(n+2)^j → n.size+1 ≤ L → (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      (∀ bs ∈ D.reportedCounts, bs.length ≤ R*L^k) →
      reportRow.meter (D,i.val,D.reportedCounts[i]) ≤ C*(M+1)^62*L^e := by
  obtain ⟨C,e,hC,he,h⟩ := reportRow_meter_static_width A T (B.size+j+1) 1 R k
  refine ⟨C,e,hC,he,fun D p M U n L i st store raw hu hL tables widths =>
    h D p M U L i (by omega) st store raw ?_ tables widths⟩
  have hh := size_of_polynomial_field hu
  rw [pow_one,Nat.add_mul,Nat.one_mul,Nat.add_mul]
  have h₁ := Nat.le_mul_of_pos_right B.size (by omega : 0 < L)
  have h₂ := Nat.mul_le_mul_left j hL
  omega

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
