import OAI.Computability.BorderVNP.CellSubtotalEmitCost
import OAI.Computability.BorderVNP.CellTypedDirectorySize
import OAI.Computability.BorderVNP.CellDirectoryInputSize
import OAI.Computability.BorderVNP.CellReportRowScale
import OAI.Computability.BorderVNP.CellReportFieldWidth

/-! # Physical running time for all subtotal descriptors

The native procedure resolves the cell's box tables and emits the prefix
and digit guards for each supplied report. Static one-copy mass bounds its
input and output lengths. Binary field widths and the fixed size of each
factor table control the local computations independently of the cell load.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram CellMacro.Generator

/-- Quadratic output length using only the bit width of the fields. This also
covers global addresses that grow with the stretching parameter. -/
theorem program_output_width (D : Directory) (p : ℕ) {A M V G g L : ℕ}
    (hs : D.StaticBounds A M) (hc : D.CompactFields p V) (hw : V.size+1 ≤ G*L^g) :
    (serialized 8 (D.program p)).length ≤
      (16^4*64^9 * directoryMassCoefficient A * ((10000*3^3 : ℕ).size+6)*G)*(M+1)^2*L^g := by
  have hv : V ≤ 1*(V+2)^1 := by simp
  have h := D.program_serialized_length_le p hs hc hv
  apply h.trans
  calc _ ≤ _*(G*L^g) := Nat.mul_le_mul_left _ hw
       _ = _ := by simp only [Nat.one_add]; ring

private theorem collect_rows (A B j G g C e : ℕ) :
    ∃ K t : ℕ, 0 < K ∧ 0 < t ∧ ∀ (D : Directory) (p M E U V L : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → D.CompactFields p V →
      1 ≤ L → U.size+1 ≤ B*L^j → V.size+1 ≤ G*L^g →
      (∀ i : Fin D.reportedCounts.length, reportRow.meter (D,i.val,D.reportedCounts[i]) ≤ C*(M+1)^62*L^e) →
      (subtotalGuardsStmt (Procedure.identity Typed.directory)).meter D ≤ K*(M+E+1)^63*L^t := by
  let J := max (max j g) e + 1
  let Cin := 300*(8*A+4)*B
  let Cout := 16^4*64^9*directoryMassCoefficient A*((10000*3^3 : ℕ).size+6)*G
  let Q := A+Cin+Cout+C
  obtain ⟨K,hK⟩ := subtotalGuards_meter_of_rows Q 62 J (by decide)
  refine ⟨K+1,J*9,by omega,by dsimp [J]; omega,?_⟩
  intro D p M E U V L hs hm hr hc hL hU hV hrows
  let X := M+E+1
  have hM : M+1 ≤ X := by dsimp [X]; omega
  have hj : j ≤ J := by dsimp [J]; omega
  have hg : g ≤ J := by dsimp [J]; omega
  have he : e ≤ J := by dsimp [J]; omega
  have widen {b d t : ℕ} (hb : b ≤ Q) (ht : t ≤ J) :
      b*(M+1)^d*L^t ≤ Q*X^d*L^J :=
    Nat.mul_le_mul (Nat.mul_le_mul hb (Nat.pow_le_pow_left hM _)) (Nat.pow_le_pow_right hL ht)
  apply (hK D p X L (by omega) hL ?_ ?_ ?_ ?_).trans
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · exact hs.reports.trans (Nat.mul_le_mul (by dsimp [Q]; omega) hM)
  · apply (typed_directory_length D p hr).trans
    have hp := words_length_from_static D p hs hm
    calc _ ≤ 300*((8*A+4)*(M+1)^2)*(B*L^j) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hU
         _ = Cin*(M+1)^2*L^j := by dsimp [Cin]; ring
         _ ≤ _ := widen (by dsimp [Q]; omega) hj
  · exact (program_output_width D p hs hc hV).trans (widen (by change Cout ≤ Q; dsimp [Q]; omega) hg)
  · exact fun i => (hrows i).trans (widen (by dsimp [Q]; omega) he)

/-- The complete native subtotal pass has degree sixty-three in the local
load. The global identifiers and each individual report enter only through
their binary widths. The constants precede every directory and every order. -/
theorem subtotalGuards_meter_static_width (A T B j G g R k : ℕ) :
    ∃ K t : ℕ, 0 < K ∧ 0 < t ∧ ∀ (D : Directory) (p M E U V L : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → D.CompactFields p V →
      1 ≤ L → U.size+1 ≤ B*L^j → V.size+1 ≤ G*L^g →
      (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) → (∀ bs ∈ D.reportedCounts, bs.length ≤ R*L^k) →
      (subtotalGuardsStmt (Procedure.identity Typed.directory)).meter D ≤ K*(M+E+1)^63*L^t := by
  obtain ⟨C,e,_,_,hr⟩ := reportRow_meter_static_width A T B j R k
  obtain ⟨K,t,hK,ht,h⟩ := collect_rows A B j G g C e
  refine ⟨K,t,hK,ht,fun D p M E U V L hs hm raw hc hL hu hv tables digits =>
    h D p M E U V L hs hm raw hc hL hu hv (fun i => hr D p M U L i hL hs hm raw hu tables digits)⟩

/-- For the contiguous little-endian count bank, the numerical count cap's
bit length gives the report width uniformly, including the zero-width case. -/
theorem subtotalGuards_meter_countFields (A T B j G g R k : ℕ) :
    ∃ K t : ℕ, 0 < K ∧ 0 < t ∧ ∀ (D : Directory) (p M E U V L base gadgets cap : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → D.CompactFields p V →
      1 ≤ L → U.size+1 ≤ B*L^j → V.size+1 ≤ G*L^g → (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      D.reportedCounts = DiagonalTallyCellReports.countFields base gadgets (Nat.clog 2 (cap+1)) →
      cap.size ≤ R*L^k →
      (subtotalGuardsStmt (Procedure.identity Typed.directory)).meter D ≤ K*(M+E+1)^63*L^t := by
  obtain ⟨K,t,hK,ht,h⟩ := subtotalGuards_meter_static_width A T B j G g R k
  refine ⟨K,t,hK,ht,fun D p M E U V L base gadgets cap hs hm hr hc hL hu hv tables layout width =>
    h D p M E U V L hs hm hr hc hL hu hv tables ?_⟩
  intro bs hb
  rw [layout] at hb
  rwa [DiagonalTallyCellReports.countField_length _ _ _ hb, Finish.countWidth_eq]

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
