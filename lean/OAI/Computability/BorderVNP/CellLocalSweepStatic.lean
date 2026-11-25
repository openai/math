import OAI.Computability.BorderVNP.CellLocalSweepWidth
import OAI.Computability.BorderVNP.CellLocalSweepRows

/-! # Mixed local-load and global-width clock for an entire private box sweep

Each visited factor receives only a fixed-size table and polynomially bounded
scalar fields. The actual table traversal pays degree thirty-one in the size
of the complete one-copy input and output directories. The resulting degree
in the local load is sixty-two, independent of the scalar printer's degree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

set_option maxHeartbeats 1200000 in
private theorem sweep_product (a b s x L j d : ℕ) :
    a*(b*L^(j*d))^4*(s*x^2*L^j)^31 = a*b^4*s^31*x^62*L^(j*d*4+j*31) := by
  rw [mul_pow,mul_pow,mul_pow,pow_add]
  simp only [← pow_mul,Nat.reduceMul]
  ring

set_option maxHeartbeats 1200000 in
/-- The complete physical sweep handles arbitrary global identifier values when their
binary widths fit the supplied scale. All constants precede the directory and the order. -/
theorem sweepPrinter_meter_static_width (mode : Pass) (A T B j : ℕ) :
    ∃ C e : ℕ, 0 < C ∧ 0 < e ∧ ∀ (params : Params) (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      ParamsWidth params (B*L^j) → (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      (sweepPrinter mode).meter (params,D) ≤ C*(M+1)^62*L^e := by
  obtain ⟨F,d,hF⟩ := printer_meter_fields_width mode T
  obtain ⟨K,hK⟩ := sweepPrinter_rows_meter mode
  let Q := F*(3*B+2)^d
  let S := (300*(8*A+4)+8*A+8)*(B+1)
  refine ⟨(K+1)*(Q+1)^4*S^31,j*d*4+j*31+1,by dsimp [S]; positivity,by omega,?_⟩
  intro params D p M U L hL hs hstore hraw hu hp ht
  let V := visitMax U params
  let X := M+1
  have hOne : 1 ≤ L^j := Nat.one_le_pow _ _ hL
  have hwidth := visitMax_cube_width hu hp
  have hw : ((V+1)^3).size+1 ≤ (3*B+2)*L^j := by
    change ((V+1)^3).size+1 ≤ 3*(B*L^j)+2 at hwidth
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  have row (i : Fin D.blocks.length) (k : Fin (D.blocks[i.val]'i.isLt).factors.length) :
      (printer mode).meter (factorAt (visit (params,D) i (D.blocks[i.val]'i.isLt)) k) ≤ Q*L^(j*d) := by
    let x := factorAt (visit (params,D) i (D.blocks[i.val]'i.isLt)) k
    have hh := visitMax_bounds U params
    have hfields := visit_fields D params hraw hh.1 hh.2 i k
    have hm := hF x ((V+1)^3) hfields.1 hfields.2
      (resolved_tableBound D ht _ (List.getElem_mem ..) _ (List.getElem_mem ..))
    apply hm.trans ((Nat.mul_le_mul_left F (Nat.pow_le_pow_left hw d)).trans_eq ?_)
    simp only [Q,Nat.mul_pow,← pow_mul,Nat.mul_assoc]
  have hrun := hK (params,D) (Q*L^(j*d)) row
  have hsize := sweepSpan_static_width D p params hs hstore hraw hu hp
  have hspan : sweepSpan (params,D)+1 ≤ S*X^2*L^j := by
    apply hsize.trans
    calc (300*(8*A+4)+8*A+8)*(M+1)^2*(B*L^j) =
           (300*(8*A+4)+8*A+8)*B*X^2*L^j := by dsimp [X]; ring
         _ ≤ S*X^2*L^j := by dsimp only [S]; gcongr; omega
  have hR : 1 ≤ L^(j*d) := Nat.one_le_pow _ _ hL
  have hchild : Q*L^(j*d)+1 ≤ (Q+1)*L^(j*d) := by rw [Nat.add_mul,Nat.one_mul]; omega
  have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_left hchild 4))
    (Nat.pow_le_pow_left hspan 31)
  calc (sweepPrinter mode).meter (params,D) ≤ _ := hrun
       _ ≤ _ := h
       _ = (K+1)*(Q+1)^4*S^31*(M+1)^62*L^(j*d*4+j*31) := sweep_product ..
       _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by omega))

/-- Specialization to polynomial numerical field values, including larger computed
parameters, gives a bound in the binary length of the global input order. -/
theorem sweepPrinter_meter_static (mode : Pass) (A T B j : ℕ) :
    ∃ C e : ℕ, 0 < C ∧ 0 < e ∧ ∀ (params : Params) (D : Directory) (p M U n : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U ≤ B*(n+2)^j →
      ParamsBound params (B*(n+2)^j) → (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      (sweepPrinter mode).meter (params,D) ≤ C*(M+1)^62*(n.size+1)^e := by
  obtain ⟨C,e,hC,he,run⟩ := sweepPrinter_meter_static_width mode A T (B.size+j+1) 1
  refine ⟨C,e,hC,he,?_⟩
  intro params D p M U n hs hstore hraw hu hp ht
  have width (v : ℕ) (hv : v ≤ B*(n+2)^j) : v.size+1 ≤ (B.size+j+1)*(n.size+1)^1 := by
    have hb := CellMacro.Generator.size_of_polynomial_field hv
    rw [pow_one,Nat.add_mul,Nat.add_mul,Nat.one_mul]
    have := Nat.le_mul_of_pos_right B.size (by omega : 0 < n.size+1)
    omega
  exact run params D p M U (n.size+1) (by omega) hs hstore hraw (width _ hu)
    ⟨width _ hp.1,width _ hp.2.1,width _ hp.2.2⟩ ht

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
