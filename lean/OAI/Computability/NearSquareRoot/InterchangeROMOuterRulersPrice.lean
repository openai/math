import OAI.Computability.NearSquareRoot.InterchangeROMOuterRulers
import OAI.Computability.NearSquareRoot.InterchangeROMBankRulers
import OAI.Computability.NearSquareRoot.InterchangeROMBankReindex
import OAI.Computability.NearSquareRoot.InterchangeROMRecursionThick
import OAI.Computability.NearSquareRoot.InterchangeROMOuterGeometry
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Native accounting for the center bank's emitted wiring -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter.Wire

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom Space InterchangeAddress InterchangeROMExpose InterchangeROMRecursion
  InterchangeROMBankRulers

abbrev out (i : Input) (W : ℕ) : Wire.Rulers :=
  (send (cutTriple i i.b),send (cutTriple i (BatchRows.groups i.b W)),send (bankHeader i W))

private def scale (v : Input × ℕ) := v.2+v.1.b+v.1.n+v.1.req.header.count

private theorem input_poly : Dom scale fun x : Input × ℕ => size (input x.1 x.2) := by
  have base := Dom.base scale
  have hspec : Dom scale (fun x => size (InterchangeROMExpose.template x.1)) := by
    apply ((Dom.const scale 5).mul (base.add (Dom.const scale 5))).mono
    intro x
    change (size (tally x.1.b)+size (tally x.1.n)+1)+x.1.req.header.count+1 ≤ _
    simp only [size_tally,tally_length]
    dsimp [scale]; omega
  obtain ⟨k,C,h⟩ := header_budget
  have center : Dom scale (fun x => size (centerHeader x.1)) :=
    ((Dom.const scale C).mul ((hspec.add (Dom.const scale 1)).pow k)).mono
      fun x => (Nat.le_add_left _ _).trans (h x.1)
  have parameters : Dom scale (fun x => (template x.2 x.1.b x.1.n).count) := by
    apply ((Dom.const scale 5).mul (base.add (Dom.const scale 5))).mono
    intro x
    change size (tally x.2,tally x.1.b,tally x.1.n) ≤ _
    simp only [size_prod,size_tally,tally_length]
    dsimp [scale]; omega
  exact (parameters.add center).add (Dom.const scale 1)

/-- Both the complete return value of the ruler generator and its running
time fit the native local mass. The exponent is common to all templates. -/
theorem ruler_cost : ∃ k C : ℕ, ∀ i W,
    let A := C*(W+i.b+i.n+1)^k*(localMass i.req k+1)
    size (out i W) ≤ A ∧ (template W i.b i.n).count+size (centerHeader i)+1 ≤ A ∧
    ∀ env, LocalFits env InterchangeROMBankRulers.command (send (input i W)) (send (out i W)) A := by
  obtain ⟨J,d,run⟩ := command_fits
  let h := input_poly.add (Dom.const scale 1)
  obtain ⟨k,C,poly⟩ := h.add (h.pow d)
  refine ⟨k,(J+1)*(C+2),?_⟩
  intro i W A
  let Q := (W+i.b+i.n+1)^k
  let H := (i.req.header.count+1)^k
  let V := localMass i.req k+1
  have enough : (scale (i,W)+1)^k ≤ Q*H := by
    rw [← Nat.mul_pow]
    apply Nat.pow_le_pow_left
    dsimp [scale,Q,H]
    rw [Nat.add_mul,Nat.mul_add,Nat.one_mul]
    omega
  have bound : (size (input i W)+1)+(size (input i W)+1)^d ≤ C*(Q*H) :=
    (poly (i,W)).trans (Nat.mul_le_mul_left _ enough)
  have Npos : 0 < i.req.rows.count :=
    (Nat.pow_pos (a:=2) (by decide)).trans_le (i.req.pow_digits_le i.radix i.valid)
  have Hpos : 1 ≤ H := Nat.one_le_pow _ _ (by omega)
  have Qpos : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have Hv : H ≤ V := by
    change H ≤ i.req.rows.count*(i.req.recordWidth+H)+1
    have h := Nat.le_mul_of_pos_left (i.req.recordWidth+H) Npos
    omega
  have Nv : i.req.rows.count+1 ≤ V :=
    Nat.succ_le_succ (Nat.le_mul_of_pos_right _ (by change 0 < i.req.recordWidth+H; omega))
  have qv : V ≤ Q*V := Nat.le_mul_of_pos_left _ Qpos
  have bnd := bound.trans (Nat.mul_le_mul_left C (Nat.mul_le_mul_left Q Hv))
  have ready : InterchangeROMBankRulers.work d i W+1 ≤ (C+2)*(Q*V) := by
    change i.req.rows.count+(size (input i W)+1)^d+1 ≤ (C+2)*(Q*V)
    rw [Nat.add_mul]; omega
  have mono := Nat.mul_le_mul_left (J+1) ready
  have eq : (J+1)*((C+2)*(Q*V)) = A := by dsimp only [A,Q,V]; ring
  rw [eq] at mono
  have time : J*(InterchangeROMBankRulers.work d i W+1) ≤ A :=
    (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans mono
  obtain ⟨_,_,proof⟩ := run i W [] (fun _ => []) 0 (by intro j; rfl)
  have finish := proof.finish 0
  simp only [Schoolbook.letters_pile_empty,Schoolbook.raw_zero,Tree.spell_length,Nat.zero_add] at finish
  have pay : (C+2)*(Q*V) ≤ A := eq ▸ Nat.le_mul_of_pos_left _ (Nat.succ_pos J)
  refine ⟨finish.trans time,?_,fun env deck base hd => (run i W env deck base hd).fits.mono time⟩
  change size (input i W) ≤ A
  exact ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans bnd)).trans <|
    ((Nat.mul_le_mul_right _ (show C ≤ C+2 by omega)).trans pay)

end InterchangeROMOuter.Wire

end NearSquareRoot
end Computability
end OAI
