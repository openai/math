import OAI.Computability.NearSquareRoot.InterchangeROMOuterHeaderGrowth
import OAI.Computability.NearSquareRoot.InterchangeROMOuterCost
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectFactor

/-! # Polynomial-width allowance for the grouped cubic bank

The clock of the emitted repair program may enlarge its *local accounting width* by
a fixed power of the grouped header size. Each transmitted child still uses the
parent's physical record width. Both volume formulas below retain the chosen degree.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code InterchangeAddress
  InterchangeROMExpose InterchangeROMRecursion InterchangeROMStageVolume

private theorem row_bound {b : ℕ} (q : Request b) (e : ℕ) (hdr : InterchangeROMAddress.Header)
    {N F : ℕ} (rows : N ≤ q.rows.count) (pos : 0 < q.rows.count)
    (growth : size hdr + 1 ≤ F*(q.header.count+1)) :
    Interchange.Template.Data.rowMass e hdr N q.recordWidth ≤
      (2*(F^e+2))*localMass q e := by
  let T := (q.header.count+1)^e
  have hT : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  have hp : (size hdr+1)^e ≤ F^e*T := by
    simpa only [Nat.mul_pow,T] using Nat.pow_le_pow_left growth e
  have width : q.recordWidth + 1 + (size hdr+1)^e ≤ (F^e+2)*(q.recordWidth+T) := by
    have h := Nat.mul_le_mul_left (F^e) (show T ≤ q.recordWidth+T by omega)
    rw [Nat.add_mul]
    omega
  have count : N+1 ≤ 2*q.rows.count := by omega
  calc
    _ ≤ (2*q.rows.count)*((F^e+2)*(q.recordWidth+T)) := Nat.mul_le_mul count width
    _ = _ := by dsimp [localMass,T]; ring

/-- The ordinary stage volume and enlarged repair volume are both bounded by
the same move clock. The positive degree pays the independent header term. -/
private theorem enlarged_le_row (e : ℕ) (he : 1 ≤ e)
    (hdr : InterchangeROMAddress.Header) (N w : ℕ) :
    mass (send hdr) N (w+(size hdr+1)^e) ≤ Interchange.Template.Data.rowMass e hdr N w := by
  have power : size hdr+1 ≤ (size hdr+1)^e := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < size hdr+1) he
  change size hdr+N*(w+(size hdr+1)^e+1)+1 ≤ (N+1)*(w+1+(size hdr+1)^e)
  rw [Nat.add_mul,Nat.one_mul,Nat.add_right_comm w ((size hdr+1)^e) 1]
  omega

/-- Fixed-degree price of the grouped geometry in units of parent local mass. -/
def groupedRate (b n e : ℕ) := 2*((overhead b n + 1)^e + 2)

theorem computable_groupedRate {P : Type} [Primcodable P] {b n e : P → ℕ}
    (hb : Computable b) (hn : Computable n) (he : Computable e) :
    Computable (fun p => groupedRate (b p) (n p) (e p)) := by
  have pow : Computable₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    (KernelComputableAddress.primrec_pow Primrec.fst Primrec.snd).to₂.to_comp
  exact Primrec.nat_mul.to_comp.comp (.const 2) (Primrec.nat_add.to_comp.comp
    (pow.comp (Primrec.succ.to_comp.comp (computable_overhead hb hn)) he) (.const 2))

theorem grouped_rowMass_le (i : Input) (W : ℕ) (hW : 3 ≤ W) (hw : W ≤ i.b) (e : ℕ) :
    Interchange.Template.Data.rowMass e (groupedHeader i W) (groupedRows i W).count i.req.recordWidth ≤
      groupedRate i.b i.n e * localMass i.req e := by
  have pos : 0 < i.req.rows.count := (Nat.pow_pos (by decide : 0 < 2)).trans_le
    (Request.pow_digits_le i.req i.radix i.valid)
  have rows := (grouped_counts i W hW hw).1
  have hdr := grouped_header_growth i W hW hw
  apply row_bound i.req e _ (by omega) pos
  rw [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
  omega

/-- Handles the exact accounting width returned by the repair theorem. The
physical row count is the live grouped row count and the exponent in the
target is the same `e` as in the opcode bound. -/
theorem grouped_enlarged_mass_le (i : Input) (W : ℕ) (hW : 3 ≤ W) (hw : W ≤ i.b)
    (e : ℕ) (he : 1 ≤ e) :
    let hdr := groupedHeader i W
    mass (send hdr) (groupedRows i W).count (i.req.recordWidth+(size hdr+1)^e) ≤
      groupedRate i.b i.n e * localMass i.req e :=
  (enlarged_le_row e he _ _ _).trans (grouped_rowMass_le i W hW hw e)

/-- The ordinary, uninflated volume obeys the same bound. -/
theorem grouped_mass_le (i : Input) (W : ℕ) (hW : 3 ≤ W) (hw : W ≤ i.b)
    (e : ℕ) (he : 1 ≤ e) :
    mass (send (groupedHeader i W)) (groupedRows i W).count i.req.recordWidth ≤
      groupedRate i.b i.n e * localMass i.req e :=
  (show mass _ _ _ ≤ mass _ _ (i.req.recordWidth+_) by unfold mass; gcongr; omega).trans
    (grouped_enlarged_mass_le i W hW hw e he)

/-- The emitted opcode coefficient can depend computably on the epoch. This
bound has exactly the form required by the native outer-body compiler. -/
theorem cubic_clock_le (i : Input) (W : ℕ) (hW : 3 ≤ W) (hw : W ≤ i.b)
    (e : ℕ) (he : 1 ≤ e) (K : ℕ) :
    let hdr := groupedHeader i W
    K * mass (send hdr) (groupedRows i W).count (i.req.recordWidth+(size hdr+1)^e) ≤
      (K*groupedRate i.b i.n e)*(localMass i.req e+1) := by
  refine (Nat.mul_le_mul_left K (grouped_enlarged_mass_le i W hW hw e he)).trans ?_
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.le_succ _)

theorem computable_cubic_rate {P : Type} [Primcodable P] {K b n e : P → ℕ}
    (hK : Computable K) (hb : Computable b) (hn : Computable n) (he : Computable e) :
    Computable (fun p => K p * groupedRate (b p) (n p) (e p)) :=
  Primrec.nat_mul.to_comp.comp hK (computable_groupedRate hb hn he)

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
