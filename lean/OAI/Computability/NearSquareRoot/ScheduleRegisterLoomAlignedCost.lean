import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAligned

/-! # Uniform linear costs of aligned record calls -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip Space

private def volumeFactor (f o C : ℕ) := f * (C + 3) + o * (C + 2) + C + 12

/-- Layout-dependent coefficient for an aligned call on a bank of bounded fields. -/
def alignedFactor (f o C : ℕ) : ℕ :=
  (3000 + 401 * (f + 1) + 250 * (o + 1) + 2 * o) * (volumeFactor f o C + 1)

private theorem stream_size {A : Type} (s : Series A) (v : A → Tree) (C W : ℕ)
    (hW : 1 ≤ W) (h : ∀ a, (v a).count ≤ C * W) :
    (stripe s v).count ≤ (C + 2) * (s.count * W + 1) := by
  apply (stripe_size s v _ h).trans
  have hm := Nat.mul_le_mul_left s.count hW
  simp only [Nat.mul_one] at hm
  nlinarith

private theorem bank_size {A : Type} (s : Series A) (v : A → Tree) (C W : ℕ)
    (hW : 1 ≤ W) (h : ∀ a, (v a).count ≤ C * W) :
    (stripe s v).count ≤ (s.count * (C + 1) + 1) * W := by
  apply (stripe_size s v _ h).trans
  have hm := Nat.mul_le_mul_left s.count hW
  simp only [Nat.mul_one] at hm
  nlinarith

private theorem sum_const {A : Type} (l : List A) (n : ℕ) : costSum (fun _ => n) l = l.length * n := by
  induction l with
  | nil => simp
  | cons a t ih => rw [costSum_cons, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem time_scaled (f o bank vin vout work X : ℕ) (h : 1 ≤ X)
    (hb : bank ≤ X) (hi : vin + 1 ≤ X) (ho : vout + 1 ≤ X) (hw : work ≤ X) :
    430 * bank + 12 + alignClock f o vin vout work ≤ (3000 + 401 * (f + 1) + 250 * (o + 1) + 2 * o) * X := by
  have hv : vout ≤ X := by omega
  have const (u : ℕ) : u ≤ u * X := Nat.le_mul_of_pos_right _ h
  calc
    _ ≤ 430 * X + 12 * X + (401 * (f + 1) * X + X + 100 * X +
          10 * X + 250 * (o + 1) * X + 4 * X) := by
      unfold alignClock
      gcongr
      all_goals first | assumption | apply const
    _ = (557 + 401 * (f + 1) + 250 * (o + 1)) * X := by ring
    _ ≤ _ := Nat.mul_le_mul_right X (by omega)

private theorem space_scaled (f o bank vin vout space X : ℕ) (h : 1 ≤ X)
    (hb : bank ≤ X) (hi : vin + 1 ≤ X) (ho : vout + 1 ≤ X) (hw : space ≤ X) :
    alignSpace space o vin vout + 432 * bank + 12 ≤ (3000 + 401 * (f + 1) + 250 * (o + 1) + 2 * o) * X := by
  have d := Nat.mul_le_mul_left (2 * o) h
  simp only [Nat.mul_one] at d
  simp only [alignSpace, Nat.add_mul]
  omega

/-- The clock and workspace both scale with total record volume. For an empty
stream, the bound is independent of the field width. -/
theorem aligned_linear {K L A : Type} [DecidableEq K] [DecidableEq L]
    (cols : Series K) (dst : Series L) (rows : Series A) (k : K)
    (v : A → K → Tree) (w : A → L → Tree) (op : Cmd) (C W : ℕ) (hW : 1 ≤ W)
    (hv : ∀ a j, (v a j).count ≤ C * W) (hw : ∀ a j, (w a j).count ≤ C * W)
    (hc : ∀ a env r base, DeckCap base r →
      BoundedFits env op (pile 0 (stripe cols (v a)) r) (pile 0 (stripe dst (w a)) r)
        (C * W) (base + C * W) (C * W))
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let D := alignedFactor cols.count dst.count C * (rows.count * W + 1)
    BoundedFits env (alignedCommand (cols.explore.idxOf k) dst op)
      (pile 0 (stripe cols (fun j => stripe rows (fun a => v a j))) r)
      (pile 0 (stripe dst (fun j => stripe rows (fun a => w a j))) r) D (base + D) D := by
  let V := rows.count * W + 1
  let B := volumeFactor cols.count dst.count C
  let X := (B + 1) * V
  let S := if rows.count = 0 then 0 else C * W
  let bank := stripe cols (fun j => stripe rows (fun a => v a j))
  let blank := stripe rows (fun _ => .atom false)
  let input := Tree.fork bank blank
  let output := stripe rows (stripe dst ∘ w)
  have child (a : A) (env r base) (h : DeckCap base r) := hc a env r base h
  have arg (a : A) : S = C * W := by
    have pos := List.length_pos_of_mem (rows.complete a)
    simp [S, Nat.ne_of_gt (show 0 < rows.count from pos)]
  have run := aligned_bounded cols dst rows k v w op (fun _ => C * W) S
    (fun a e d b hd => by simpa only [arg a] using child a e d b hd) env r base hr
  have hV : 1 ≤ V := by dsimp [V]; omega
  have cn := Nat.mul_le_mul_left rows.count hW
  simp only [Nat.mul_one] at cn
  have bankCap : bank.count ≤ (cols.count * (C + 3) + 1) * V :=
    bank_size _ _ (C + 2) V hV fun j => stream_size _ _ C W hW fun a => hv a j
  have blankCap := stripe_size rows (fun _ => .atom false) 1 (fun _ => le_refl 1)
  change blank.count ≤ rows.count * (1 + 1) + 1 at blankCap
  have pCap : input.count ≤ B * V := by
    have hb : cols.count * (C + 3) + 4 ≤ B := by dsimp [B,volumeFactor]; omega
    have hg := Nat.mul_le_mul_right V hb
    change bank.count + blank.count + 1 ≤ _
    rw [Nat.add_mul] at bankCap hg
    dsimp only [V] at bankCap hg ⊢
    omega
  have roCap : output.count ≤ B * V := by
    have hd := stream_size rows (stripe dst ∘ w) (dst.count * (C + 1) + 1) W hW
      (fun a => bank_size dst _ C W hW (hw a))
    apply hd.trans (Nat.mul_le_mul_right _ ?_)
    dsimp [B,volumeFactor]
    rw [show dst.count * (C + 2) = dst.count * (C + 1) + dst.count by ring]
    omega
  have sCap : S ≤ B * V := by
    by_cases h : rows.count = 0
    · simp [S,h]
    have hh := Nat.mul_le_mul_right W (show 1 ≤ rows.count by omega)
    simp only [Nat.one_mul] at hh
    have bC : C ≤ B := by dsimp [B, volumeFactor]; omega
    have hv' : W ≤ V := by dsimp [V]; omega
    simpa only [S, ite_eq_right h] using Nat.mul_le_mul bC hv'
  have tCap : costSum (fun _ : A => C * W) rows.explore ≤ B * V := by
    rw [sum_const]
    change rows.count * (C * W) ≤ _
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul (by dsimp [B,volumeFactor]; omega) (by dsimp [V]; omega)
  have x_pos : 1 ≤ X := Nat.mul_pos (by omega : 0 < B + 1) hV
  have bound1 : B * V + 1 ≤ X := by dsimp only [X]; rw [Nat.add_mul]; omega
  have bankX : bank.count ≤ X := by
    change bank.count + blank.count + 1 ≤ _ at pCap
    omega
  have ipX : input.count + 1 ≤ X := by omega
  have opX : output.count + 1 ≤ X := by omega
  have tX : costSum (fun _ : A => C * W) rows.explore ≤ X := by omega
  have sX : S ≤ X := by omega
  have tim := time_scaled cols.count dst.count bank.count input.count output.count _ X x_pos bankX ipX opX tX
  have sp := space_scaled cols.count dst.count bank.count input.count output.count _ X x_pos bankX ipX opX sX
  have scale : alignedFactor cols.count dst.count C * V =
      (3000 + 401 * (cols.count + 1) + 250 * (dst.count + 1) + 2 * dst.count) * X := Nat.mul_assoc ..
  rw [← scale] at tim sp
  exact run.mono tim (Nat.add_le_add_left sp base) sp

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
