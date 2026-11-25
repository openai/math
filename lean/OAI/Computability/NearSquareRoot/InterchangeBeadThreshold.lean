import OAI.Computability.IntegerMultiplication.Loom.Priority
import OAI.Computability.IntegerMultiplication.Staff.Nat
import Mathlib.Data.Nat.Log

/-!
# A computable padding width for rectangular interchange

The upper bound uses just the number of spectator and field digits. The
unary descriptor containing this bound can be computed from the outer
regime's header even when the packed records themselves have unknown width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Staff

private theorem told_length {I : Type} {r : Regime I} {P : I → Tape} (h : Told r P) :
    Realizes r (fun i => (P i).length) := by
  have t := h.shape.ez (Easy.ruler (X:=Tally) Easy.identity)
  simpa only [Realizes, box, Function.comp_def, ruler, shape, List.map_const', tally,
    List.length_map, id_eq] using t

private theorem realized_power {I : Type} {r : Regime I} {f : I → ℕ}
    (hf : Realizes r f) (k : ℕ) : Realizes r (fun i => f i ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (Realizes.fix (r:=r) 1)
  | succ k ih => simpa only [pow_succ] using ih.times hf

private theorem room_bounded (b : ℕ) (P : Tape) (hp : ∀ a ∈ P, a ≤ b) :
    room P ≤ b ^ P.length := by
  induction P with
  | nil => simp [room]
  | cons a P ih =>
    rw [room_cons,List.length_cons,pow_succ']
    exact Nat.mul_le_mul (hp a List.mem_cons_self) (ih fun j hj => hp j (List.mem_cons_of_mem _ hj))

/-- Produce a unary pad sufficient for the thickness exponent extracted from
the radix program. Its length is polynomial in the regime scale. -/
theorem bead_threshold {I : Type} {r : Regime I} {b : ℕ}
    (P G B : I → Tape) (e : I → ℕ) (hP : Told r P) (hG : Told r G) (hB : Told r B)
    (he : r.Has (tally ∘ e)) (radices : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ b) (k : ℕ) :
    ∃ pad : I → ℕ, r.Has (tally ∘ pad) ∧ Dom r.scale pad ∧
      ∀ i, (Nat.log 2 (stock b (P i) (G i) (B i) (e i)).count + 1) ^ k ≤ pad i := by
  let digits (i : I) := (P i).length + e i + (G i).length + e i + (B i).length
  have hd : Realizes r digits := (((told_length hP).plus he).plus (told_length hG)).plus he
    |>.plus (told_length hB)
  let pad (i : I) := (b * digits i + 1) ^ k
  have visible : Realizes r pad := realized_power (((Realizes.fix b).times hd).plus (Realizes.fix 1)) k
  have sz := Regime.Small.extent visible
  refine ⟨pad,visible,sz.mono ?_,fun i => ?_⟩
  · intro i
    change pad i ≤ size (tally (pad i))
    rw [size_tally,tally_length]
    omega
  · have hp := room_bounded b (P i) (fun d hd => radices i d (by simp [hd]))
    have hg := room_bounded b (G i) (fun d hd => radices i d (by simp [hd]))
    have hb := room_bounded b (B i) (fun d hd => radices i d (by simp [hd]))
    have count : (stock b (P i) (G i) (B i) (e i)).count ≤ b ^ digits i := by
      change ((layout (P i)).cart ((line b (e i)).cart ((layout (G i)).cart
        ((line b (e i)).cart (layout (B i)))))).count ≤
          b ^ ((P i).length + e i + (G i).length + e i + (B i).length)
      have hf : room (field b (e i)) = b ^ e i := by
        rw [← Dims.population, ← Adic.count (p:=b) (l:=e i)]
      simp only [Series.count_cart, space, hf, pow_add]
      simpa only [mul_assoc] using Nat.mul_le_mul hp
        (Nat.mul_le_mul_left (b ^ e i) (Nat.mul_le_mul hg (Nat.mul_le_mul_left (b ^ e i) hb)))
    have exp : (stock b (P i) (G i) (B i) (e i)).count ≤ 2 ^ (b * digits i) := by
      rw [pow_mul]
      exact count.trans (Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _)
    have logBound := Nat.log_mono_right (b:=2) exp
    rw [Nat.log_pow (by decide)] at logBound
    exact Nat.pow_le_pow_left (Nat.succ_le_succ logBound) _

end InterchangePayload

end NearSquareRoot
end Computability
end OAI
