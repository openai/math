import OAI.Computability.VPVNP.PairSimulationMapStream
import OAI.Computability.VPVNP.CompressorRecordsCursorCapacity

/-!
# Word capacity for the motif's private field reads

On any decoded selector sequence, all its running payload offsets are
bounded by its length times the largest width in the fixed table. This bound
also covers sequences whose totals disagree with the descriptor. Demand
padding and selector offsets likewise remain addressable on the live RAM.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapStream

open CursorBounds BurstRAM Filter MotifBlocks MotifConversion MotifSelector MotifGrid

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- All fixed table words fit, and every field-read start and end below the
indicated private workspace prefix fit without modular wraparound. Each
incident payload limit may be an arbitrary word width up to the branch cap. -/
theorem eventually_polynomial_field_addresses (bexp : ℕ) (hb : 1 ≤ bexp)
    (bound : ℕ → ℕ) (hbound : PolynomiallyBounded bound) :
    ∀ᶠ n : ℕ in atTop,
      let w := CursorBounds.wordBits bexp n
      B.selectorBits ≤ w ∧ (∀ z e, baseDemand B z e ≤ w) ∧ (∀ s e, basePayload B s e ≤ w) ∧
      ∀ u ≤ n, ∀ z (θ : Fin u → Selector B) (i : Fin u) (base : ℕ), base ≤ bound n →
        (∀ e, base + baseDemand B z e * i.val + baseDemand B z e < 2 ^ w) ∧
        (∀ e, base + MotifEntry.offset (fun l ↦ basePayload B (θ l) e) i +
          basePayload B (θ i) e < 2 ^ w) ∧
        (∀ e, totalWidth (basePayload B) θ e < 2 ^ w) ∧
        ∀ v ≤ n, base + v + B.selectorBits * i.val + B.selectorBits < 2 ^ w := by
  let A := ∑ z : B.grid.demands, ∑ e, baseDemand B z e
  let W := ∑ s : Selector B, ∑ e, basePayload B s e
  let C := max B.selectorBits (max A W)
  have hsel : B.selectorBits ≤ C := le_max_left ..
  have hd (z) (e) : baseDemand B z e ≤ C :=
    ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (baseDemand B z j)) (Finset.mem_univ e)).trans
      (Finset.single_le_sum (fun z _ ↦ Nat.zero_le (∑ j, baseDemand B z j))
        (Finset.mem_univ z))).trans ((le_max_left A W).trans (le_max_right ..))
  have hs (s) (e) : basePayload B s e ≤ C :=
    ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (basePayload B s j)) (Finset.mem_univ e)).trans
      (Finset.single_le_sum (fun s _ ↦ Nat.zero_le (∑ j, basePayload B s j))
        (Finset.mem_univ s))).trans ((le_max_right A W).trans (le_max_right ..))
  have room := CompressorRecords.CursorRAM.eventual_word_room bexp hb
    ((hbound.add PolynomiallyBounded.id).add
      (PolynomiallyBounded.id.mul (PolynomiallyBounded.const C)))
  filter_upwards [room, eventually_ge_atTop (2 ^ C)] with n hmod hn
  let w := CursorBounds.wordBits bexp n
  have hlog : C ≤ n.log2 :=
    (Nat.le_log2 (by have := Nat.two_pow_pos C; omega : n ≠ 0)).mpr hn
  have hc : C ≤ w :=
    (hlog.trans (log2_le_addressWidth hb n)).trans
      ((Nat.le_add_right (addressWidth bexp n) 10).trans (Nat.le_self_pow (by decide : 4 ≠ 0) _))
  refine ⟨hsel.trans hc, fun z e ↦ (hd z e).trans hc, fun s e ↦ (hs s e).trans hc, ?_⟩
  intro u hu z θ i base hbase
  change bound n + n + n * C < 2 ^ w at hmod
  dsimp only [w] at hmod
  have hi : i.val + 1 ≤ n := i.isLt.trans_le hu
  have hcend (v : ℕ) (hv : v ≤ C) :
      v * i.val + v ≤ n * C := by
    rw [← Nat.mul_succ, Nat.mul_comm]
    exact Nat.mul_le_mul hi hv
  refine ⟨fun e ↦ ?_, fun e ↦ ?_, fun e ↦ ?_, fun v hv ↦ ?_⟩
  · have := hcend _ (hd z e)
    omega
  · have h := offset_le (basePayload B) hs θ e i
    have he : i.val * C + C ≤ n * C := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right C hi
    have := hs (θ i) e
    omega
  · have h := (totalWidth_le (basePayload B) hs θ e).trans (Nat.mul_le_mul_right C hu)
    omega
  · have := hcend _ hsel
    omega

/-- Specialize the address bound to a packed local field workspace. -/
theorem eventually_field_addresses (bexp : ℕ) (hb : 1 ≤ bexp) :
    ∀ᶠ n : ℕ in atTop,
      let w := CursorBounds.wordBits bexp n
      B.selectorBits ≤ w ∧ (∀ z e, baseDemand B z e ≤ w) ∧ (∀ s e, basePayload B s e ≤ w) ∧
      ∀ u ≤ n, ∀ z (θ : Fin u → Selector B) (i : Fin u) (base : ℕ), base ≤ n ^ 5 →
        (∀ e, base + baseDemand B z e * i.val + baseDemand B z e < 2 ^ w) ∧
        (∀ e, base + MotifEntry.offset (fun l ↦ basePayload B (θ l) e) i +
          basePayload B (θ i) e < 2 ^ w) ∧
        (∀ e, totalWidth (basePayload B) θ e < 2 ^ w) ∧
        ∀ v ≤ n, base + v + B.selectorBits * i.val + B.selectorBits < 2 ^ w :=
  eventually_polynomial_field_addresses B bexp hb (fun n ↦ n ^ 5) (PolynomiallyBounded.id.pow 5)

end PairSimulation.MapStream

end VPVNP
end Computability
end OAI
