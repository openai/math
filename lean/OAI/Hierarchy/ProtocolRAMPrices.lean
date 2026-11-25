import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProbePotential

namespace OAI
/-! # Advised quotes from exact integer stock and the box maximizer -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

noncomputable section

/-- The price table is independent of the selector. The physical input to a row is
the exact integer bit stock, measured in units of the payload width at this phase. -/
structure PhasePrice where
  a : ℝ
  M : ℝ
  time : ℝ
  bonus : ℕ → ℝ
  cap : ℕ → ℝ
  bits : ℕ
  precision : ℕ

def PhasePrice.quote (s : PhasePrice) (kind bits : ℕ) : ℝ :=
  AdaptiveProbe.offer s.a (s.bonus kind) s.M s.time ((bits:ℝ)/s.bits) (s.cap kind)

def PhasePrice.word (s : PhasePrice) (kind bits : ℕ) : ℕ :=
  ⌊(s.precision:ℝ)*s.quote kind bits⌋₊

theorem PhasePrice.approx (s : PhasePrice) (kind bits : ℕ) (a : 0<s.a) (bonus : 0≤ s.bonus kind)
    (M : 0≤ s.M) (time : 0<s.time) (cap : 0≤ s.cap kind) (precision : 0<s.precision) :
    let p := (s.word kind bits:ℝ)/s.precision
    p ≤ s.quote kind bits ∧ s.quote kind bits - p < 1/(s.precision:ℝ) := by
  have hp : (0:ℝ)<s.precision := Nat.cast_pos.mpr precision
  have stock : (0:ℝ) ≤ (bits:ℝ)/s.bits := by positivity
  have pos : 0 ≤ s.quote kind bits := (AdaptiveProbe.offer_spec a bonus M time stock cap).1.1
  have low : (s.word kind bits : ℝ) ≤ s.precision*s.quote kind bits :=
    Nat.floor_le (mul_nonneg hp.le pos)
  have high : (s.precision:ℝ)*s.quote kind bits < (s.word kind bits:ℝ)+1 :=
    Nat.lt_floor_add_one _
  dsimp
  constructor
  · apply (div_le_iff₀ hp).mpr
    linarith
  · rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ hp]
    linarith

/-- Canonical row-major advice. Every coordinate of a given kind shares this table. -/
def PhasePrice.advice {w : ℕ} (s : PhasePrice) (prices : Bank) (kinds stride : ℕ)
    (m : Memory w) : Memory w :=
  fillSegment prices.base (kinds*stride) (fun a =>
    let j := a-prices.base
    (s.word (j/stride) (j%stride) : Word w)) m

theorem PhasePrice.read_advice {w : ℕ} (s : PhasePrice) (prices : Bank) (kinds stride kind bits : ℕ)
    (m : Memory w) (hk : kind<kinds) (hb : bits<stride) (room : kinds*stride < 2^w)
    (cap : kinds*stride ≤ prices.size) :
    prices.read (s.advice prices kinds stride m) ((kind*stride+bits : ℕ) : Word w) =
      (s.word kind bits : Word w) := by
  have next : (kind+1)*stride ≤ kinds*stride := Nat.mul_le_mul_right _ hk
  have index : kind*stride+bits < kinds*stride := by rw [Nat.succ_mul] at next; omega
  have inside : prices.base ≤ prices.base+(kind*stride+bits) ∧
      prices.base+(kind*stride+bits)<prices.base+kinds*stride := by omega
  have sp : 0<stride := by omega
  have quo : (kind*stride+bits)/stride=kind := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ sp,Nat.div_eq_of_lt hb,Nat.zero_add]
  have rem : (kind*stride+bits)%stride=bits := Nat.mul_add_mod_of_lt hb
  simp only [Bank.read,Fin.val_cast_of_lt (index.trans room),Nat.mod_eq_of_lt (index.trans_le cap),
    advice,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left,quo,rem]

/-- One native lookup at a dynamically addressed commodity returns exactly the rounded
coordinate maximizer. The caller can install additional advice in disjoint banks. -/
theorem PhasePrice.priceLookup_word {w : ℕ} (s : PhasePrice) (prices stock : Bank)
    (kind stride bits : ℕ) (coordinate : Expr) (m : Memory w) (r : Word w)
    (stockRead : stock.read m (coordinate.eval m r) = (bits : Word w))
    (rom : prices.read m ((kind*stride+bits:ℕ):Word w) = (s.word kind bits : Word w)) :
    (priceLookup prices stock kind stride coordinate).eval m r = (s.word kind bits : Word w) := by
  simpa [priceLookup,Expr.eval,RowOp.opcode,BinaryOp.eval,stockRead,Nat.cast_add] using rom


end
end Hierarchy.ProtocolRAM

end OAI
