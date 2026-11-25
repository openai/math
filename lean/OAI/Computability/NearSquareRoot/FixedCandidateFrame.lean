import OAI.Computability.NearSquareRoot.PrecisionDigitGridTask
import OAI.Computability.NearSquareRoot.PrecisionProductPass
import OAI.Computability.NearSquareRoot.BoundedProduct
import OAI.Computability.NearSquareRoot.BoundedProductRight
import OAI.Computability.NearSquareRoot.CRTControlledElementaryRun
import OAI.Computability.NearSquareRoot.UniformMultiplicationRelease
import OAI.Computability.NearSquareRoot.ProductCanonical

/-! # Data packets and resource accounting for a fixed multiplication candidate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code Bits DigitPacking FixedPoint Space

abbrev LargeInput (N : ℕ) := {i : MultiplicationInput // N ≤ i.width}

abbrev LargeTask (N : ℕ) (T : ℕ → ℕ) :=
  BoundedTask (fun i : LargeInput N => T i.val.width) (fun i => i.val.width)
    (fun i => send i.val.operands) (fun i => send (Lea.answer i.val.operands))

abbrev Array (n : ℕ) := Fin (capacity n) → Record (addressBits n)

def records {n : ℕ} (r : Array n) : List Dusk.Pair := List.ofFn (Dusk.mark ∘ r)

def framed {n : ℕ} (r : Array n) : Tree := send (tally n, records r)

theorem array_volume {n : ℕ} (hn : 2 ≤ n) : (capacity n+1)*(addressBits n+1) ≤ 192*n := by
  have hk : 1 ≤ addressBits n := by have := width_pos hn; have := width_le_twice_addressBits hn; omega
  have hN : 1 ≤ capacity n := Nat.two_pow_pos _
  calc
    _ ≤ (2*capacity n)*(2*addressBits n) := Nat.mul_le_mul (by omega) (by omega)
    _ = 4*(capacity n*addressBits n) := by ring
    _ ≤ _ := by have := (packed_volume hn).2; omega

theorem framed_size {n : ℕ} (hn : 2 ≤ n) (r : Array n) : (framed r).count ≤ 75000*(n+1) := by
  have h := ProductPass.streamSize (Dusk.mark ∘ r) (w := 384*addressBits n+23) (fun j =>
    (record_size _ _).le)
  change size (tally n, records r) ≤ _
  rw [size_prod, size_tally, tally_length]
  change size (List.ofFn (Dusk.mark ∘ r)) ≤ _ at h
  have hv := array_volume hn
  have hw : 384*addressBits n+23+1 ≤ 384*(addressBits n+1) := by omega
  have hb := Nat.mul_le_mul_left (capacity n+1) hw
  have he : (capacity n+1)*(384*(addressBits n+1)) = 384*((capacity n+1)*(addressBits n+1)) := by ring
  rw [he] at hb
  dsimp only [records, Prod.snd]
  omega

private theorem fromLinear {I : Type} {n : I → ℕ} {p q : I → Tree}
    (h : Carries (Brief.measure n) p q) : BoundedTask n n p q := by
  have h' : Carries (fun i => ((n i+1 : ℕ):ℝ)) p q := by simpa [Brief.measure] using h
  exact (Controlled.boundedOfCarries h').bound 2 2 (fun i => by omega) (fun i => by omega)

/-- Encode both actual words and preserve the unary operand length independently
on each stream. The header is copied once, before the two transform branches. -/
theorem prepare {I : Type} (p : I → Interface.Pair)
    (hw : ∀ i, (p i).2.length = (p i).1.length) (hn : ∀ i, 2 ≤ (p i).1.length)
    (hv : ∀ i, ValidShape (p i).1.length) :
    BoundedTask (fun i => (p i).1.length) (fun i => (p i).1.length) (send ∘ p)
      (fun i => send ((tally (p i).1.length,encodedBoxed (p i).1),
        (tally (p i).1.length,encodedBoxed (p i).2))) := by
  let n i := (p i).1.length
  have pair := encoded_pair_scan p hw hn hv
  have hsmall := pair.small
  have rulerOp : Easy (fun v : Interface.Pair => ruler v.1) := Easy.ruler Easy.fst
  have head := Carries.func (y := p) (Brief.here n) hsmall _ rulerOp
  have ruler_eq (w : Word) : ruler w = tally w.length := by simp [ruler,tally,List.map_const']
  have full := head.twice pair
  let duplicate (v : Tally × List Dusk.Pair × List Dusk.Pair) := ((v.1,v.2.1),(v.1,v.2.2))
  have cheap : Easy duplicate := by unfold duplicate; fun_prop
  have finish := Carries.func (y := fun i => (ruler (p i).1, encodedBoxed (p i).1, encodedBoxed (p i).2))
    (Brief.here n) full.out duplicate cheap
  apply fromLinear
  simpa only [duplicate, ruler_eq, Function.comp_def, n] using full.chain finish

/-- Compose two uniform commands while charging both clocks to one target
function and keeping one linear tape allowance. -/
theorem sequence {I : Type} {n t : I → ℕ} {a b c : I → Tree}
    (f : BoundedTask t n a b) (g : BoundedTask t n b c) : BoundedTask t n a c := by
  exact (f.compose g).bound 2 1 (fun i => by omega) (fun i => by simp)

theorem pairCalls {I : Type} {n t : I → ℕ} (hnt : ∀ i, n i ≤ t i) {a b c d : I → Tree}
    (f : BoundedTask t n a b) (g : BoundedTask t n c d)
    (room : ∀ i, (c i).count ≤ 75000*(n i+1) ∧ (b i).count ≤ 75000*(n i+1)) :
    BoundedTask t n (fun i => .fork (a i) (c i)) (fun i => .fork (b i) (d i)) := by
  have f' := (f.left c).bound (time' := t) (space' := n) 75001 75001
    (fun i => by have := (room i).1; have := hnt i; omega) (fun i => by have := (room i).1; omega)
  have g' := (g.right b).bound (time' := t) (space' := n) 75001 75001
    (fun i => by have := (room i).2; have := hnt i; omega) (fun i => by have := (room i).2; omega)
  exact sequence f' g'

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
