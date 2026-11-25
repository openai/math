import OAI.Computability.NearSquareRoot.InterchangeBoundedBeadRadix
import OAI.Computability.NearSquareRoot.InterchangeBoundedCharge
import OAI.Computability.NearSquareRoot.InterchangeBinaryBridge

/-! # Rectangular interchange with separate time and space bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom IntegerMultiplication.Adic
  NearSquareRoot.InterchangePayload

def BoundedRectInterchange {X : Type} (r : Regime X) (n : X → ℕ) (ρ : ℝ) : Prop :=
  ∀ (P G B : X → Tape), r.Has (tally ∘ n) → Told r P → Told r G → Told r B →
    (∀ i j, j ∈ P i ++ G i ++ B i → j ≤ Net.Shuttle.base) →
    ∀ (L : X → ℕ) {T : X → Type} (u : (i : X) → Series (T i)), (∀ i, (u i).count ≤ L i) →
    ∀ v : (i : X) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → T i → Bead,
      let s i := stock 2 (P i) (G i) (B i) (n i)
      BoundedBreeze (Spindle.modes n (τ := ρ)) r (fun i => (s i).count) L
        (together r.header (cloth s u v))
        (cloth s u fun i x => v i (swapper _ _ _ x))

/-- Grow both binary wings, interchange all padded rows over the selected
prime radix, and crop them. The halo overhead in space is at most a constant
times the binary row mass. -/
theorem nearRoot_bounded_rectInterchange {α : ℝ} (hα : 1/2 < α) {I : Type}
    (r : Regime I) (n : I → ℕ) : BoundedRectInterchange r n α := by
  obtain ⟨b,prime,large,native⟩ := exists_bounded_radix_beads hα Net.Shuttle.base
  let _ : NeZero b := ⟨prime.ne_zero⟩
  intro P G B hn hp hg hs guard L T t ht v
  let e i := InterchangeBinary.radixWidth prime.two_le (n i)
  let x i a := v i (InterchangeBinary.binaryRecord P G B n prime.two_le i a)
  have hpz : 0 ≤ α := by linarith
  have F := Spindle.belly n hpz
  have run := native r P G B e (fun i => InterchangeBinary.width_pos prime.two_le (n i))
    (InterchangeBinary.width_has prime.two_le n hn) hp hg hs
    (fun i d hd => (guard i d hd).trans large.le) L t ht x
  obtain ⟨K,price⟩ := InterchangeBinary.padded_price n hpz prime.two_le
  obtain ⟨pos,growth,pre,post⟩ := InterchangeBinary.halo_parts P G B n prime.two_le hn hp hg hs L
    (fun i a => strip (t i) (v i a)) (visible t v ht)
  have core := run.rescale F (b^2) K growth price
  have start := BoundedBreeze.ofRip ((Rip.split pre.again).1.twice pre) F
  have keep := BoundedBreeze.ofRip (Drive.fetch pos pre.idle) F
  exact (start.chain (keep.pair core)).chain (BoundedBreeze.ofRip (Rip.factor post pos (b^2) growth) F)

variable {I : Type} {r : Regime I} (P G B : I → Tape) (n : I → ℕ)
open IntegerMultiplication.Spindle
/-- A uniform-length binary record is sent exactly as its list of bits. The
physical bits agree with the bead codec even when the record width is zero. -/
theorem bounded_bitstrings {α : ℝ} (rect : BoundedRectInterchange r n α)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (guard : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ Net.Shuttle.base)
    (L width : I → ℕ) (bound : ∀ i, width i ≤ L i)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → List Bool)
    (exactWidth : ∀ i x, (v i x).length = width i) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    BoundedBreeze (modes n (τ:=α)) r (fun i => (s i).count) L
      (together r.header (stackRun s fun i x => send (v i x)))
      (stackRun s fun i x => send (v i (swapper _ _ _ x))) := by
  let t i := Series.natural (width i)
  let value i a := notify.symm ∘ (t i).untab (v i a) (by simp [t,exactWidth])
  have run := rect P G B hn hp hg hs guard L t (fun i => by simpa [t] using bound i) value
  have repr (i : I) (a) : strip (t i) (value i a) = send (v i a) := by
    have bits : (fun d => send (value i a d)) =
        fun d => send ((t i).untab (v i a) (by simp [t,exactWidth]) d) := by
      funext d
      change Tree.atom (notify (notify.symm _)) = Tree.atom _
      rw [Equiv.apply_symm_apply]
    rw [strip,bits,stripe_eq',Series.recover]
  unfold cloth at run
  simp_rw [repr] at run
  exact run


end Controlled

end NearSquareRoot
end Computability
end OAI
