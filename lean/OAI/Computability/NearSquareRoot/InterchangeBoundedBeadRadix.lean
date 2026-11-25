import OAI.Computability.NearSquareRoot.InterchangeBoundedBeadCore
import OAI.Computability.NearSquareRoot.InterchangeBeadThreshold
import OAI.Computability.NearSquareRoot.InterchangeBoundedBreeze
import OAI.Computability.NearSquareRoot.InterchangeRadixSpace

/-! # Joint time and space for prime-radix interchange on ordinary bead records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom IntegerMultiplication.Adic
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request

variable {I : Type} {α : ℝ}

def BoundedRadixBeads (b : ℕ) (r : Regime I) (α : ℝ) : Prop :=
  ∀ (P G B : I → Tape) (e : I → ℕ), (∀ i, 0 < e i) → r.Has (tally ∘ e) →
    Told r P → Told r G → Told r B → (∀ i d, d ∈ P i ++ G i ++ B i → d ≤ b) →
    ∀ (L : I → ℕ) {T : I → Type} (t : (i : I) → Series (T i)), (∀ i, (t i).count ≤ L i) →
    ∀ v : (i : I) → SpanKey (P i) (G i) (B i) (Block b (e i)) → T i → Bead,
      let s i := stock b (P i) (G i) (B i) (e i)
      BoundedBreeze (Spindle.modes (τ:=α) e) r (fun i => (s i).count) L (together r.header (cloth s t v))
        (cloth s t fun i => v i ∘ swapper _ _ _)

/-- The near-square-root time and the linear padded record mass hold for the
same physical command through padding, recursive interchange and unpadding. -/
theorem exists_bounded_radix_beads (hα : 1/2 < α) (threshold : ℕ) :
    ∃ b : ℕ, b.Prime ∧ threshold < b ∧ ∀ {I : Type} (r : Regime I), BoundedRadixBeads b r α := by
  obtain ⟨p,b,prime,_,base,large,solver⟩ := exists_bounded_radix_interchange hα threshold
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨k,run⟩ := solver (beadDigit (F:=ZMod p)) beadDigit_injective
  refine ⟨b,base,large,?_⟩
  intro I r P G B e pos he hp hg hb hbound L T u fit v
  obtain ⟨pad,header,dom,thick⟩ := bead_threshold P G B e hp hg hb he hbound k
  obtain ⟨q,hvol,hw,arrange,read,finish⟩ := bead_parts (F:=ZMod p) base.two_le k P G B e pos he
    hp hg hb hbound L u fit v pad header thick
  let N i := (stock b (P i) (G i) (B i) (e i)).count
  have hα' : 0 ≤ α := by linarith
  have rate := Spindle.belly e hα'
  have recursive := run.on q
  simp_rw [hvol,hw,Nat.cast_mul] at recursive
  have c := bounded_padded_fare N L (fun i => (u i).count) pad e fit dom α hα' _ _ recursive
  have center : BoundedBreeze (Spindle.modes e (τ:=α)) r N L
      (fun i => (job b).issue (q i).val) (fun i => (job b).reply (q i).val) := ⟨rate,c⟩
  exact ((BoundedBreeze.ofRip read rate).pair ((BoundedBreeze.ofRip arrange rate).chain center)).chain
    (BoundedBreeze.ofRip finish rate)

end InterchangePayload

end NearSquareRoot
end Computability
end OAI
