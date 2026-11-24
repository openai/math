import OAI.Computability.VPVNP.CompressorSelectedTermWorker
import OAI.Computability.VPVNP.CursorDescriptorWords

/-!
# Uniform word bounds for the canonical dense term-worker input

Demand rows begin at zero and the strided term rows begin at the end of
the demand array. Both shrink and refresh grids have template-fixed row
widths. Their storage, including the two header words and the independent
stride operands, is polynomially bounded in the original cursor length.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.CanonicalWorker

open BurstRAM CursorBounds Compression Filter SelectedTerms PairSimulation.LocalHistory
open scoped Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Every origin of every selected execution satisfying the current position
and maximum-width bounds has the exact dense addresses, private operand
width and input word range required by the canonical worker. -/
theorem eventually_fit (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ len : ℕ in atTop,
    ∀ {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
      {a g b' n' : ℕ} {X : State a g} {p : StatePass R X b' n'} (o : PassOrigin B f hf p),
      X.positions ≤ initialPositions b len → X.maxWireWidth ≤ len →
      let G := grid o
      let w := wordBits b len
      o.motifCount*(G.d+(2+G.e))+max G.d (2+G.e)+2 < 2^w ∧
        SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w ∧ X.maxWireWidth < 2^w := by
  let width (G : Grid k) := G.d+(2+G.e)
  let K := max (width (shrinkGrid B)) (width (refreshGrid B))
  have bounded := ((((CursorRAM.bounded_positions b).mul (PolynomiallyBounded.const (slotDegree S))).mul
    (PolynomiallyBounded.const K)).add (PolynomiallyBounded.const K)).add (PolynomiallyBounded.const 2)
  filter_upwards [CursorRAM.eventual_word_room b hb bounded,CursorRAM.eventual_word_room b hb PolynomiallyBounded.id,
    DemandPreparation.eventually_live_word_fits b hb (SelectedTermWorker.fitConstant B) 4 1 1]
    with len room input bits
  intro R _ f hf a g b' n' X p o positions maxWidth G w
  have degree : 2^a ≤ slotDegree S := by
    cases o with
    | shrink i _ _ => exact (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j)
        (Finset.mem_univ i.castSucc)).trans (le_max_right ..)
    | refresh => exact le_max_left ..
  have dim : G.d+(2+G.e) ≤ K := by
    change width (grid o) ≤ K
    cases o <;> first | exact le_max_left .. | exact le_max_right ..
  have motifs := o.motifCount_le.trans (Nat.mul_le_mul positions degree)
  have stride : max G.d (2+G.e) ≤ K := (max_le (Nat.le_add_right ..) (Nat.le_add_left ..)).trans dim
  have scratch := Nat.add_le_add (Nat.mul_le_mul motifs dim) stride
  exact ⟨(Nat.add_le_add_right scratch 2).trans_lt room,bits _ (by simpa using maxWidth),maxWidth.trans_lt input⟩

end CompressorRecords.CanonicalWorker

end

end VPVNP
end Computability
end OAI
