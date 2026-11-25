import OAI.ThreeFlat.Diagonal.MotifDemandPadding
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking
import OAI.ThreeFlat.Diagonal.MotifPayload

namespace OAI
/-! # Finite base tiles and common scale

Base blocks obtained from separate asymptotic restrictions may have different
multiplicities. Repeating each block a fixed number of times puts the whole
finite grid at one scale without increasing the selector fraction or the
normalized supply radius.
-/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks MotifDemandPadding MotifOuterTerms
open scoped Classical BigOperators

structure FixedMotifTile {J E S : Type} [Fintype J] [Fintype E] [Fintype S] (D : PortGraph J E)
    (P : PortGraph J S) (width : E → ℕ) (F : Type*) [CommSemiring F] where
  Alphabet : Type
  [finiteAlphabet : Fintype Alphabet]
  bits : ℕ
  encode : Alphabet ↪ Fin (2^bits)
  output : Alphabet → S → ℕ
  entry : ∀ t j, D.State (fun e => Fin (2^width e)) j → P.State (fun e => Fin (2^output t e)) j → F
  identity : ∀ x, D.wiring (fun e => Fin (2^width e)) x = ∑ t, P.contraction (A := fun e => Fin (2^output t e)) (fun j => entry t j (x j))

attribute [instance] FixedMotifTile.finiteAlphabet

namespace FixedMotifTile

variable {J E S F : Type} [Fintype J] [Fintype E] [Fintype S] [CommSemiring F]
variable {D : PortGraph J E} {P : PortGraph J S} {width : E → ℕ}

private def combine (T : FixedMotifTile D P width F) {r : ℕ} (s : Fin r → T.Alphabet) :
    (∀ i e, Fin (2^T.output (s i) e)) ≃ (∀ e, Fin (2^totalWidth T.output s e)) :=
  (Equiv.piComm _).trans (Equiv.piCongrRight fun e => MotifBinaryPacking.pack (fun i => T.output (s i) e))

/-- Repeat all finite numerical tables of a base tile at a new integer
scale. This is done once for each grid element, independently of all later
trace sizes and all input width profiles. -/
noncomputable def atScale (T : FixedMotifTile D P width F) (r : ℕ) :
    FixedMotifTile D P (fun e => width e * r) F where
  Alphabet := Fin r → T.Alphabet
  bits := r*T.bits
  encode := ((sequenceCode T.encode r).trans (MotifBinaryPacking.pack (fun _ : Fin r => T.bits)).toEmbedding).trans
    (finCongr (congrArg (2 ^ ·) (by simp : (∑ _ : Fin r, T.bits) = r*T.bits))).toEmbedding
  output := totalWidth T.output
  entry s j x y := ∏ i, T.entry (s i) j
    (readSlice D (fun e => digits (width e*r) (width e) r le_rfl) i j x)
    (fun p => (MotifBinaryPacking.pack (fun i => T.output (s i) p.1.1)).symm (y p) i)
  identity x := by
    rw [tiled_words D P (fun e => width e*r) width (fun _ => le_rfl)
      (fun t e => Fin (2^T.output t e)) T.entry T.identity x]
    apply Finset.sum_congr rfl
    intro s _
    unfold PortGraph.contraction
    rw [← (combine T s).sum_comp]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i _
    apply congrArg (T.entry (s i) j _)
    funext e
    exact (congrFun ((MotifBinaryPacking.pack (fun a => T.output (s a) e.1.1)).symm_apply_apply (fun a => z a e.1.1)) i).symm

theorem repeat_output_norm (T : FixedMotifTile D P width F) (r : ℕ) (q : S → ℝ) (hq : ∀ i, 0<q i) {R : ℝ}
    (norm : ∀ s, Computability.VPVNP.MotifGrid.widthNorm q (fun e => (T.output s e : ℝ)) ≤ R)
    (s : Fin r → T.Alphabet) :
    Computability.VPVNP.MotifGrid.widthNorm q (fun e => (((T.atScale r).output s e : ℕ):ℝ)) ≤ r*R := by
  change Computability.VPVNP.MotifGrid.widthNorm q (fun e => ((∑ i, T.output (s i) e : ℕ):ℝ)) ≤ _
  simp_rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i, Computability.VPVNP.MotifGrid.widthNorm q (fun e => (T.output (s i) e : ℝ)) := Computability.VPVNP.MotifWidths.widthNorm_sum_le q hq _
    _ ≤ ∑ _ : Fin r, R := Finset.sum_le_sum fun i _ => norm (s i)
    _ = _ := by simp

end FixedMotifTile
end ThreeFlat.Diagonal

end OAI
