import OAI.ThreeFlat.Diagonal.TraceSortTerminal
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Row-independent final memory packet with a public successor bit -/

namespace ThreeFlat.Diagonal.TraceSortSite

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization TraceAdjacent TraceWords
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w : ℕ} {σ τ : Type*}

private def decodeWord (z : Fin w → Bool) : Word w := (wordBits w).symm z

private theorem decodeWord_bits (z : Fin w → Bool) (j : Fin w) : z j = bits (decodeWord z) j :=
  (congrFun ((wordBits w).apply_symm_apply z) j).symm.trans (Computability.VPVNP.LiveHeader.testBit_wordBits _ _).symm

private theorem pairExpr_congr {a b : SlotAddr w σ} {c d : SlotAddr w τ} {x : σ → Bool} {y : τ → Bool}
    (ha : ∀ f j, x (a f j) = y (c f j)) (hb : ∀ f j, x (b f j) = y (d f j)) :
    (pairExpr a b).eval x = (pairExpr c d).eval y := by
  let u := fun f => decodeWord (fun j => x (a f j))
  let v := fun f => decodeWord (fun j => x (b f j))
  have hu (f j) : x (a f j) = bits (u f) j := decodeWord_bits (fun j => x (a f j)) j
  have hv (f j) : x (b f j) = bits (v f) j := decodeWord_bits (fun j => x (b f j)) j
  have h₁ : Represents (addressed (slices a b)) x (slices u v) :=
    ⟨hv 5, hv 1, hv 6, hu 1, hu 6⟩
  have h₂ : Represents (addressed (slices c d)) y (slices u v) :=
    ⟨fun j => (hb 5 j).symm.trans (hv 5 j), fun j => (hb 1 j).symm.trans (hv 1 j),
     fun j => (hb 6 j).symm.trans (hv 6 j), fun j => (ha 1 j).symm.trans (hu 1 j),
     fun j => (ha 6 j).symm.trans (hu 6 j)⟩
  exact Bool.eq_iff_iff.mpr ((check_at _ x _ h₁).trans (check_at _ y _ h₂).symm)

private def finishInputExpr (previous outgoing : SlotAddr w σ) (hasNext : σ) :
    Expr (σ ⊕ Live w) :=
  (.input (.inr (.inr ())) : Expr _).and
    ((pairExpr (externalPins previous) (ownAddr 0)).and
      ((pairExpr (ownAddr 0) (ownAddr 1)).and
        ((.not (.input (.inl hasNext)) : Expr _).or (eqPort (externalPins outgoing) (ownAddr 1)))))

noncomputable def finishInput [Fintype σ] (frame : Frame σ (Live w))
    (previous outgoing : SlotAddr w σ) (hasNext : σ) : Frame σ Unit :=
  frame.withInput.step fun _ => finishInputExpr previous outgoing hasNext

/-- This identity holds even on arbitrary binary messages and arbitrary live
registers. Only the selected input bits and the accumulated prior verdict matter. -/
theorem finishInput_agrees [Fintype σ] [Fintype τ] (frame : Frame σ (Live w))
    (other : Frame τ (Live w)) (previous outgoing : SlotAddr w σ) (p' o' : SlotAddr w τ)
    (hasNext : σ) (last : Bool) (x : σ → Bool) (y : τ → Bool)
    (live : frame.eval x = other.eval y)
    (prev : ∀ f j, x (previous f j) = y (p' f j))
    (sent : ∀ f j, x (outgoing f j) = y (o' f j)) (atNext : x hasNext = last) :
    (finishInput frame previous outgoing hasNext).eval x () =
      (finish other p' o' last).eval y () := by
  let X := frame.withInput.eval x
  let Y := other.withInput.eval y
  have own (i : Fin 2) (f j) : X (ownAddr i f j) = Y (ownAddr i f j) := by
    simp [X,Y,ownAddr,live]
  have pext (f j) : X (externalPins previous f j) = Y (externalPins p' f j) := by
    simpa [X,Y,externalPins] using prev f j
  have oext (f j) : X (externalPins outgoing f j) = Y (externalPins o' f j) := by
    simpa [X,Y,externalPins] using sent f j
  have hp := pairExpr_congr pext (own 0)
  have hc := pairExpr_congr (own 0) (own 1)
  have ho := eqPort_congr oext (own 1)
  have hn : X (.inl hasNext) = last := by simpa [X] using atNext
  have hold : X (.inr (.inr ())) = Y (.inr (.inr ())) := by simp [X,Y,live]
  simp only [finishInput,finish,Frame.step_eval]
  change (finishInputExpr previous outgoing hasNext).eval X = (finishExpr p' o' last).eval Y
  cases last <;> simp [finishExpr,finishInputExpr,Expr.eval,hp,hc,ho,hold,hn]

theorem finishInput_size [Fintype σ] (frame : Frame σ (Live w)) (previous outgoing : SlotAddr w σ)
    (hasNext : σ) : (finishInput frame previous outgoing hasNext).size ≤ frame.size+188*(w+1) := by
  have h₀ := pairExpr_size (externalPins previous) (ownAddr 0)
  have h₁ := pairExpr_size (ownAddr (σ := σ) (w := w) 0) (ownAddr 1)
  have hs := eqPort_size (externalPins outgoing) (ownAddr 1)
  have hz : (finishInputExpr previous outgoing hasNext).size ≤ 188*(w+1) := by
    simp only [finishInputExpr,Expr.size]
    omega
  simpa [finishInput] using frame.withInput.step_size_le
    (fun _ : Unit => finishInputExpr previous outgoing hasNext) (188*(w+1)) (fun _ => hz)

end ThreeFlat.Diagonal.TraceSortSite

end OAI
