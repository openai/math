import OAI.Computability.BorderVNP.PackedStableOffsets

/-! # Sorting geometry word rows by current cell and stable word ordinal

The forward sort carries each whole word to the appropriate cell section. The second
sort returns the sorted position to its original row. Start and end marker rows thus
expose their true addresses in the output without a search by the receiving team.
Both passes use the shared Batcher circuit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchLookup ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open private first source code source_word code_rank source_size from OAI.Computability.BorderVNP.PackedStableOffsets
open private restore from OAI.Computability.BorderVNP.PackedHistogram

/-- One sorted payload array followed by the original-order array of position words. -/
abbrev Bank (b : ℕ) := Fin (2^b) ⊕ Fin (2^b)

private noncomputable def position (w : ℕ) (i : ℕ) : Fin w → Bool :=
  (numberWords w).symm (Fin.ofNat (2^w) i)

private def stampBits {b k w : ℕ} (i : Fin (2^b)) (pos : Fin w → Bool) :
    Fin (w+b) → Expr (Expanded b k w) :=
  prepend (fun j => .input (i,ordinalPin k w j)) (fun j => .const (pos j))

private noncomputable def stamped (b k w : ℕ) : Frame (Expanded b k w) (Pins b (w+b)) :=
  (Frame.initial id).step fun ij => stampBits ij.1 (position w ij.1.val) ij.2

private theorem stamp_eval {b k w : ℕ} (x : Expanded b k w → Bool) (i : Fin (2^b)) (j : Fin (w+b)) :
    (stamped b k w).eval x (i,j) = prepend (fun l => x (i,ordinalPin k w l)) (position w i.val) j := by
  simp only [stamped,Frame.step_eval,stampBits]
  rw [show (Frame.initial (id : Expanded b k w → _)).eval x = x from funext fun v => Frame.initial_eval id x v]
  exact congrFun (prepend_map (fun e : Expr (Expanded b k w) => e.eval x)
    (fun l => .input (i,ordinalPin k w l)) (fun l => .const (position w i.val l))) j

private noncomputable def inverse (b k w : ℕ) : Frame (Expanded b k w) (Pins b w) :=
  (phases b le_rfl (stamped b k w)).select fun ij => (ij.1,lowPin b ij.2)

/-- All payloads in ascending cell/ordinal order and all returned addresses share
a single execution of the first sort. -/
noncomputable def sortedFrame (b k w : ℕ) : Frame (Stable.Input b k w) (Bank b × Fin w) :=
  (((inverse b k w).withInput.select (fun p : Bank b × Fin w =>
    p.1.elim (fun i => .inl (i,weightPin k b p.2)) (fun i => .inr (i,p.2)))).subst (first b k w))

/-- The total overhead is linear in the number of physical words up to logarithmic
factors for the word widths and sorting depth. -/
theorem sortedFrame_size (b k w : ℕ) : (sortedFrame b k w).size ≤
    1 + 2^b * (((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + (w+b) + b^2*(24*(w+b)+1)) := by
  have hh (i : Fin (2^b)) (j : Fin (w+b)) : (stampBits (k := k) i (position w i.val) j).size ≤ 1 := by
    let f (e : Expr (Expanded b k w)) := e.size
    have h := congrFun (prepend_map f (fun t => .input (i,ordinalPin k w t))
      (fun t => .const (position w i.val t))) j
    have eq : prepend (fun _ : Fin b => 1) (fun _ : Fin w => 1) = (fun _ => 1) := by
      have he := prepend_map (fun _ : Unit => (1 : ℕ)) (fun _ : Fin b => ()) (fun _ : Fin w => ())
      exact he.symm
    exact (h.trans (congrFun eq j)).le
  have hs := Frame.step_size_le (Frame.initial (id : Expanded b k w → _))
    (fun ij : Pins b (w+b) => stampBits ij.1 (position w ij.1.val) ij.2) 1 (fun ij => hh ij.1 ij.2)
  change (stamped b k w).size ≤ _ at hs
  simp only [Frame.initial_size, Pins,Fintype.card_prod,Fintype.card_fin,mul_one,zero_add] at hs
  have h₁ := expanded_size b k w
  have h₂ := phases_size b le_rfl (expanded b k w)
  have h₃ := phases_size b le_rfl (stamped b k w)
  have h₄ := source_size b k w
  simp only [sortedFrame, Frame.select_size,Frame.withInput_size,Frame.subst_size,inverse,first]
  nlinarith only [hs,h₁,h₂,h₃,h₄]

/-- The same permutation describes the ordered payloads and the returned marker
addresses. Equal cell keys retain original ordinal order. -/
theorem sortedFrame_values {b k w : ℕ} (x : Stable.Input b k w → Bool) (fit : 2^b ≤ 2^w) :
    ∃ π : Equiv.Perm (Fin (2^b)),
      Monotone (fun u => 2*Stable.key x (π u)*2^b+(π u).val) ∧
      (∀ u, value (fun j => (sortedFrame b k w).eval x (.inl u,j)) = Stable.weight x (π u)) ∧
      ∀ u, value (fun j => (sortedFrame b k w).eval x (.inr u,j)) = (π.symm u).val := by
  let y := (source b k w).eval x
  let s := (first b k w).eval x
  obtain ⟨π,hπ⟩ := phases_order (expanded b k w) y
  have wire (u j) : s (u,j) = code x (π u) j := by
    rw [show s (u,j) = (phases b le_rfl (expanded b k w)).eval y (u,j) from Frame.subst_eval _ _ _ _,
      hπ,expanded_eval,source_word]
  refine ⟨π,?_,?_,?_⟩
  · intro i j hij
    have hn := Nat.div_le_div_right (c := 2^w) (phases_monotone (expanded b k w) y hij)
    simpa only [hπ,expanded_eval,y,source_word,code_rank] using hn
  · intro u
    unfold Stable.weight
    apply congrArg value
    funext j
    simp only [sortedFrame,Frame.subst_eval,Frame.select_eval,Sum.elim_inl]
    change (inverse b k w).withInput.eval s (.inl (u,weightPin k b j)) = _
    rw [Frame.withInput_eval_inl,wire]
    simp [code]
  · intro u
    have bits (l j) : (stamped b k w).eval s (l,j) =
        prepend ((numberWords b).symm (π l)) (position w l.val) j := by
      rw [stamp_eval]
      simp only [wire,code,record_ordinal]
    have get (j : Fin w) : (sortedFrame b k w).eval x (.inr u,j) = position w (π.symm u).val j := by
      simp only [sortedFrame,Frame.subst_eval,Frame.select_eval,Sum.elim_inr]
      change (inverse b k w).withInput.eval s (.inr (u,j)) = _
      rw [Frame.withInput_eval_inr,inverse,Frame.select_eval]
      exact restore _ s π (fun i => position w i.val) bits u j
    simp only [get,position,value_encode,Fin.val_ofNat,Nat.mod_eq_of_lt ((π.symm u).isLt.trans_le fit)]

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
