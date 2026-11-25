import OAI.Computability.BorderVNP.DiagonalResidueRAMPhysical
import OAI.Computability.BorderVNP.DiagonalResidueRAMStagedCount
import OAI.Computability.BorderVNP.RoutingISAAdviceProof

/-!
# Addressing actual literal and tally inputs of the native reader

The query operands may lie in three separated physical regions: the row
pin, the column pin, and the team's unsigned coordinate/gadget tallies.
Only polynomially many bit source addresses are stored. The literal advice
may be delivered strided, one bit per processor, before the native pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM RoutingISA ResidueEntryInput

variable {h pin tally w : ℕ} {J : Type*} [Fintype J]

/-- The actual shared source address of each query wire. The tally bank holds
parameter counts first and then numbered gadget counts. -/
noncomputable def sourceAddress (row col tallies : ℕ) : Board.Physical h pin tally J → ℕ
  | .inl (side,j) => (if side then col else row)+j.val
  | .inr (.inl i,j) => tallies+i.val*tally+j.val
  | .inr (.inr l,j) => tallies+(h+(Fintype.equivFin J l).val)*tally+j.val

/-- Every operand in the gather list reads its prescribed bit directly from
one of the two delivered pin fields or the contiguous native tally output. -/
theorem sourceAddress_value (m : Memory w) (row col tallies : ℕ)
    (r c : Fin ((h+2)*pin) → Bool) (μ : Fin h → ℕ) (δ : J → ℕ)
    (hr : ∀ j, m (row+j.val) = wordBit w (r j))
    (hc : ∀ j, m (col+j.val) = wordBit w (c j))
    (hm : ∀ (i : Fin h) (j : Fin tally), m (tallies+i.val*tally+j.val) = wordBit w ((μ i).testBit j.val))
    (hd : ∀ (l : J) (j : Fin tally),
      m (tallies+(h+(Fintype.equivFin J l).val)*tally+j.val) = wordBit w ((δ l).testBit j.val)) :
    ∀ i : Fin (Fintype.card (Board.Physical h pin tally J)),
      m (sourceAddress row col tallies ((Fintype.equivFin _).symm i)) =
        wordBit w (number (Board.physicalInput r c μ δ) i) := by
  intro i
  obtain ⟨a,rfl⟩ := (Fintype.equivFin (Board.Physical h pin tally J)).surjective i
  simp only [number,Function.comp_apply,Equiv.symm_apply_apply]
  rcases a with ⟨s,j⟩ | ⟨i | l,j⟩
  · cases s
    · exact hr j
    · exact hc j
  · exact hm i j
  · exact hd l j

private theorem bits_at (m : Memory w) (p : ℕ) (bs : List Bool)
    (h : ∀ i : Fin bs.length, (m (p+i.val)).val = (bs[i.val]).toNat) :
    DiagonalTallyBits.BitsAt m p bs := by
  induction bs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨h ⟨0,by simp⟩,ih (p+1) (fun i => by
      have h' := h ⟨i.val+1,by simp⟩
      simpa [Nat.add_assoc,Nat.add_comm 1] using h')⟩

/-- The packing contract follows from the actual chronological binary words
in the dense array, including at a word boundary. -/
theorem wordsAt_of_flat (m : Memory w) (p : ℕ) (xs : List (List Bool))
    (h : ∀ i : Fin xs.flatten.length, (m (p+i.val)).val = (xs.flatten[i.val]).toNat) :
    DiagonalTallyBits.WordsAt m p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨bits_at m p b ?_,ih (p+b.length) ?_⟩
    · intro i
      have hb := h ⟨i.val,by simp; omega⟩
      simpa [List.getElem_append_left i.isLt] using hb
    · intro i
      have hb := h ⟨b.length+i.val,by simp only [List.flatten_cons,List.length_append]; omega⟩
      simpa [Nat.add_assoc,List.getElem_append_right] using hb

/-- The literal-copy kernel's exact memory image supplies the native pack's
entire advised prefix. Extra bits beyond that prefix can carry the pin test. -/
theorem wordsAt_of_delivered (f : BroadcastFrame) (a : AdviceLayout)
    (original after : Memory w) (xs : List (List Bool)) (hlen : xs.flatten.length ≤ a.count)
    (image : readings after = a.copied f (readings original) a.count)
    (physical : ∀ i : Fin xs.flatten.length,
      (original (a.src f i.val)).val = (xs.flatten[i.val]).toNat) :
    DiagonalTallyBits.WordsAt after a.dst xs := by
  apply wordsAt_of_flat
  intro i
  exact (congrFun image (a.dst+i.val)).trans
    ((a.copied_at f (readings original) (i.isLt.trans_le hlen)).trans (physical i))

/-- The exact bit length of the advised payload at physical word width. -/
theorem payloadBits_length {u v k : ℕ} (base start : ℕ)
    (c : BooleanTranscript.Circuit (Fin u ⊕ Fin v) k) (src : Fin u → ℕ) :
    ((payload w base start c src).map BurstRAM.wordBits).flatten.length = (6+3*k+u)*w := by
  let data := payload w base start c src
  have all (xs : List (Word w)) : (xs.map BurstRAM.wordBits).flatten.length = xs.length*w := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [BurstRAM.wordBits,ih,Nat.add_mul,Nat.add_comm]
  exact (all data).trans (congrArg (·*w) (payload_length base start c src))

/-- Polynomial overhead for both staging and evaluation in the complete fixed
instruction table. -/
theorem staged_ticks_le {u v k w B : ℕ} (hu : u ≤ B) (hv : v ≤ B) (hk : k ≤ B) (hw : w ≤ B) :
    prepareTicks u k w + ticks k v ≤ 128*(B+1)^2 := by
  have hp := DiagonalTallyBits.ticks_le (6+3*k+u) w
  have scale := Nat.mul_le_mul (show 8*(6+3*k+u) ≤ 8*(6+4*B) by omega) (Nat.add_le_add_right hw 1)
  unfold prepareTicks ticks
  nlinarith

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
