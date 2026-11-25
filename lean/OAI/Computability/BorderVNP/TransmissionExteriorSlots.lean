import OAI.Computability.BorderVNP.DiagonalLayout
import OAI.Computability.BorderVNP.TransmissionExteriorInput
import OAI.Computability.VPVNP.RAMTapeSuccessorFields

/-! # Exterior link arrays in the signed diagonal input layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.Layout

open VPVNP BurstRAM

variable {R r link d : ℕ} {Edge : Type}

/-- Exterior input strings of one processor, obtained from the common assignment
to the unordered direct links in the signed contraction. -/
def exteriorRows (u : Fin (R + 1)) (j : Fin r) (links : Wire R r link Edge → Bool) :
    List (List Bool) :=
  List.ofFn fun k : Fin R => List.ofFn fun b : Fin link =>
    links (.inr (blockOf u (u.succAbove k) (u.ne_succAbove k), j, b))

/-- The local team is omitted from the partner list. -/
theorem exteriorRows_count (u : Fin (R + 1)) (j : Fin r) (links : Wire R r link Edge → Bool) :
    (exteriorRows u j links).length = R := by simp [exteriorRows]

/-- Every partner contributes a link-width string, even for empty link widths. -/
theorem exteriorRows_width (u : Fin (R + 1)) (j : Fin r) (links : Wire R r link Edge → Bool)
    (bs : List Bool) (h : bs ∈ exteriorRows u j links) : bs.length = link := by
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp h
  simp

/-- Concatenating the exterior strings gives exactly the exterior part of
the evaluated symbolic input tape, in its original order. -/
theorem flatten_exteriorRows (u : Fin (R + 1)) (j : Fin r) (links : Wire R r link Edge → Bool)
    (pins : Fin d → Bool) :
    (exteriorRows u j links).flatten =
      (List.ofFn fun off : Fin (R * link) => (exteriorSlot u j off).read pins links) := by
  rw [RAMTape.SuccessorFields.raw_eq_flatten]
  simp only [exteriorRows, exteriorSlot, Equiv.symm_apply_apply, InputSlot.read]

/-- Position of a partner among the teams other than the caller. -/
def partnerRank (u v : Fin (R + 1)) (hd : u ≠ v) : Fin R :=
  ⟨if v.val < u.val then v.val else v.val - 1, by
    have hv := v.isLt
    have hu := u.isLt
    have hn : u.val ≠ v.val := fun h => hd (Fin.ext h)
    split <;> omega⟩

/-- The public skipped-rank formula is the inverse of the input layout's team omission. -/
theorem succAbove_partnerRank (u v : Fin (R + 1)) (hd : u ≠ v) :
    u.succAbove (partnerRank u v hd) = v := by
  have hn : u.val ≠ v.val := fun h => hd (Fin.ext h)
  by_cases hv : v.val < u.val
  · have hs : (partnerRank u v hd).castSucc < u := by
      simpa only [Fin.lt_def, Fin.val_castSucc, partnerRank, ite_eq_left hv] using hv
    rw [Fin.succAbove_of_castSucc_lt _ _ hs]
    exact Fin.ext (by simp [partnerRank, hv])
  · have hs : u ≤ (partnerRank u v hd).castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, partnerRank, ite_eq_right hv]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hs]
    apply Fin.ext
    simp only [Fin.val_succ, partnerRank, ite_eq_right hv]
    omega

/-- An exterior read at the skipped partner rank gives the word for precisely
the wire shared by both endpoints of that physical link. -/
theorem exteriorRows_word (w : ℕ) (u v : Fin (R + 1)) (hd : u ≠ v) (j : Fin r)
    (b : Fin link) (links : Wire R r link Edge → Bool) :
    TeamTapeInputEmit.headerWord w ((exteriorRows u j links)[(partnerRank u v hd).val]?.getD []) b =
      TeamTapeInputEmit.word w (links (.inr (blockOf u v hd, j, b))).toNat := by
  have hr : (partnerRank u v hd).val < (exteriorRows u j links).length :=
    by rw [exteriorRows_count]; exact (partnerRank u v hd).isLt
  rw [List.getElem?_eq_getElem hr]
  simp only [exteriorRows, Option.getD_some, List.getElem_ofFn, Fin.eta, TeamTapeInputEmit.headerWord]
  simp [b.isLt, succAbove_partnerRank u v hd]

end Diagonal.Layout

end BorderVNP
end Computability
end OAI
