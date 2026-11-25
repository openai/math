import OAI.ThreeFlat.Diagonal.CompressorOrderIndex
import OAI.ThreeFlat.Diagonal.CompressorNativeRank

namespace OAI
/-! # Native selection returns precisely the locally sorted slot -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Rank
open Computability.VPVNP.BurstRAM
open scoped Fin.NatCast
variable {w N : ℕ}

def eligible (xs : List (Word w)) : Finset (Word w) := xs.toFinset.erase 0

theorem eligible_below (xs : List (Word w)) (key : Word w) :
    below xs key = (eligible xs).filter (· < key) := by
  ext v
  simp [below,eligible,and_left_comm,and_comm]

theorem below_index (s : Finset (Word w)) (h : s.card = N) (i : Fin N) :
    (s.filter fun v => v < ((s.orderIsoOfFin h) i).val).card = i.val :=
  sorted_index s h i

theorem chosen_eq (all : List (Word w)) (key out : Word w) (xs : List (Word w))
    (found : out ∈ xs) (good : out ≠ 0 ∧ ((below all out).card : Word w) = key)
    (unique : ∀ z ∈ xs, z ≠ 0 → ((below all z).card : Word w) = key → z=out) :
    chosen all key xs = out := by
  induction xs with
  | nil => simp at found
  | cons z xs ih =>
    by_cases h : z ≠ 0 ∧ ((below all z).card : Word w) = key
    · exact (ite_eq_left h).trans (unique z (by simp) h.1 h.2)
    · rw [chosen,ite_eq_right h]
      apply ih ((List.mem_cons.mp found).resolve_left (fun eq => h (eq ▸ good)))
      exact fun a ha => unique a (List.mem_cons_of_mem _ ha)

theorem chosen_index (xs : List (Word w)) (hc : (eligible xs).card = N) (fits : N ≤ 2^w)
    (i : Fin N) : chosen xs (i.val : Word w) xs = (((eligible xs).orderIsoOfFin hc) i).val := by
  let e := (eligible xs).orderIsoOfFin hc
  have member (z : eligible xs) : z.val ≠ 0 ∧ z.val ∈ xs := by
    simpa [eligible] using z.property
  have eq (j : Fin N) : (below xs (e j).val).card = j.val := by
    rw [eligible_below,below_index]
  apply chosen_eq
  · exact (member (e i)).2
  · exact ⟨(member (e i)).1,congrArg (fun n : ℕ => (n : Word w)) (eq i)⟩
  · intro z hz hn rank
    let v : eligible xs := ⟨z,by simp [eligible,hn,hz]⟩
    let j := e.symm v
    have hj : e j = v := e.apply_symm_apply v
    have actual : (below xs z).card = j.val := by simpa only [hj] using eq j
    rw [actual] at rank
    have ji : j = i := Fin.ext (by
      have same := congrArg Fin.val rank
      simpa [Fin.val_natCast,Nat.mod_eq_of_lt (j.isLt.trans_le fits),
        Nat.mod_eq_of_lt (i.isLt.trans_le fits)] using same)
    exact (congrArg Subtype.val (ji ▸ hj)).symm

end ThreeFlat.Diagonal.CompressorPacking.Native.Rank

end OAI
