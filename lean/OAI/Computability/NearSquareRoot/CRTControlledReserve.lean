import OAI.Computability.NearSquareRoot.CRTPositionShort
import Mathlib.Data.List.FinRange

/-! # Gathering fixed positions at both ends of an address

Only an end position moved by the matching needs to be exchanged. The algorithm
pairs these positions in increasing order with distinct fixed interior positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {k : ℕ}

def endPosition (lo hi : ℕ) (x : Fin k) : Bool := decide (x.val < lo ∨ k-hi ≤ x.val)

def misplaced (p : Equiv.Perm (Fin k)) (lo hi : ℕ) : List (Fin k) :=
  (List.finRange k).filter (fun x => endPosition lo hi x && decide (p x ≠ x))

def available (p : Equiv.Perm (Fin k)) (lo hi : ℕ) : List (Fin k) :=
  (List.finRange k).filter (fun x => !endPosition lo hi x && decide (p x = x))

def reserveMoves (p : Equiv.Perm (Fin k)) (lo hi : ℕ) : List (Fin k × Fin k) :=
  (misplaced p lo hi).zip (available p lo hi)

@[simp] theorem mem_misplaced (p : Equiv.Perm (Fin k)) (lo hi : ℕ) (x : Fin k) :
    x ∈ misplaced p lo hi ↔ endPosition lo hi x = true ∧ p x ≠ x := by simp [misplaced]

@[simp] theorem mem_available (p : Equiv.Perm (Fin k)) (lo hi : ℕ) (x : Fin k) :
    x ∈ available p lo hi ↔ endPosition lo hi x = false ∧ p x = x := by simp [available]

private def endSet (k lo hi : ℕ) : Finset (Fin k) := Finset.univ.filter (fun x => endPosition lo hi x)

private theorem endSet_card {lo hi : ℕ} (fit : lo+hi ≤ k) : (endSet k lo hi).card ≤ lo+hi := by
  let left : Fin lo ↪ Fin k := Fin.castLEEmb (by omega)
  let right : Fin hi ↪ Fin k := ⟨fun x => ⟨k-hi+x.val, by have := x.isLt; omega⟩,
    fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
  have sub : endSet k lo hi ⊆ Finset.univ.map left ∪ Finset.univ.map right := by
    intro x hx
    have he : x.val < lo ∨ k-hi ≤ x.val := by simpa [endSet,endPosition] using hx
    rcases he with hl|hr
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨⟨x.val,hl⟩,Finset.mem_univ _,rfl⟩)
    · apply Finset.mem_union_right _ (Finset.mem_map.mpr ?_)
      have := x.isLt
      exact ⟨⟨x.val-(k-hi),by omega⟩, Finset.mem_univ _, Fin.ext (by change k-hi+(x.val-(k-hi)) = x.val; omega)⟩
  simpa using (Finset.card_le_card sub).trans (Finset.card_union_le ..)

private theorem badSize (p : Equiv.Perm (Fin k)) (lo hi : ℕ) :
    (misplaced p lo hi).length = ((endSet k lo hi) \ fixedPositions p).card := by
  rw [← List.toFinset_card_of_nodup (show (misplaced p lo hi).Nodup from
    (List.nodup_finRange k).filter _)]
  congr 1
  ext x
  simp [endSet,fixedPositions]

private theorem goodSize (p : Equiv.Perm (Fin k)) (lo hi : ℕ) :
    (available p lo hi).length = (fixedPositions p \ (endSet k lo hi)).card := by
  rw [← List.toFinset_card_of_nodup (show (available p lo hi).Nodup from
    (List.nodup_finRange k).filter _)]
  congr 1
  ext x
  simp [endSet,fixedPositions,and_comm]

private theorem enough (p : Equiv.Perm (Fin k)) {lo hi : ℕ} (fit : lo+hi ≤ k)
    (free : lo+hi ≤ (fixedPositions p).card) :
    (misplaced p lo hi).length ≤ (available p lo hi).length := by
  rw [badSize,goodSize]
  have hbad := Finset.card_sdiff_add_card_inter (endSet k lo hi) (fixedPositions p)
  have hgood := Finset.card_sdiff_add_card_inter (fixedPositions p) (endSet k lo hi)
  rw [Finset.inter_comm] at hgood
  have h := endSet_card fit
  omega

/-- The number of physical two-position exchanges is bounded by the number of
positions reserved for high row indices plus low payload bits. -/
theorem reserveMoves_length (p : Equiv.Perm (Fin k)) {lo hi : ℕ} (fit : lo+hi ≤ k) :
    (reserveMoves p lo hi).length ≤ lo+hi := by
  apply le_trans (show (reserveMoves p lo hi).length ≤ (misplaced p lo hi).length by simp [reserveMoves])
    ((badSize p lo hi) ▸ (Finset.card_le_card Finset.sdiff_subset).trans (endSet_card fit))

private theorem pairedGather {α : Type*} [DecidableEq α] (bad good : List α)
    (dn : bad.Nodup) (gn : good.Nodup) (apart : ∀ x ∈ bad, x ∉ good) (size : bad.length ≤ good.length) :
    (∀ x ∈ bad, positionExchanges (bad.zip good) x ∈ good) ∧
    (∀ x, x ∉ bad → x ∉ good → positionExchanges (bad.zip good) x = x) := by
  induction bad generalizing good with
  | nil => simp [positionExchanges]
  | cons u bs ih =>
    cases good with
    | nil => simp at size
    | cons v gs =>
      have B := List.nodup_cons.mp dn
      have G := List.nodup_cons.mp gn
      have off : ∀ x ∈ bs, x ∉ gs := fun x hx h => apart x (by simp [hx]) (by simp [h])
      obtain ⟨land,stay⟩ := ih gs B.2 G.2 off (by simpa using size)
      have offu := apart u List.mem_cons_self
      constructor
      · intro x hx
        change Equiv.swap u v (positionExchanges (bs.zip gs) x) ∈ v::gs
        rcases List.mem_cons.mp hx with rfl|xB
        · rw [stay _ B.1 (fun h => offu (List.mem_cons_of_mem _ h)),Equiv.swap_apply_left]
          exact List.mem_cons_self
        · have h := land x xB
          have nu : positionExchanges (bs.zip gs) x ≠ u := by
            rintro eq; exact offu (List.mem_cons_of_mem _ (eq ▸ h))
          have nv : positionExchanges (bs.zip gs) x ≠ v := fun eq => G.1 (eq ▸ h)
          rw [Equiv.swap_apply_of_ne_of_ne nu nv]
          exact List.mem_cons_of_mem _ h
      · intro x hb hg
        change Equiv.swap u v (positionExchanges (bs.zip gs) x) = x
        have nu : x ≠ u := fun eq => hb (eq ▸ List.mem_cons_self)
        have nv : x ≠ v := fun eq => hg (eq ▸ List.mem_cons_self)
        rw [stay _ (fun h => hb (List.mem_cons_of_mem _ h)) (fun h => hg (List.mem_cons_of_mem _ h)),
          Equiv.swap_apply_of_ne_of_ne nu nv]

def reservedMatching (p : Equiv.Perm (Fin k)) (lo hi : ℕ) : Equiv.Perm (Fin k) :=
  let move := positionExchanges (reserveMoves p lo hi)
  (move.trans p).trans move.symm

/-- After conjugating by the generated list, both appointed ends are pointwise fixed. -/
theorem reservedMatching_fixed (p : Equiv.Perm (Fin k)) {lo hi : ℕ} (fit : lo+hi ≤ k)
    (free : lo+hi ≤ (fixedPositions p).card) (x : Fin k)
    (hx : x.val < lo ∨ k-hi ≤ x.val) : reservedMatching p lo hi x = x := by
  let move := positionExchanges (reserveMoves p lo hi)
  obtain ⟨land,stay⟩ := pairedGather (misplaced p lo hi) (available p lo hi)
    ((List.nodup_finRange k).filter _) ((List.nodup_finRange k).filter _)
    (fun j hb hg => (mem_misplaced .. |>.mp hb).2 (mem_available .. |>.mp hg).2)
    (enough p fit free)
  have he : endPosition lo hi x = true := by exact decide_eq_true hx
  have hf : p (move x) = move x := by
    by_cases h : p x = x
    · have stayx : move x = x := stay x (by simp [h]) (by simp [he])
      rwa [stayx]
    · exact (mem_available .. |>.mp (land x (by simp [he,h]))).2
  change move.symm (p (move x)) = x
  rw [hf, Equiv.symm_apply_apply]

theorem reserve_reconstruct (p : Equiv.Perm (Fin k)) (lo hi : ℕ) :
    let move := positionExchanges (reserveMoves p lo hi)
    (move.symm.trans (reservedMatching p lo hi)).trans move = p := by
  ext x
  simp [reservedMatching]

end Controlled

end NearSquareRoot
end Computability
end OAI
