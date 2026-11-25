import OAI.Computability.BorderVNP.PackedBundleDirectoryISA
import OAI.Computability.BorderVNP.PackedBundleGroups

/-! # The marker-free six-word bundle table and the two-word cell ranges -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BundleDirectory

open BottomReports
open BottomReports.Writer (write write_read write_outside)
open RoutingISA.CellPacket

/-- Six consecutive words per site header in the source order of this cell. -/
def cellWords (g : ℕ → List BundleHeader) (c : ℕ) := (g c).flatMap BundleHeader.words

/-- The true sequence of physical writes up to but excluding cell i. -/
def Layout.image (l : Layout) (g : ℕ → List BundleHeader) (m : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => m
  | i+1 =>
    let j := «prefix» g i
    let d := write (l.image g m i) (l.output+6*j) (cellWords g i)
    write d (l.ranges+2*i) [j,«prefix» g (i+1)]

/-- No address outside the two completed output prefixes was changed. -/
theorem Layout.image_outside (l : Layout) (g : ℕ → List BundleHeader) (m : ℕ → ℕ)
    (n j : ℕ) (hr : j < l.ranges ∨ l.ranges+2*n ≤ j)
    (hd : j < l.output ∨ l.output+6*«prefix» g n ≤ j) : l.image g m n j = m j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : (cellWords g n).length = 6*(g n).length := fields_length _
    simp only [prefix_succ,Nat.mul_add] at hd
    rw [image,write_outside _ _ _ _ (by simp; omega),write_outside _ _ _ _ (by rw [hl]; omega)]
    exact ih (by omega) (by omega)

/-- Address separation for a single word of an entire protected allocation. -/
theorem apart_word {a len b size j : ℕ} (ha : apart a len b size)
    (hb : b ≤ j) (hj : j < b+size) : j < a ∨ a+len ≤ j := by
  rcases ha with h | h <;> omega

/-- Both ranges and every six-word record are contiguous and stable in the actual image. -/
theorem Layout.image_cell (l : Layout) (g : ℕ → List BundleHeader) (m : ℕ → ℕ)
    (total : «prefix» g l.cells = l.bundles)
    (sep : apart l.ranges (2*l.cells) l.output (6*l.bundles)) (n : ℕ) (hn : n ≤ l.cells)
    (c : ℕ) (hc : c < n) :
    WordsAt (l.image g m n) (l.ranges+2*c) [«prefix» g c,«prefix» g (c+1)] ∧
    WordsAt (l.image g m n) (l.output+6*«prefix» g c) (cellWords g c) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have endBound := prefix_mono g hn
    rw [total] at endBound
    have width (i : ℕ) : (cellWords g i).length = 6*(g i).length := fields_length _
    have keepRange (j : ℕ) (hj : j<l.ranges+2*n) (hj' : l.ranges ≤ j) :
        l.image g m (n+1) j = l.image g m n j := by
      rw [image,write_outside _ _ _ _ (.inl hj),write_outside]
      rw [width]
      rcases sep with h | h <;> simp only [prefix_succ] at endBound <;> omega
    have keepData (j : ℕ) (hj : l.output ≤ j) (hj' : j < l.output+6*«prefix» g n) :
        l.image g m (n+1) j = l.image g m n j := by
      rw [image,write_outside _ _ _ _ ?_,write_outside _ _ _ _ (.inl hj')]
      simp only [List.length_cons,List.length_nil]
      rcases sep with h | h <;> simp only [prefix_succ] at endBound <;> omega
    by_cases eqn : c=n
    · subst c
      constructor
      · intro j
        exact write_read _ _ _ j
      · intro j
        rw [image,write_outside]
        · exact write_read _ _ _ j
        · have hj : j.val < 6*(g n).length := j.isLt.trans_eq (width n)
          simp only [List.length_cons,List.length_nil,prefix_succ] at *
          rcases sep with h | h <;> omega
    · have hc' : c < n := by omega
      obtain ⟨hr,hd⟩ := ih (by omega) hc'
      constructor
      · intro j
        have hj : j.val < 2 := j.isLt
        rw [keepRange _ (by omega) (by omega)]
        exact hr j
      · intro j
        have hj : j.val < 6*(g c).length := j.isLt.trans_eq (width c)
        have hb := prefix_mono g (show c+1 ≤ n by omega)
        rw [prefix_succ] at hb
        rw [keepData _ (by omega) (by omega)]
        exact hd j

/-- True sorted interval endpoints, rank bounds, and stable words for each cell. -/
structure Layout.Sections (l : Layout) (g : ℕ → List BundleHeader) (width : ℕ) (m : ℕ → ℕ) : Prop where
  /-- Both marker ranks refer to positions inside the sorted array. -/
  rankBound : ∀ c < l.cells, m (l.rank+c) < width ∧ m (l.stopRank+c) < width
  /-- The open interval contains exactly six scalar words per site in this cell. -/
  extent : ∀ c < l.cells, l.start m c+(cellWords g c).length = l.stop m c
  /-- All scalar words in that interval come from the original assigned sites. -/
  words : ∀ c < l.cells, WordsAt m (l.start m c) (cellWords g c)

end Packing.BundleDirectory

end BorderVNP
end Computability
end OAI
