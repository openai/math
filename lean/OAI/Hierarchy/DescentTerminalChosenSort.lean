import OAI.Hierarchy.TaggedSortLiftRecursive
import OAI.Hierarchy.DescentTerminalPhysicalVolume
import OAI.Hierarchy.TaggedWidthSlices

namespace OAI
/-! # Choosing and paying the actual homogeneous bank for a full native history -/
namespace Hierarchy.DescentTerminalChosenSort
open Tagged.SortLift DescentTerminalHost.SortBank
open scoped Classical BigOperators
noncomputable section

variable (κ : Type*) [LinearOrder κ] {h e : ℕ} (base : 4≤h) (lo : h-1≤e) (hi : e≤3*h)

/-- One fixed seven-level family of actual stages is shared across all input histories. -/
def program : List (Stage (2^e)) :=
  Classical.choose (recursive_sorts κ h base 7 e lo (hi.trans (DescentSortLiftHeight.threefold base)))

private theorem spec :
    (program κ base lo hi).length=4^7 ∧
    Widths (fun w=>2^(h-1)≤w ∧ w≤2^h) (program κ base lo hi) ∧
    Sorts (program κ base lo hi) κ :=
  Classical.choose_spec (recursive_sorts κ h base 7 e lo (hi.trans (DescentSortLiftHeight.threefold base)))

abbrev stages := (program κ base lo hi).get

theorem depth : (program κ base lo hi).length=4^7 := (spec κ base lo hi).1

theorem sorts : Sorts (List.ofFn (stages κ base lo hi)) κ := by
  simpa only [stages,List.ofFn_get] using (spec κ base lo hi).2.2

theorem widths (i : Fin (program κ base lo hi).length) (j : Fin ((stages κ base lo hi i).blocks)) :
    2^h≤2*(stages κ base lo hi i).length j ∧ (stages κ base lo hi i).length j≤2^h := by
  obtain ⟨l,u⟩:=(spec κ base lo hi).2.1 _ (List.get_mem _ i) j
  refine ⟨?_,u⟩
  have hp : 2^h=2*2^(h-1) := by
    conv_lhs => rw [show h=h-1+1 by omega,pow_succ,Nat.mul_comm]
  exact hp.le.trans (Nat.mul_le_mul_left _ l)

theorem volume : localCount (stages κ base lo hi)*2^h+2^h ≤
    (2*4^7+1)*(2^e+2^h) :=
  DescentTerminalHost.SortBank.physical_volume h h e _
    (fun i j=>(widths κ base lo hi i j).1) (depth κ base lo hi).le

theorem fields (payload K : ℕ) (hpos : 0<h) (bits : payload≤K*h) :
    let parts:=TaggedWidthSlices.count (h+payload) h
    0<parts ∧ parts≤K+1 ∧
    (∑ j : Fin parts,TaggedWidthSlices.width (h+payload) h j)=h+payload ∧
    ∀j : Fin parts,TaggedWidthSlices.width (h+payload) h j≤h :=
  ⟨TaggedWidthSlices.count_pos (by omega) hpos,
   TaggedWidthSlices.count_le hpos (by rw [Nat.add_mul,Nat.one_mul];omega),
   TaggedWidthSlices.sum_width hpos,TaggedWidthSlices.width_le hpos⟩

end
end Hierarchy.DescentTerminalChosenSort

end OAI
