import OAI.Hierarchy.DescentFallbackOperandBranch
import OAI.Hierarchy.DescentTreeLaneAddresses

namespace OAI
/-! # Flattened pointer words at the two arguments of an ordered fallback equality -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentTreePrefixIntervals DescentFallbackOperandQuery DescentFallbackItemSelect DescentResetLocalRoster
open scoped Classical
noncomputable section
variable {n : ℕ} (C : Config)
variable (s : Bool) (cap height : ℕ) (path : List Bool)
variable (root : code C.residual×Option (Fin (2^n))) (items : Fin C.count→Item)
variable (node arg : ℕ) (j : Fin C.count) (leaf : ℕ)
local notation "here" => rows C.maxDepth path items
local notation "next" => rows C.maxDepth (childPath C.maxDepth path leaf) items
local notation "first" => C.startWord items here j node
local notation "incoming" => C.visibleWords items here j node
local notation "childFirst" => C.startWord items next j node
local notation "childWords" => C.visibleWords items next j node
variable (picked : select items (rows C.maxDepth path items) (node/C.batches)=some j) (landed : (items j).leaf=some leaf)

include picked landed in
theorem input_edge (level : path≠[]) (inside : arg< incoming) :
    C.make s cap height path root items node arg=
      some (C.treeAt s true cap height (path.length-1) leaf root,first+arg,incoming,true) :=by
  cases path with
  | nil=>contradiction
  | cons a rest=>simp [make,picked,landed,inside]

include picked landed in
theorem input_pin (level : path=[]) (inside : arg< incoming) (other : Fin C.count)
    (actual : select items here ((first+arg)/C.batches)=some other) :
    C.make s cap height path root items node arg=
      some (C.stemAt s cap (items other),(first+arg)%C.batches,incoming,false) :=by
  subst path
  simp [make,picked,landed,inside,actual]

include picked landed in
theorem output_edge (level : path.length≠height) (afterIn : incoming≤arg)
    (inside : arg-incoming<childWords) :
    C.make s cap height path root items node arg=
      some (C.treeAt s false cap height path.length leaf root,childFirst+(arg-incoming),childWords,true) :=by
  simp [make,picked,landed,not_lt.mpr afterIn,level,not_le.mpr inside]

include picked landed in
theorem output_pin (level : path.length=height) (afterIn : incoming≤arg)
    (inside : arg-incoming< incoming) :
    C.make s cap height path root items node arg=
      some (C.contactAt s cap height leaf root,first+(arg-incoming),incoming,true) :=by
  simp [make,picked,landed,not_lt.mpr afterIn,level,not_le.mpr inside]

include picked landed in
theorem outside (afterIn : incoming≤arg)
    (afterOut : C.visibleWords items (if path.length=height then here else next) j node≤arg-incoming) :
    C.make s cap height path root items node arg=none :=by
  by_cases top:path.length=height
  · simp only [top,ite_true] at afterOut
    simp [make,picked,landed,not_lt.mpr afterIn,top,afterOut]
  · simp only [top,ite_false] at afterOut
    simp [make,picked,landed,not_lt.mpr afterIn,top,afterOut]

/-- On an actual ranked item the printed node splits into its chronological predecessor count
and its p-wide batch. The visible argument length is the lane cover of this very cable. -/
theorem word_rank (live : Finset (Fin C.count)) (m : Fin C.batches)
    (seen : j∈live) :
    let n₀:=rank items live j*C.batches+m.val
    select items live (n₀/C.batches)=some j ∧ C.startWord items live j n₀=n₀ ∧
      C.visibleWords items live j n₀=min 2 (live.card*C.batches-n₀) :=by
  have rem : (rank items live j*C.batches+m.val)%C.batches=m.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt m.isLt]
  exact ⟨select_nth items live seen _ m,by simp only [startWord,rem],by simp only [visibleWords,startWord,rem]⟩

end
end Hierarchy.DescentFallbackOperandBranch.Config

end OAI
