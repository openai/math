import OAI.Hierarchy.DescentFallbackRepeatedFields

namespace OAI
/-! # Full pointer answer at both arguments of the exceptional equality -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentFallbackItemSelect DescentFallbackOperandQuery DescentResetLocalRoster DescentTreeLaneProgram DescentLaneGates
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {n : ℕ} (C : DescentFallbackOperandBranch.Config) (s : Bool) (cap depth : ℕ) (ds : List Bool)
    (root : code C.residual×Option (Fin (2^n))) (items : Fin C.count→Item) (leaf : ℕ)
local notation "cell" => rows C.maxDepth ds items
local notation "outgoingCell" => if ds.length=depth then cell else rows C.maxDepth (childPath C.maxDepth ds leaf) items

/-- An incoming public word may name the next chronological stem even within a single gate
operand. Its source address uses that word's own containing original item. -/
def physicalReply {Q : Type} {width : Q→ℕ} {p : ℕ} (left right : Lane p width) (arg : ℕ) :
    Option (ℕ×ℕ×ℕ×Bool) :=
  let measure:=fun a=>width a/p
  let a:=left.count measure
  let b:=right.count measure
  if arg<a then
    let word:=left.bundleStart+arg
    if ds=[] then
      if hi:word/C.batches<(cell).card then
        let origin:=(rankOrder items cell).symm ⟨word/C.batches,hi⟩
        some (C.stemAt s cap (items origin),word%C.batches,a,false)
      else none
    else some (C.treeAt s true cap depth (ds.length-1) leaf root,word,a,true)
  else if arg-a<b then
    let q:=if ds.length=depth then C.contactAt s cap depth leaf root
      else C.treeAt s false cap depth ds.length leaf root
    some (q,right.bundleStart+(arg-a),b,true)
  else none

theorem physical_range_le {Q : Type} {width : Q→ℕ} {p : ℕ} (left right : Lane p width)
    (lstride : left.stride=1) (rstride : right.stride=1) (arg : ℕ) (f : Fin 3) :
    rangeDigit (C.physicalReply s cap depth ds root items leaf left right arg) f≤2 :=by
  let units:=fun a=>width a/p
  have leftSmall : left.count units≤2:=by simpa only [lstride] using left.count_le units
  have rightSmall : right.count units≤2:=by simpa only [rstride] using right.count_le units
  have selected (q word count : ℕ) (mark : Bool) (bound : count≤2) :
      rangeDigit (some (q,word,count,mark)) f≤2:=by
    fin_cases f <;> simp [rangeDigit,DescentRetainedRangeDigits.value]; omega
  unfold physicalReply
  dsimp only
  split
  · split
    · split
      · exact selected _ _ _ _ leftSmall
      · exact Nat.zero_le _
    · exact selected _ _ _ _ leftSmall
  · split
    · exact selected _ _ _ _ rightSmall
    · exact Nat.zero_le _

theorem make_reply {Q : Type} {width : Q→ℕ} {p : ℕ} (left right : Lane p width)
    (j : Fin C.count) (node arg : ℕ) (positive : 0<C.batches)
    (picked : select items cell (node/C.batches)=some j) (landed : (items j).leaf=some leaf)
    (l : measuredWord C p left items cell j node) (r : measuredWord C p right items outgoingCell j node) :
    C.make s cap depth ds root items node arg=C.physicalReply s cap depth ds root items leaf left right arg :=by
  unfold physicalReply
  simp only [l.2.1,r.2.1,l.2.2,r.2.2]
  by_cases incoming:arg<C.visibleWords items cell j node
  · have fits:=fits_aperture (show arg< min 2 ((cell).card*C.batches-C.startWord items cell j node) from incoming)
    have seen:=(selected_word items cell positive fits).1
    have hi:=(Nat.div_lt_iff_lt_mul positive).2 fits
    cases ds with
    | nil=>simp [make,picked,landed,incoming,hi,seen]
    | cons b more=>simp [make,picked,landed,incoming]
  · by_cases external:arg-C.visibleWords items cell j node<C.visibleWords items outgoingCell j node
    · simp [make,picked,landed,incoming,external,not_le.mpr external]
    · simp [make,picked,landed,incoming,external,Nat.le_of_not_gt external]

end
end Hierarchy.DescentFallbackOperandBranch.Config

end OAI
