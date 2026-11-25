import OAI.Hierarchy.DescentEqualityRangeDigits
import OAI.Hierarchy.DescentFallbackPhysicalColumns
import OAI.Hierarchy.DescentMeasuredFallbackLane
import OAI.Hierarchy.DescentOperandApertureOrder

namespace OAI
/-! # The exceptional-tree operand columns repeat the range of the actual gate lane -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentFallbackItemSelect DescentFallbackOperandQuery DescentDenseHostOrder DescentResetLocalRoster
open DescentRetainedRangeDigits DescentBundleHistory DescentLaneGates DescentTreeLaneProgram
open scoped Classical
noncomputable section
set_option quotPrecheck false

def rangeDigit (hit : Option (ℕ×ℕ×ℕ×Bool)) (f : Fin 3) : ℕ :=
  hit.elim 0 (fun h=>value ⟨0,1,h.2.2.1⟩ f)

variable {n : ℕ} (C : DescentFallbackOperandBranch.Config) (s : Bool) (cap ht : ℕ) (ds : List Bool)
    (root : code C.residual×Option (Fin (2^n))) (items : Fin C.count→Item) (node : ℕ) (j : Fin C.count) (leaf : ℕ)
local notation "cell" => rows C.maxDepth ds items
local notation "outgoingCell" => if ds.length=ht then cell else rows C.maxDepth (childPath C.maxDepth ds leaf) items
local notation "first" => C.visibleWords items cell j node
local notation "second" => C.visibleWords items outgoingCell j node
variable (positive : 0<C.batches)
    (picked : select items (rows C.maxDepth ds items) (node/C.batches)=some j) (landed : (items j).leaf=some leaf)

include positive picked landed in
theorem make_range (arg : ℕ) (f : Fin 3) :
    rangeDigit (C.make s cap ht ds root items node arg) f=
      if arg<first then value ⟨0,1,first⟩ f
      else if arg-first<second then value ⟨0,1,second⟩ f else 0 :=by
  by_cases incoming:arg<first
  · have fits:=fits_aperture (show arg< min 2 ((cell).card*C.batches-C.startWord items cell j node) from incoming)
    have donor:=(selected_word items cell positive fits).1
    cases ds with
    | nil=>simp [make,rangeDigit,picked,landed,incoming,donor]
    | cons b tail=>simp [make,rangeDigit,picked,landed,incoming]
  · by_cases fit:arg-first<second
    · simp [make,rangeDigit,picked,landed,incoming,not_le.mpr fit,fit]
    · simp [make,rangeDigit,picked,landed,incoming,Nat.le_of_not_gt fit,fit]

include positive picked landed in
/-- This uses the ordered previous and following lane measurements. The installed tree program
supplies the equality operation and unit strides at the same node. -/
theorem make_atSlot {A : Type} {width : A→ℕ} {Y p : ℕ} (hp : 0<p)
    (multiple : ∀a,width a=(width a/p)*p) (P : Program Y p width) (u : P.Node)
    (l r : Lane p width) (eqOp : P.op u=equalOp (.wire l) (.wire r))
    (lstride : l.stride=1) (rstride : r.stride=1)
    (left : measuredWord C p l items cell j node) (right : measuredWord C p r items outgoingCell j node)
    (arg : ℕ) (f : Fin 3) :
    rangeDigit (C.make s cap ht ds root items node arg) f=
      atSlot (ofProgram (fun a=>width a/p) multiple hp P) u arg f :=by
  rw [make_range C s cap ht ds root items node j leaf positive picked landed,
    equality_slot _ multiple hp P u l r eqOp]
  simp only [laneCode,Lane.residue,left.1,right.1,Nat.mul_mod_left,lstride,rstride,left.2.2,right.2.2]

end
end Hierarchy.DescentFallbackOperandBranch.Config

namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentFallbackOperandBranch DescentRetainedRangeDigits DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : DescentResetPublicOperandBook.Config)

/-- These are exactly fields 4, 5 and 6 of the joint printed lookup, including blank rows. -/
theorem column_range (width : ℕ) (x : C.Data n) (arg : Fin C.args) (node : Fin C.nodes) (f : Fin 3) :
    C.column board width (some (page f)) (finProdFinEquiv (arg,node)) x=
      ((DescentFallbackOperandBranch.Config.rangeDigit (C.mixed board node.val arg.val x) f : ℕ) : Cell width) :=by
  unfold column
  simp only [Equiv.symm_apply_apply]
  cases hit:C.mixed board node.val arg.val x with
  | none=>rfl
  | some z=>
    obtain ⟨q,word,count,marked⟩:=z
    fin_cases f <;> rfl

/-- A natural digit determined at every output width can be read without reduction
from any cell large enough for that physical range. -/
theorem column_nat (x : C.Data n) (arg : Fin C.args) (node : Fin C.nodes) (f : Fin 3) (actual : ℕ)
    (width : ℕ) (small : DescentFallbackOperandBranch.Config.rangeDigit (C.mixed board node.val arg.val x) f≤2)
    (room : 2<2^width)
    (printed : ∀b,C.column board b (some (page f)) (finProdFinEquiv (arg,node)) x=(actual:Cell b)) :
    (C.column board width (some (page f)) (finProdFinEquiv (arg,node)) x).val=actual :=by
  let digit:=DescentFallbackOperandBranch.Config.rangeDigit (C.mixed board node.val arg.val x) f
  have upper : max actual 2<2^(max actual 2):=Nat.lt_two_pow_self
  have eqn := congrArg Fin.val (printed (max actual 2))
  rw [column_range board C] at eqn
  change ((digit:Cell (max actual 2))).val=((actual:Cell (max actual 2))).val at eqn
  rw [Fin.val_cast_of_lt (small.trans_lt ((Nat.le_max_right actual 2).trans_lt upper)),
      Fin.val_cast_of_lt ((Nat.le_max_left actual 2).trans_lt upper)] at eqn
  rw [printed width,Fin.val_cast_of_lt (eqn ▸ small.trans_lt room)]


end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
