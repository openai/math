import OAI.Hierarchy.DescentContactLinks
import OAI.Hierarchy.DescentPackedWords
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Finite contact directories and their logarithmic relay depth -/

namespace Hierarchy.DescentContactTree
open scoped Classical BigOperators
noncomputable section
variable {C : Type*} [Fintype C]

def codeHeight (C : Type*) [Fintype C] := Nat.clog 2 (Fintype.card C)

def directory (C : Type*) [Fintype C] : C ↪ Node (codeHeight C) :=
  (Fintype.equivFin C).toEmbedding.trans <|
    (Fin.castLEEmb (Nat.le_pow_clog (show 1<2 by decide) (Fintype.card C))).trans
      (DescentRotor.bitWord (codeHeight C)).symm.toEmbedding

/-- Every actual contact has a unique leaf of the padded balanced tree. -/
def contactBit (c : C) (n : ℕ) : Bool :=
  if h : n<codeHeight C then directory C c ⟨n,h⟩ else false

@[simp] theorem prefix_contactBit (c : C) :
    prefixAt contactBit (codeHeight C) c=directory C c := by
  funext n
  simp [prefixAt,contactBit,n.isLt]

theorem unique_leaf (c d : C) :
    prefixAt contactBit (codeHeight C) c=prefixAt contactBit (codeHeight C) d ↔ c=d := by
  simp

theorem height_bound (M : ℕ) (h : Fintype.card C≤M) : codeHeight C≤Nat.clog 2 M :=
  Nat.clog_mono_right 2 h

/-- Each terminal invokes the construction with its own two finite directories.
Two different catalog numbers on the two ends may designate the same physical
link, so only the actual wire correspondence is shared. -/
theorem coded_cost {I R : Type*} [Fintype I] [Fintype R]
    (contact : I → C) (other : C → R) (wt : I → ℕ) :
    (∑ d∈Finset.range (codeHeight C+1),∑ v : Node d,
      ∑ i : Cell (fun i => contactBit (contact i)) d v,wt i.val)+
      (∑ c : C,∑ i : {i // contact i=c},wt i.val)+
      (∑ d∈Finset.range (codeHeight R+1),∑ v : Node d,
      ∑ i : Cell (fun i => contactBit (other (contact i))) d v,wt i.val)=
      (codeHeight C+codeHeight R+3)*(∑i,wt i) :=
  two_tree_cost contact wt _ _ _ _

end
end Hierarchy.DescentContactTree

end OAI
