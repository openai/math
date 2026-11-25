import OAI.Hierarchy.DescentTerminalRoleWordRoom
import OAI.Hierarchy.DescentTerminalRawSpanBound
import OAI.Hierarchy.DescentTerminalIssuedScale
import OAI.Hierarchy.DescentTerminalRoleTables
import OAI.Hierarchy.DescentTerminalPrimitiveSpace
import OAI.Hierarchy.DescentTerminalPrivateSourceChannels

namespace OAI
/-! # The actual combined-role and private-count cells fit the jointly chosen terminal word -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette
open DescentTerminalVertexFields Filter
open scoped Classical BigOperators
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)

/-- A uniform three-input width for the count table, including higher unused padding. -/
theorem count_inputs (q tags H N A p groups:ℕ) (f:Fin 3) :
    familySize (q:=q) (t:=tags) (H:=H) (N:=N) (A:=A) (w:=p) (DescentTerminalPrivateSourceChannels.family f)*groups≤
      groups*span q tags H N A p := by
  rw [Nat.mul_comm]
  apply Nat.mul_le_mul_left
  fin_cases f <;> simp [DescentTerminalPrivateSourceChannels.family,familySize,itemBits,items,size] <;> omega

theorem count_words_room (groups span h:ℕ) (paid:32*(groups*(span+1))≤h) (positive:0<groups) :
    3*(groups*span)+2≤h/2:=by rw [Nat.mul_add,Nat.mul_one] at paid;omega

/-- Both actual ROM prices follow on the same machine height. Group-slot padding
is retained; the estimate is uniform over all occupation masks. -/
theorem mounted_room (n a g p stride N groups h span:ℕ)
    (roles:32*(groups*(DescentBundleTagKeys.width (Nat.clog 2 (n+1)) a g p stride*N+1))≤h)
    (counts:32*(groups*(span+1))≤h) (positive:0<groups) :
    DescentTerminalRoleTables.count (fun f=>DescentTerminalCombinedRole.width n a g p stride f*N*groups)≤2^(h/2) ∧
      DescentTerminalPrimitiveArena.fee 3 (groups*span)≤2^(h/2) := by
  constructor
  · exact DescentTerminalRoleTables.price (role_words_room n a g p stride N groups h roles positive)
  · apply DescentTerminalPrimitiveArena.fee_le _ _ _ (by decide)
    have bits:=count_words_room groups span h counts positive
    have radix:Nat.clog 2 (3+1)=2:=by decide
    rw [radix,Nat.mul_comm];exact bits

end
end Hierarchy.DescentSixParty

end OAI
