import OAI.Hierarchy.DescentResetRetainedIssue
import OAI.Hierarchy.DescentPriorNodePresenceShape

namespace OAI
/-! # Reading the true prior presence mask through the physical reset shuffle -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.PackedFlow.Channels
open DescentGL DescentColonies DescentOrdinaryAtomFieldRAM.ScalarOperand
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : DescentResetRetainedSetup.Layout)
variable (size : 2^(v.high+v.low)=v.groups*v.blocks) (cut : v.cut≤v.high+v.low)
    (matrix : DescentGL.Layout (v.high+v.low)) (x : v.Values)
    (h : Fin v.hosts) (hi : Block v.cut) (d : Fin v.donors)
local notation "physical" => v.site (fun j=>blockValues cut (v.before size x j) matrix) h hi
local notation "key_" => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi d)
local notation "cell_" => (finProdFinEquiv.symm (Fin.cast size key_) : Fin v.groups×Fin v.blocks)
variable (tokenBits roleLanes : ℕ)
local notation "mask_" => (⟨v.blocks,v.previousNodes,v.hosts,v.groups,tokenBits,v.bits,roleLanes,v.previousLanes⟩
  : DescentPriorNodePresence.Chart)

/-- At the actual source of each remixed donor, the decoder's counter sees the
one-based primitive token of the prior node after the native presence conversion. -/
theorem issued_presence (role : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell (tokenBits*v.previousNodes))
    (source : ∀b h' g',x (v.sourceID v.occupiedField b) h' g'=(mask_).readings (role b h' g'))
    (positive : 0<v.bits) (n : Fin v.previousNodes) :
    (v.entry physical d n v.occupiedField).val≠0 ↔
      ((encode tokenBits v.previousNodes).symm (role (cell_).2 h (cell_).1) n).val≠0 := by
  rw [v.prior_digit x size cut matrix h hi d n v.occupiedField,source]
  change (((encode v.bits v.previousNodes).symm ((mask_).readings _) n).val≠0) ↔ _
  rw [(mask_).at_node]
  split
  next missing=>exact iff_of_false (fun nz => nz rfl) (fun nz => nz missing)
  next live=>
    have one : 1<2^v.bits:=Nat.one_lt_two_pow (by omega)
    apply iff_of_true _ live
    change 1 % (2^v.bits) ≠ 0
    rw [Nat.mod_eq_of_lt one]
    decide

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
