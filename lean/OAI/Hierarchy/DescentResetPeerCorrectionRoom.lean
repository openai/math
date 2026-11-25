import OAI.Hierarchy.DescentDenseHostOrder
import OAI.Hierarchy.DescentResetPeerJointRAM

namespace OAI
/-! The two public trunk shapes supply enough digits for the predecessor sign
correction whenever the shape-and-halo coordinate fits. -/
namespace Hierarchy.DescentDenseHostOrder
open DescentCommonHost DescentRelativeContacts DescentHostDirectory DescentResetHostSize
open scoped Classical
noncomputable section

theorem two_le_roster_card {n h : ℕ} (G : NonlinearExpanders.Graph n h) (r height : ℕ) :
    2≤(roster G r height).card := by
  let root : Code r:=⟨(0,0),mem_codes (Nat.zero_le _) (by decide)⟩
  let node (s : Bool) : Pool G Unit r height:=(s,(),root,.inl none)
  have member (s : Bool) : render G r height (node s)∈roster G r height:=
    Finset.mem_image.mpr ⟨node s,Finset.mem_univ _,rfl⟩
  exact Finset.one_lt_card.mpr ⟨_,member false,_,member true,by simp [node,render]⟩

theorem predecessor_sign_fits {n h : ℕ} (G : NonlinearExpanders.Graph n h) (r height D b : ℕ)
    (packed : (roster G r height).card*DescentResetPeerJointRAM.radix D≤2^b) :
    2*(D+1)≤2^b :=
  (Nat.mul_le_mul (two_le_roster_card G r height)
    ((Nat.le_succ _).trans (show D+2≤DescentResetPeerJointRAM.radix D from Nat.le_pow_clog (by decide) _))).trans packed

end
end Hierarchy.DescentDenseHostOrder

end OAI
