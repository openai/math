import OAI.Hierarchy.DescentResetPublicDepth
import OAI.Hierarchy.DescentSenderBoardHeight
import OAI.Hierarchy.DescentFallbackActorWordRoom
import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # Machine words for the fixed graph and actor indices at each authentic reset -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentDatedAddressBook Filter
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)

theorem degree_at_reset_positive (t:ℕ) : 0< atRound t := by
  cases t with
  | zero=>decide
  | succ j=>simp only [atRound,ordinaryDegree];positivity

structure ResetActorWords (d D n k f g w:ℕ) : Prop where
  board : d≤2^k
  degree : 0<32*Nat.clog 2 (2*D)
  ranks : D*2^(GroupStage.depthBound D n f g)<2^w
  actor : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*D)) g n≤ w
  successor : D+1<2^w
  depth : GroupStage.depthBound D n f g+2< w

theorem reset_actor_words (t f g rate n d β:ℕ) (den:0<β) :
    ∀ᶠ h:ℕ in atTop,let k:=groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)
      ∀w:ℕ,h≤ w→ResetActorWords d (atRound t) n k f g w := by
  let D:=atRound t
  let Ht:=GroupStage.depthBound D n f g
  let A:=1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g
  let extra:=max (32*Nat.clog 2 (2*D)) g+n+1
  let C:=4*(A+extra)+1
  filter_upwards [ResetMiddle.sender_board_at t β (hostRate t rate) (capRate G t g) (cutRate t f g) d den,
    dyadic_log_room C 1,eventually_ge_atTop (D*2^Ht+D+Ht+4)] with h board words large
  dsimp only
  intro w width
  let k:=groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)
  let L:=Nat.log 2 h+1
  have positive:1≤ L:=Nat.succ_pos _
  have bits:k≤ A*L :=
    (groupBits_linear t _ (hostRate t rate) (capRate G t g) (cutRate t f g)).trans
      (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.div_le_self ..)))
  have root:0< D:=degree_at_reset_positive t
  have digit:=Nat.clog_pos (by decide:1<2) (show 1<2*D by omega)
  have space:h<2^w := (Nat.lt_two_pow_self (n:=h)).trans_le (Nat.pow_le_pow_right (by decide) width)
  refine ⟨board,Nat.mul_pos (by decide) digit,by change D*2^Ht<_;omega,?_,by change D+1<_;omega,by change Ht+2<_;omega⟩
  change 4*(k+max (32*Nat.clog 2 (2*D)) g+n+1)+1≤ w
  have constant:extra≤ extra*L:=Nat.le_mul_of_pos_right _ positive
  have digitSize:4*(k+extra)+1≤ C*L:=by
    dsimp only [C]
    rw [Nat.add_mul,Nat.mul_assoc,Nat.add_mul,one_mul]
    omega
  have economical:C*L≤ h:=by simpa only [pow_one] using words
  simpa only [extra,←Nat.add_assoc] using digitSize.trans (economical.trans width)

end
end Hierarchy.DescentSixParty

end OAI
