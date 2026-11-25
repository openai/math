import OAI.Hierarchy.DescentBitQuotient
import OAI.Hierarchy.DescentMergedSiteLoad

namespace OAI
/-! # A contracted cable becomes a private variable with its original, already counted width -/

namespace Hierarchy.DescentHistoryOrder
open DescentKernelHistory DescentNetworkPartition DescentSixParty.GadgetNetwork Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D d : ℕ} {P U V : Type} [Fintype V] {w : P→ℕ} (N : Network D P w)
variable (r : SiteBits (U:=U) N)
def privateWidth (a : N.Site) := ∑h : (r a).Hidden,(r a).hiddenWidth h

/-- Total number of private bits plus the widths of live cables at this site.
Local self-loops occur once in this count. -/
def localVolume (v : N.Site) := privateWidth N r v+siteLoad N v

variable (loc : N.Site→V) (pos : V→EuclideanSpace ℝ (Fin d)) (ball : ∀v,‖pos v‖≤1)
local notation "Q" => quotient N loc pos ball
local notation "old" => quotientBits N loc pos ball r

theorem quotient_private_width (c : V) :
    privateWidth Q old c=(∑e : PrivateEdge N loc c,N.width e.val)+
      ∑u : {u //loc u=c},privateWidth N r u.val := by
  let absorbed (e : PrivateEdge N loc c) := N.width e.val
  let carried (x : Σ u : {u // loc u = c}, (r u.val).Hidden) := (r x.1.val).hiddenWidth x.2
  change (∑ x, Sum.elim absorbed carried x) = _
  rw [Fintype.sum_sum_type (Sum.elim absorbed carried)]
  exact congrArg₂ (· + ·) rfl (Fintype.sum_sigma carried)

private theorem selected_sum {E : Type} [Fintype E] (p : E→Prop) [DecidablePred p] (f : E→ℕ) :
    (∑e : Subtype p,f e.val)=∑e,if p e then f e else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_subtype (Finset.univ.filter p) (fun e=>by simp) f]

theorem internal_live_sum (c : V) :
    (∑ e : PrivateEdge N loc c,N.width e.val)+ siteLoad Q c=∑e,oldBill N loc c e := by
  let privateAt (e : N.Edge) := loc (N.src e)=c ∧ loc (N.dst e)=c
  let cross (e : N.Edge) := loc (N.src e)≠loc (N.dst e)
  let touch (e : N.Edge) := loc (N.src e)=c ∨ loc (N.dst e)=c
  change (∑e : Subtype privateAt,N.width e.val)+(∑e : Subtype cross,if touch e.val then N.width e.val else 0)=_
  rw [selected_sum privateAt N.width, selected_sum cross (fun e=>if touch e then N.width e else 0),
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases src : loc (N.src e)=c <;> by_cases dst : loc (N.dst e)=c
  · simp [privateAt, cross, oldBill, touches, src, dst]
  · simp [privateAt, cross, touch, oldBill, touches, src, dst, Ne.symm dst]
  · simp [privateAt, cross, touch, oldBill, touches, src, dst]
  · simp [privateAt, cross, touch, oldBill, touches, src, dst]

theorem quotient_local_volume (c : V) :
    localVolume Q old c≤∑u : {u //loc u=c},localVolume N r u.val := by
  simp only [localVolume,Finset.sum_add_distrib,quotient_private_width]
  rw [Nat.add_right_comm,internal_live_sum]
  exact Nat.add_le_add_right (oldBill_le N loc c) _ |>.trans_eq (Nat.add_comm _ _)

end
end Hierarchy.DescentHistoryOrder

end OAI
