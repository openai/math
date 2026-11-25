import OAI.Hierarchy.DescentSignedPrefix

namespace OAI
/-! Every physically emitted column in an append-only signed date can be
read in one common poststate. The immutable inputs to its expression have
the values used at its actual execution time. -/
namespace Hierarchy.DescentDatedAddressBook.SignedPrefix
open DescentSixParty.Chronology Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section
variable {w:ℕ}
def Job.Written (base:ℕ) (m:Memory w):Job→Prop
  | .words n value=>∀i:Fin n,m (base+i.val)=(value i.val:Word w)
  | .columns c n pitch expr=>∀j:Fin c,∀i:Fin n,m (base+j.val*pitch+i.val)=(expr j.val).eval m (i.val:Word w)
def Written (m:Memory w):List Job→ℕ→Prop
  | [],_=>True
  | j::js,base=>j.Written base m ∧ Written m js (base+j.width)

theorem Job.written (j:Job) (base:ℕ) (m m':Memory w) (fit:j.Fits base w) (room:base+j.width<2^w)
    (prior:∀a<base,m' a=m a)
    (kept:∀a,base≤a→a<base+j.width→m' a=(j.atBase base w).image m a):
    j.Written base m':=by
  cases j with
  | words n value=>
    intro i
    have hi:base+i.val<base+n:=Nat.add_lt_add_left i.isLt _
    exact (kept _ (Nat.le_add_right ..) hi).trans (DescentStaticWordColumn.read base n value m i.isLt)
  | columns c n pitch expr=>
    intro j i
    have hr:=i.isLt.trans_le fit.1
    have hi:base+j.val*pitch+i.val<base+c*pitch:=by
      have upper:=Nat.mul_le_mul_right pitch j.isLt
      rw [Nat.succ_mul] at upper
      omega
    have step:=DescentPackedFlowBatch.execute base n pitch c expr m fit.2 room fit.1
    exact ((kept _ (by omega) hi).trans (step.2.1 j i)).trans
      (eval_below _ _ m m' (fit.2 j.val j.isLt) prior).symm

theorem earlier_below (js:List Job) (base:ℕ) (m:Memory w) (fit:Fits w js base)
    (room:finish js base<2^w) (a:ℕ) (before:a<base):earlier js base m a=m a:=by
  induction js generalizing base m with
  | nil=>rfl
  | cons j js ih=>
    have top:base+j.width<2^w:=(lower js _).trans_lt room
    exact (ih (base+j.width) ((j.atBase base w).image m) fit.2 room (before.trans_le (Nat.le_add_right ..))).trans
      ((j.any base m fit.1 top).2 a (.inl before))

theorem written (js:List Job) (base:ℕ) (m:Memory w) (fit:Fits w js base) (room:finish js base<2^w):
    Written (earlier js base m) js base:=by
  induction js generalizing base m with
  | nil=>trivial
  | cons j js ih=>
    let mid:=(j.atBase base w).image m
    let last:=earlier js (base+j.width) mid
    have top:base+j.width<2^w:=(lower js _).trans_lt room
    have before (a:ℕ) (h:a<base+j.width):last a=mid a:=earlier_below js _ mid fit.2 room a h
    exact ⟨j.written base m last fit.1 top (fun a h=>(before a (h.trans_le (Nat.le_add_right ..))).trans
      ((j.any base m fit.1 top).2 a (.inl h))) (fun a _ h=>before a h),ih _ _ fit.2 room⟩

end
end Hierarchy.DescentDatedAddressBook.SignedPrefix

end OAI
