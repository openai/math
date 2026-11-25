import OAI.Hierarchy.TaggedWirePacketNeighbor
import OAI.Hierarchy.TaggedWideCarried
import OAI.Hierarchy.TaggedWideRoleScatter

namespace OAI
/-! # Each positive historical row recovers its true degree slot in the expanded port partition -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketNeighbor
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged PassiveWindow ProtocolRAM AdaptiveProbe
open scoped Classical
variable {S n D K : ℕ} {H : Type} (ends : Fin n→Chord S) (bits : Fin n→ℕ)
    (port : Fin n×Bool ↪ H) (slot : H ↪ Fin (S*D))
    (here : ∀i b,(finProdFinEquiv.symm (slot (port (i,b)))).1=(portGraph S).vertex (ends i) b)
    (s : Fin S)

def localSlot : EndsAt ends bits s ↪ Fin D where
  toFun p:=(finProdFinEquiv.symm (slot (port p.val.val))).2
  inj' a b same:=by
    have atA : (finProdFinEquiv.symm (slot (port a.val.val))).1=s :=
      (here _ _).trans (by cases a with | mk v pos => rcases v with ⟨⟨i,b⟩,h⟩;cases b <;>exact h)
    have atB : (finProdFinEquiv.symm (slot (port b.val.val))).1=s :=
      (here _ _).trans (by cases b with | mk v pos => rcases v with ⟨⟨i,b⟩,h⟩;cases b <;>exact h)
    exact Subtype.ext (Subtype.ext (port.injective (slot.injective
      (finProdFinEquiv.symm.injective (Prod.ext (atA.trans atB.symm) same)))))

local notation "seat" => localSlot ends bits port slot here s
variable (bound : ∀i,bits i≤K) {total : Widths S} (shape : installedWidths ends bits=total)
local notation "parts" => carried ends bits s bound seat shape
local notation "addr" => fun q:Fin D=>finProdFinEquiv (s,q)

theorem local_addr (a : EndsAt ends bits s) : slot (port a.val.val)=addr (seat a) := by
  apply finProdFinEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  apply Prod.ext
  · refine (here a.val.val.1 a.val.val.2).trans ?_
    rcases a with ⟨⟨⟨i,b⟩,h⟩,pos⟩;cases b <;>exact h
  · rfl

theorem local_owner (a : EndsAt ends bits s) : (parts).owner (seat a)=some (byRow ends bits s a) := by
  cases shape
  change Function.extend seat (fun x => some (byRow ends bits s x)) (fun _ => none) (seat a) = _
  rw [(seat).injective.extend_apply]

theorem local_width (a : EndsAt ends bits s) : (parts).width (seat a)=bits a.val.val.1 := by
  cases shape
  change Function.extend seat (fun x => bits x.val.val.1) (fun _ => 0) (seat a) = _
  rw [(seat).injective.extend_apply]

theorem local_blank (q : Fin D) (miss : ¬∃a : EndsAt ends bits s,seat a=q) : (parts).owner q=none := by
  cases shape
  change Function.extend seat (fun x => some (byRow ends bits s x)) (fun _ => none) q = none
  exact Function.extend_apply' _ _ _ miss

theorem width_at (q : Fin D) :
    RoleWidths.shelf port slot (fun a=>bits a.1) (addr q)=amount parts q := by
  by_cases hit:∃a : EndsAt ends bits s,seat a=q
  · obtain ⟨a,rfl⟩:=hit
    rw [←local_addr ends bits port slot here s a,RoleWidths.shelf_live]
    rw [amount,local_owner,Option.elim_some,local_width]
  · have blank:=local_blank ends bits port slot here s bound shape q hit
    rw [amount,blank,Option.elim_none]
    by_cases found:∃a,slot (port a)=addr q
    · obtain ⟨⟨i,b⟩,eq⟩:=found
      rw [←eq,RoleWidths.shelf_live]
      by_contra live
      have pair:=congrArg finProdFinEquiv.symm eq
      rw [Equiv.symm_apply_apply] at pair
      have site : (portGraph S).vertex (ends i) b=s:=(here i b).symm.trans (congrArg Prod.fst pair)
      let a : EndsAt ends bits s:=⟨⟨(i,b),by cases b <;>exact site⟩,Nat.pos_of_ne_zero live⟩
      exact hit ⟨a,congrArg Prod.snd pair⟩
    · exact Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using found)

theorem other_at (q : Fin D) (p : (portGraph S).Port s) (owns : (parts).owner q=some p)
    (opposite : Fin n×Bool→ℕ)
    (read : ∀i b,0<bits i→ opposite (i,b)=((portGraph S).vertex (ends i) (!b)).val) :
    RoleWidths.shelf port slot opposite (addr q)=(other p).val := by
  by_cases hit:∃a : EndsAt ends bits s,seat a=q
  · obtain ⟨a,rfl⟩:=hit
    have own : byRow ends bits s a=p := by
      exact Option.some.inj ((local_owner ends bits port slot here s bound shape a).symm.trans owns)
    rw [←local_addr ends bits port slot here s a,RoleWidths.shelf_live,←own]
    exact read _ _ a.property
  · have blank:=local_blank ends bits port slot here s bound shape q hit
    rw [blank] at owns;contradiction

end Hierarchy.WireTelescope.PacketNeighbor

end
end OAI
