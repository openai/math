import OAI.Hierarchy.DescentOrdinaryFinalLaw

namespace OAI
/-! The private alias in an ordinary operand is the least occupied rectangular
argument referring to that very p-word. Public and inactive entries are excluded. -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentPackedOperand DescentOperandStateBanks DescentKernelHistory DescentLocalPrivateNames
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

variable (B : DescentOrdinaryFinal.Chart) {Tag Port : Type} (r : Recipe Tag Port)
  (node : r.Node ↪ Fin B.layout.nodes) (arityFit : ∀u,r.arity u≤B.layout.operands)

def mouth (s : Slot r) : Fin B.keys := B.slots (node s.1,s.2.castLE (arityFit s.1))

def mouths : Slot r ↪ Fin B.keys where
  toFun := B.mouth r node arityFit
  inj' := by
    rintro ⟨u,j⟩ ⟨v,k⟩ eqn
    have mates := B.slots.injective eqn
    have same : u=v := node.injective (congrArg Prod.fst mates)
    subst v
    have digit_ := congrArg (fun p : Fin B.layout.nodes × Fin B.layout.operands => p.2.val) mates
    exact congrArg (Sigma.mk u) (Fin.ext digit_)

local notation "idx" => B.mouths r node arityFit
variable (x : B.Input)
  (count : ∀u,B.arity x (node u)=r.arity u)
  (absent : ∀n,(∀u,node u≠n)→B.arity x n=0)

include count in
theorem mouth_live (s : Slot r) : B.live x (idx s) := by
  change (B.slots.symm (B.slots _)).2.val < B.arity x (B.slots.symm (B.slots _)).1
  simpa only [Equiv.symm_apply_apply,Fin.val_castLE,count] using s.2.isLt

include count absent in
theorem live_image (i : Fin B.keys) : B.live x i ↔ ∃s,idx s=i := by
  constructor
  · obtain ⟨⟨n,a⟩,rfl⟩:=B.slots.surjective i
    intro live
    change (B.slots.symm (B.slots (n,a))).2.val<B.arity x (B.slots.symm (B.slots (n,a))).1 at live
    simp only [Equiv.symm_apply_apply] at live
    by_cases found : ∃u,node u=n
    · obtain ⟨u,rfl⟩:=found
      rw [count] at live
      exact ⟨⟨u,⟨a.val,live⟩⟩,rfl⟩
    · have zero:=absent n (fun u e=>found ⟨u,e⟩)
      omega
  · rintro ⟨s,rfl⟩
    exact B.mouth_live r node arityFit x count s

private theorem same_word {k : ℕ} (a b : Fragment k) :
    (word a).val=(word b).val ↔ resolve a=resolve b := by
  constructor
  · intro e
    apply Key.fields_injective
    funext j
    rw [←word_read a j,←word_read b j,e]
  · intro e
    simp only [word,e]

/-- All requirements on the pre-renaming key are individual occurrence reads.
The chart's comparison of all keys, padding, and the final first-use alias are derived. -/
structure Occurrences (fragment : Slot r → Fragment B.layout.size)
    (hidden : r.UsedWord ↪ Key) : Prop where
  stamp : ∀s,B.stamp x (idx s)=(word (fragment s)).val
  privateKey : ∀s h,DescentLocalPrivateNames.read r s=some h → resolve (fragment s)=hidden h
  privateTag : ∀h,(hidden h).fields 0<3
  publicTag : ∀s,DescentLocalPrivateNames.read r s=none → 3≤(resolve (fragment s)).fields 0

variable {frag : Slot r→Fragment B.layout.size} {hidden : r.UsedWord↪Key}
  (seen : B.Occurrences r node arityFit x frag hidden)

include count seen in
private theorem mark_private (s : Slot r) (h : r.UsedWord) (hit : DescentLocalPrivateNames.read r s=some h) :
    (B.marked x (idx s)).val=1+(word (frag s)).val := by
  have tag : digit (B.layout.size+4) 0 (B.stamp x (idx s))<3 := by
    have head := word_read (frag s) (0 : Fin 5)
    rw [seen.stamp]
    exact head.le.trans_lt (by rw [seen.privateKey s h hit];exact seen.privateTag h)
  rw [B.marked_key x _ (B.mouth_live r node arityFit x count s) tag,seen.stamp]

include seen in
private theorem mark_public (s : Slot r) (hit : DescentLocalPrivateNames.read r s=none) :
    B.marked x (idx s)=0 := by
  have tag : ¬digit (B.layout.size+4) 0 (B.stamp x (idx s))<3 := by
    rw [seen.stamp]
    have head := word_read (frag s) (0 : Fin 5)
    exact Nat.not_lt.mpr ((seen.publicTag s hit).trans head.ge)
  simp [marked,tag]

include count absent seen in
theorem marked_alias (s : Slot r) (h : r.UsedWord) (hit : DescentLocalPrivateNames.read r s=some h) :
    renameDigit (B.marked x) (idx s)=1+(firstAlias r idx h).val := by
  let a:=idx s
  have positive : 0<(B.marked x a).val:=by
    change 0<(B.marked x (idx s)).val
    rw [B.mark_private r node arityFit x count seen s h hit]
    omega
  have nonzero : B.marked x a≠0:=fun e=>by simp [e] at positive
  have related (j : Fin B.keys) :
      B.marked x j=B.marked x a ↔ ∃t,idx t=j ∧ DescentLocalPrivateNames.read r t=some h := by
    constructor
    · intro same
      have live:B.live x j:=by
        by_contra inactive
        exact nonzero (same.symm.trans (by simp [marked,inactive]))
      obtain ⟨t,rfl⟩:=(B.live_image r node arityFit x count absent j).1 live
      cases e : DescentLocalPrivateNames.read r t with
      | none => exact False.elim (nonzero (same.symm.trans (B.mark_public r node arityFit x seen t e)))
      | some h' =>
        have eqv:=congrArg Fin.val same
        change (B.marked x (idx t)).val=(B.marked x (idx s)).val at eqv
        rw [B.mark_private r node arityFit x count seen t h' e,
          B.mark_private r node arityFit x count seen s h hit] at eqv
        have keys:=(same_word (frag t) (frag s)).1 (Nat.add_left_cancel eqv)
        rw [seen.privateKey t h' e,seen.privateKey s h hit] at keys
        exact ⟨t,rfl,e.trans (congrArg some (hidden.injective keys))⟩
    · rintro ⟨t,rfl,tHit⟩
      apply Fin.ext
      change (B.marked x (idx t)).val=(B.marked x (idx s)).val
      rw [B.mark_private r node arityFit x count seen t h tHit,
        B.mark_private r node arityFit x count seen s h hit]
      exact congrArg (1+·) ((same_word ..).2 ((seen.privateKey t h tHit).trans (seen.privateKey s h hit).symm))
  let matchingSlots:=Finset.univ.filter (fun j=>B.marked x j=B.marked x a)
  have present : matchingSlots.Nonempty:=⟨a,by simp [matchingSlots]⟩
  have least : matchingSlots.min' present=firstAlias r idx h := by
    apply le_antisymm
    · apply Finset.min'_le
      obtain ⟨t,index,href⟩:=firstAlias_read r idx h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(related _).2 ⟨t,index,href⟩⟩
    · have member:=Finset.min'_mem matchingSlots present
      obtain ⟨t,place,href⟩:=(related _).1 (Finset.mem_filter.mp member).2
      rw [←place]
      exact firstAlias_le r idx t h href
  change renameDigit (B.marked x) a=_
  rw [renameDigit,ite_eq_right nonzero]
  exact congrArg (fun j : Fin B.keys=>1+j.val) least

include count absent seen in
theorem private_header (s : Slot r) (h : r.UsedWord) (hit : DescentLocalPrivateNames.read r s=some h)
    (f : Fin 4) (fits : (Pointer.privateWord (firstAlias r idx h).val).header f<2^B.field) :
    digit B.field (node s.1).val
      (B.law (B.pages (f.castLE (by decide),s.2.castLE (arityFit s.1))) x).val=
      (Pointer.privateWord (firstAlias r idx h).val).header f := by
  have renamed:=B.marked_alias r node arityFit x count absent seen s h hit
  have proj : Pointer.ofKey (renameDigit (B.marked x) (idx s)-1) (resolve (frag s))=
      Pointer.privateWord (firstAlias r idx h).val := by
    rw [renamed,seen.privateKey s h hit]
    have priv:=seen.privateTag h
    cases e:hidden h <;> simp [Pointer.ofKey,Key.fields,e] at priv ⊢
  exact (B.header f _ _ x (B.mouth_live r node arityFit x count s) _ (seen.stamp s)
    (proj.symm ▸ fits)).trans (congrArg (fun t : Pointer=>t.header f) proj)

include count seen in
theorem public_header (s : Slot r) (hit : DescentLocalPrivateNames.read r s=none)
    (f : Fin 4) (fits : (Pointer.ofKey 0 (resolve (frag s))).header f<2^B.field) :
    digit B.field (node s.1).val
      (B.law (B.pages (f.castLE (by decide),s.2.castLE (arityFit s.1))) x).val=
      (Pointer.ofKey 0 (resolve (frag s))).header f := by
  have proj : Pointer.ofKey (renameDigit (B.marked x) (idx s)-1) (resolve (frag s))=
      Pointer.ofKey 0 (resolve (frag s)) := by
    have pub:=seen.publicTag s hit
    cases e : resolve (frag s) <;> simp [Pointer.ofKey,Key.fields,e] at pub ⊢
  exact (B.header f _ _ x (B.mouth_live r node arityFit x count s) _ (seen.stamp s)
    (proj.symm ▸ fits)).trans (congrArg (fun t : Pointer=>t.header f) proj)

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
