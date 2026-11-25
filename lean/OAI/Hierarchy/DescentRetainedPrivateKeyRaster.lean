import OAI.Hierarchy.DescentReachedRetainedPrivateBook
import OAI.Hierarchy.DescentReachedPointerAlias
import OAI.Hierarchy.DescentRetainedMovedHeaders

namespace OAI
/-! Private-key readback and zero padding on the full measured retained rectangle. -/
namespace Hierarchy.DescentRetainedPrivateSlotBook
open DescentKernelHistory DescentLocalPrivateNames DescentSIMDLookup DescentOperandStateBanks
open DescentRetainedControl DescentRetainedRangeDigits DescentPackedResetDonors DescentResetRetainedSetup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {T U A I : Type} {P : I→Type} {r : Recipe T A} {src : ∀i,Recipe U (P i)}
  (orig : Donors r src) (C : DescentResetOperandSetup.Chart)
local notation "L" => C.retained
variable (which : C.seven.control.Targets) (X : C.seven.Packets) (panels : (L).Strips)
  (t : Fin C.placement.shapes) (h : Fin (L).hosts) (g : Fin (L).grouped)
local notation "accept" => ownerAt C which X t h g
local notation "prior" => priorAt C X h g
local notation "before" => (L).site panels h g
local notation "out" => (L).routedWord accept prior before
variable (order : Fin (L).donors≃Fin (L).donors) (rank : ∀d,neighbors prior d=(order d).val)
  (donor : I↪Fin (L).donors) (node : ∀i,(src i).Node→Fin (L).previousNodes)
  (arity : ∀i n,(src i).arity n≤(L).previousArgs)
  (place : Slot r↪Fin ((L).nodes*(L).args))
local notation "native" q:arg => orig.slots q
local notation "i_" q:arg => (native q).1
local notation "n_" q:arg => node (i_ q) (native q).2.1
local notation "j_" q:arg => (native q).2.2.castLE (arity _ _)
local notation "d_" q:arg => donor (i_ q)
local notation "pair" z:arg => (finProdFinEquiv.symm (z:Fin ((L).nodes*(L).args)) : Fin (L).nodes×Fin (L).args)
local notation "old" q:arg f:arg => (L).entry before (d_ q) (n_ q) ((L).operandField f (j_ q))
variable (issued : ∀q:Slot r,accept (d_ q)=true ∧ (n_ q).val<(L).originalCount before (d_ q) ∧
    (j_ q).val<((L).entry before (d_ q) (n_ q) (L).arityField).val ∧
    (pair (place q)).1.val=(L).offset out (order (d_ q))+(n_ q).val ∧ (pair (place q)).2.val=(j_ q).val)
variable (covered : ∀(d : Fin (L).donors) (n : Fin (L).previousNodes) (j : Fin (L).previousArgs),accept d=true→n.val<(L).originalCount before d→
    j.val<((L).entry before d n (L).arityField).val→∃q:Slot r,d_ q=d ∧ n_ q=n ∧ j_ q=j)
variable {K:ℕ} (slots : ∀i,Slot (src i)↪Fin K) (fit : K≤2^(L).bits)
variable (ptr : Slot r→Pointer)
  (archive : ∀(q:Slot r)(f:Fin 4),(old q (f.castLE (by decide:4≤7))).val=(ptr q).header f)
  (privateSource : ∀q:Slot r,(ptr q).privateIndex=(read (src (i_ q)) (native q).2).map
    (fun u=>(firstAlias _ (slots _) u).val))
local notation "key" => orig.key (donor.trans order.toEmbedding) slots fit

include issued rank archive privateSource in
theorem key_on_real (q : Slot r) :
    (L).keyIndex out (place q)=(read r q).map key:=by
  obtain ⟨yes,live,active,site,arg⟩:=issued q
  have count: (L).originalCount out (order (d_ q))=(L).originalCount before (d_ q):=by
    simp only [(L).routed_count accept prior order rank before (d_ q),yes,ite_true]
  have digit (f:Fin (L).fields) : (L).entry out (order (d_ q)) (n_ q) f=(L).entry before (d_ q) (n_ q) f:=by
    simp only [(L).routed_entry accept prior order rank before (d_ q) (n_ q) f,yes,ite_true]
  have original : (read r q).map key=(ptr q).privateIndex.map
      (fun (n : ℕ)=>(order (d_ q),(n:Cell (L).bits))):=by
    rw [privateSource,Option.map_map]
    exact orig.key_slot (donor.trans order.toEmbedding) slots fit q
  rw [original]
  change (L).keyAt out (pair (place q)).1.val (pair (place q)).2.val=_
  rw [site,arg,(L).original_key out (order (d_ q)) (n_ q) (j_ q) (count.symm ▸ live) ((digit _).symm ▸ active),digit,digit]
  have tag:=archive q 0
  have label:=archive q 2
  change (old q (0:Fin 7)).val=(ptr q).header 0 at tag
  change (old q (2:Fin 7)).val=(ptr q).header 2 at label
  cases e:ptr q with
  | privateWord name=>
    rw [e] at tag label
    change (old q (0:Fin 7)).val=0 at tag
    change (old q (2:Fin 7)).val=name at label
    simp only [tag,ite_true,Pointer.privateIndex,Option.map_some]
    apply congrArg (fun z=>some (order (d_ q),z))
    apply Fin.ext
    simp only [←label,Fin.val_cast_of_lt (old q (2:Fin 7)).isLt]
  | pin name chunk=>
    rw [e] at tag
    change (old q (0:Fin 7)).val=2 at tag
    simp [tag,Pointer.privateIndex]
  | cable peer wire chunk=>
    rw [e] at tag
    change (old q (0:Fin 7)).val=1 at tag
    simp [tag,Pointer.privateIndex]

include issued covered rank in
theorem key_on_padding (p : Fin ((L).nodes*(L).args)) (vacant : ∀q,place q≠p) :
    (L).keyIndex out p=none:=by
  cases real:(L).keyIndex out p with
  | none=>rfl
  | some k=>
    have earlier:=(moved_earlier_key_iff C which X panels t h g order rank (pair p).1.val (pair p).2.val k).1 real
    obtain ⟨d,n,j,yes,active,used,offset,arg,_,_⟩:=earlier
    obtain ⟨q,dOld,nOld,jOld⟩:=covered d n j yes active used
    obtain ⟨_,_,_,first,second⟩:=issued q
    rw [dOld,nOld] at first
    rw [jOld] at second
    exact False.elim (vacant q (finProdFinEquiv.symm.injective
      (Prod.ext (Fin.ext (first.trans offset.symm)) (Fin.ext (second.trans arg.symm)))))

end
end Hierarchy.DescentRetainedPrivateSlotBook

end OAI
