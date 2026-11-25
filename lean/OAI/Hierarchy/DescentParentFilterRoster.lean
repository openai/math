import OAI.Hierarchy.DescentParentFilterSource
import OAI.Hierarchy.DescentParallelTapeOrder
import OAI.Hierarchy.DescentHaloParentRoster
import OAI.Hierarchy.DescentPackedOperandStreamSerial

namespace OAI
/-! # Build the operand stream roster from the two rooted cable endpoint records -/
namespace Hierarchy.DescentParallelBase.ParentFilter
open DescentSharedCableNames DescentHaloWalkRAM DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
  {n D H Q O K L : ℕ} {B : Ends U n} (C : Blocks B E)
local notation "P" => breadth D
variable (R : Fin H→Fin D→Option (Fin H)) (symm : ∀v u i,R v i=some u→∃j,R u j=some v)

/-- The previous step's live raw donor rows, the measured normalized site
addresses, and actual physical post-grouping chronology. -/
structure Measured (C : Blocks B E) (R : Fin H→Fin D→Option (Fin H)) (X T V : Type) [Fintype X] [Fintype T] (Q O K L : ℕ) where
  venue : U→Fin H×Fin Q
  raw : ∀h,Local C h↪X
  loc : X↪Fin H×Fin O
  read : ∀h,Local C h→Source (breadth D) Q K L
  reached : ∀h e,Witness R (loc (raw h e)).1 (read h e) (venue (C.src e.val)) (venue (C.dst e.val))
  otherInj : ∀h (e f : Local C h),venue (other C h e)=venue (other C h f) → other C h e=other C h f
  survives : ∀h e,(read h e).weight.val=C.count e.val
  tape : Tape T
  site : V↪ℕ
  src : T→V
  dst : T→V
  width : T→ℕ
  head : ∀h,Local C h→T
  active : ∀h e,0<width (head h e)
  orientation : ∀h e,(read h e).upper=side site (src (head h e)) (dst (head h e))
  samePair : ∀h e f,other C h e=other C h f→
    (src (head h e)=src (head h f) ∧ dst (head h e)=dst (head h f)) ∨ (src (head h e)=dst (head h f) ∧ dst (head h e)=src (head h f))
  shortTicket : ∀h e f,src (head h e)=src (head h f)→
    (tape.sourceKey src site width (head h e)<tape.sourceKey src site width (head h f) ↔ (read h e).ticket<(read h f).ticket)
  chronology : ∀h e f,C.first e.val<C.first f.val ↔ tape.sourceKey src site width (head h e)<tape.sourceKey src site width (head h f)

namespace Measured
variable (Z : Measured C R X T V Q O K L)

variable {C R} in
def old (h : U) (e : Local C h):=(Z.loc (Z.raw h e)).1

include symm in
omit [Fintype E] in
theorem near (h : U) (e : Local C h) : ∃j,Gather.reaching R (Z.venue h).1 j=some (Z.old h e) :=by
  have truth:=Z.reached h e
  rcases e.property.2 with src|dst
  · obtain ⟨q,back,_,_⟩:=Rebase.actual R symm _ _ _ truth.src
    rw [src] at back;exact ⟨q,back⟩
  · obtain ⟨q,back,_,_⟩:=Rebase.actual R symm _ _ _ truth.dst
    rw [dst] at back;exact ⟨q,back⟩

local notation "host" => (fun v => Prod.fst (Z.venue v))

def visit (h : U) (e : Local C h) :=Resident.visit C h host Z.loc (Z.raw h) (Gather.reaching R) (near C R symm Z h) e

omit [Fintype E] in
theorem fromOld (h : U) (e : Local C h):Gather.reaching R (host h) (visit C R symm Z h e)=some (Z.old h e):=by
  have read:=Resident.visit_read C h host Z.loc (Z.raw h) (Gather.reaching R) (near C R symm Z h) e
  unfold Gather.select at read;split at read <;> first | contradiction | exact read

variable {C R} in
def otherEnd (h : U) (e : Local C h) : Endpoint P Q:=if C.src e.val=h then (Z.read h e).dst else (Z.read h e).src

variable {C R} in
omit [Fintype E] in
theorem otherFields (h : U) (e : Local C h) :
    Gather.reaching R (Z.old h e) (Z.otherEnd h e).path=some (Z.venue (other C h e)).1 ∧
      (Z.otherEnd h e).low=(Z.venue (other C h e)).2 :=by
  have read:=Z.reached h e
  by_cases src:C.src e.val=h
  · simpa [otherEnd,other,old,src] using And.intro read.dst read.dstLow
  · simpa [otherEnd,other,old,src] using And.intro read.src read.srcLow

def entry (h : U) (e : Local C h) : Entry (P*P*Q) K L:=
  ⟨peer R (host h) (visit C R symm Z h e) (Z.otherEnd h e),(Z.read h e).upper,(Z.read h e).ticket,(Z.read h e).weight⟩

omit [Fintype E] in
theorem samePeer (h : U) (e f : Local C h) : (entry C R symm Z h e).peer=(entry C R symm Z h f).peer ↔ other C h e=other C h f:=by
  have a:=Z.otherFields h e;have b:=Z.otherFields h f
  exact (peer_iff R _ _ _ _ _ _ _ _ _ (fromOld C R symm Z h e) (fromOld C R symm Z h f) a.1 b.1 a.2 b.2).trans
    ⟨Z.otherInj _ _ _,congrArg Z.venue⟩

omit [Fintype E] in
theorem readOrder (h : U) (e f : Local C h) (pair : other C h e=other C h f) :
    priority (entry C R symm Z h e)<priority (entry C R symm Z h f) ↔ C.first e.val<C.first f.val :=by
  exact (ticket_compare Z.tape Z.src Z.dst Z.site Z.width (Z.head h e) (Z.head h f) _ _ (Z.active h e) (Z.active h f) (Z.samePair h e f pair)
    (Z.orientation h e) (Z.orientation h f) (Z.shortTicket h e f)).trans (Z.chronology h e f).symm

def roster : DescentPackedOperand.Public.Roster C (P*P*Q) K L (P*O) where
  address h:=Resident.address C h host Z.loc (Z.raw h) (Gather.reaching R) (near C R symm Z h)
  entry:=entry C R symm Z
  peer:=samePeer C R symm Z
  order:=readOrder C R symm Z
  weight:=Z.survives

omit [Fintype E] in
/-- At an actual current end the native orientation and the scalar four-hop
matching test select the same other physical endpoint and copy the same
source ticket/weight. The injectivity premise is the current endpoint's
old common group and remaining block chart. -/
theorem local_output (h : U) (e : Local C h)
    (atSrc : Z.venue h=Z.venue (C.src e.val)→h=C.src e.val) :
    filter R (Z.venue h) (visit C R symm Z h e) (Z.old h e) (Z.read h e)=some (entry C R symm Z h e):=by
  rw [accepted R symm _ _ _ _ _ _ (fromOld C R symm Z h e) (Z.reached h e)]
  rw [ite_eq_right (show (Z.read h e).weight.val≠0 by rw [Z.survives];exact e.property.1.ne')]
  by_cases src:C.src e.val=h
  · simp [src,entry,otherEnd]
  · have dst: C.dst e.val=h:=e.property.2.resolve_left src
    have diff:Z.venue h≠Z.venue (C.src e.val):=fun eqn=>src (atSrc eqn).symm
    simp [dst,diff,entry,otherEnd,src]

/-- Installed before receiver filtering, one previous-group donor shelf at
its actual physical raw slot. Positive source rows have true endpoints and
one genuinely surviving normalized parent, wherever those endpoints are.
Zero-weight (trimmed, internal, or empty) sources can remain on the shelf. -/
structure Shelf (Z : Measured C R X T V Q O K L) where
  issued : U→X→Option (Source P Q K L)
  covers : ∀h e,issued h (Z.raw h e)=some (Z.read h e)
  proper : ∀h x r,issued h x=some r→0<r.weight.val→∃e:E,0<C.count e ∧
    Witness R (Z.loc x).1 r (Z.venue (C.src e)) (Z.venue (C.dst e)) ∧
    (Z.venue h=Z.venue (C.src e)→h=C.src e) ∧ (Z.venue h=Z.venue (C.dst e)→h=C.dst e) ∧
    ∀(ends:C.src e=h ∨ C.dst e=h)(positive:0<C.count e),Z.raw h ⟨e,positive,ends⟩=x

/-- Evaluate the real bank for this public path and prior allocated raw role. -/
def deposited (S : Shelf C R Z) (h : U) (p : Fin P) (x : X) : Option (Entry (P*P*Q) K L) :=
  (S.issued h x).bind (filter R (Z.venue h) p (Z.loc x).1)

theorem all_raw (S : Shelf C R Z) (h : U) (p : Fin P) (x : X) (selected : Gather.select (Gather.reaching R) (host h) p=some (Z.loc x).1) :
    deposited C R Z S h p x=Resident.localRaw C h (Z.raw h) (entry C R symm Z h) x :=by
  have reached : Gather.reaching R (host h) p=some (Z.loc x).1:=by unfold Gather.select at selected;split at selected <;> first | contradiction | exact selected
  by_cases attached:∃e:Local C h,Z.raw h e=x
  · obtain ⟨e,rfl⟩:=attached;rw [Resident.live,deposited,S.covers,Option.bind_some]
    have once:=Gather.once (Gather.reaching R) (host h) (Z.old h e) (near C R symm Z h e)
    have equal:p=visit C R symm Z h e:=once.unique selected (Resident.visit_read C h host Z.loc (Z.raw h) (Gather.reaching R) (near C R symm Z h) e)
    rw [equal]
    have liveR:0<(Z.read h e).weight.val:=by rw [Z.survives];exact e.property.1
    obtain ⟨u,up,actual,injectS,injectT,back⟩:=S.proper h (Z.raw h e) (Z.read h e) (S.covers h e) liveR
    have wt:=Z.reached h e
    have srcEq : Z.venue (C.src u)=Z.venue (C.src e.val):=Prod.ext (Option.some.inj (actual.src.symm.trans wt.src)) (actual.srcLow.symm.trans wt.srcLow)
    have dstEq : Z.venue (C.dst u)=Z.venue (C.dst e.val):=Prod.ext (Option.some.inj (actual.dst.symm.trans wt.dst)) (actual.dstLow.symm.trans wt.dstLow)
    have incident:C.src u=h ∨ C.dst u=h:=by
      rcases e.property.2 with src|dst
      · exact Or.inl (injectS (by rw [srcEq,src])).symm
      · exact Or.inr (injectT (by rw [dstEq,dst])).symm
    have same : u=e.val:=congrArg Subtype.val ((Z.raw h).injective (back incident up))
    exact local_output C R symm Z h e (by simpa only [same] using injectS)
  · rw [Resident.localRaw,dite_eq_right attached,deposited]
    cases issued:S.issued h x with
    | none=>rfl
    | some r=>
      change filter R (Z.venue h) p (Z.loc x).1 r=none
      by_cases empty:r.weight.val=0
      · simp [filter,empty]
      · obtain ⟨u,up,proved,src,dst,orig⟩:=S.proper h x r issued (Nat.pos_of_ne_zero empty)
        have ns:Z.venue h≠Z.venue (C.src u):=by intro eqn;let hi: C.src u=h:=(src eqn).symm;exact attached ⟨⟨u,up,Or.inl hi⟩,orig (Or.inl hi) up⟩
        have nt:Z.venue h≠Z.venue (C.dst u):=by intro eqn;let hi:C.dst u=h:=(dst eqn).symm;exact attached ⟨⟨u,up,Or.inr hi⟩,orig (Or.inr hi) up⟩
        rw [accepted R symm _ _ _ _ _ _ reached proved];simp [empty,ns,nt]

theorem literal_all (S : Shelf C R Z) (h : U) :
    Resident.collected h host Z.loc (Gather.reaching R) (deposited C R Z S h)=place ((roster C R symm Z).address h) ((roster C R symm Z).entry h) :=
  Resident.entire_at C h host Z.loc (Z.raw h) (Gather.reaching R) (near C R symm Z h) _ _ (all_raw C R symm Z S h)

end Measured
end
end Hierarchy.DescentParallelBase.ParentFilter

end OAI
