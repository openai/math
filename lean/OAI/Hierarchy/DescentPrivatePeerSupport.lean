import OAI.Hierarchy.DescentPrivateCandidateShelf
import OAI.Hierarchy.DescentResetPrivatePeerChip
import OAI.Hierarchy.DescentResetPeerIssued

namespace OAI
/-! # Exact unfiltered peer tickets of the chronological private-device ROM -/
namespace Hierarchy.DescentResetPeerUnionRAM.PrivateEvidence
open DescentResetPeerUnionRAM
open scoped Classical

private theorem self_read {H W D : ℕ} (peers : Fin H→Fin D→Option (Fin H))
    (old : Fin H) (v q : Fin W) (target : Fin (H*W)) :
    (∃j : Fin (Candidates.count W D),Candidates.candidate peers (finProdFinEquiv (old,v)) j=some target ∧
      D*W+q.val+1=j.val+1) ↔ target=finProdFinEquiv (old,q) := by
  let slot := Candidates.atSlot (Fin.last D) q
  have valEq : slot.val=D*W+q.val:=Candidates.atSlot_val _ _
  have found := Candidates.selfKey peers old v q
  constructor
  · rintro ⟨j,read,number⟩
    have same : j=slot:=Fin.ext (by omega)
    rw [same,found] at read
    exact (Option.some.inj read).symm
  · rintro rfl
    exact ⟨slot,found,by omega⟩

theorem ticket_read {H W D : ℕ} (peers : Fin H→Fin D→Option (Fin H)) (old : Fin H)
    (here source target : Fin W) (next : Fin (H*W)) (row : Fin 5→ℕ)
    (flag : row 0=1) (src : row 1=source.val) (dst : row 2=target.val) :
    (∃j : Fin (Candidates.count W D),Candidates.candidate peers (finProdFinEquiv (old,here)) j=some next ∧
      ticket D W here.val row=j.val+1) ↔
      (source=here ∧ next=finProdFinEquiv (old,target)) ∨ (target=here ∧ next=finProdFinEquiv (old,source)) := by
  by_cases hs : source=here
  · subst source
    simp only [ticket,flag,src,dst,ite_true,self_read,true_and]
    by_cases ht : target=here
    · subst target;simp
    · simp [ht]
  · have noValue : source.val≠here.val:=fun eq=>hs (Fin.ext eq)
    by_cases ht : target=here
    · subst target
      simpa [ticket,flag,src,dst,noValue,hs] using (self_read peers old here source next)
    · have noTarget : target.val≠here.val:=fun eq=>ht (Fin.ext eq)
      simp [ticket,flag,src,dst,noValue,noTarget,hs,ht]

end Hierarchy.DescentResetPeerUnionRAM.PrivateEvidence
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentSharedCableNames DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) height

open DescentResetPeerUnionRAM

/-- Each raw private row contributes its other endpoint to the self-root arm
of the native peer directory. Rows from all common blocks use this same
unsigned relation, including contacts with no positive-width copy. -/
theorem private_ticket_support {H D₀ count : ℕ} (prev : Fintype.card input.V≤H)
    (peers : Fin H→Fin D₀→Option (Fin H)) (old : Fin (Fintype.card input.V))
    (here : Fin (pool).card) (next : Fin (H*(pool).card)) (block : Block (T).commonDepth)
    (s : Bool) (ticket : (Z).RootTicket T) (slot : Fin capacity) (raw : Fin 5→ℕ)
    (unit : 0<(Z).unit) (panel : (Z).Fallback→DescentPackedFallbackTree.Panel height count)
    (numbers : raw=DescentPackedPrivateMenu.values (Z).graph ((Z).k-(T).commonDepth) height count (Z).layerBits C (Z).width s slot.val
      ((Z).rootsOf T vertexCode unit s panel ticket old block))
    (installed : ∀p : PrivateOccurrence B,privateRawAt B old block s ticket slot p →
      (Z).expand T vertexCode p.1.2 raw=(Z).actualRecord T vertexCode (privateWire B p)) :
    let v:=finProdFinEquiv (old.castLE prev,here)
    (∃j : Fin (Candidates.count (pool).card D₀),Candidates.candidate peers v j=some next ∧
      PrivateEvidence.ticket D₀ (pool).card here.val raw=j.val+1) ↔
    ∃p,privateRawAt B old block s ticket slot p ∧ rawPeer B (privateWire B p) v.val next.val := by
  intro v
  obtain ⟨flag,blank,coords⟩:=private_raw_presence B unit s ticket old block slot panel raw numbers installed
  have each (p : PrivateOccurrence B) (atSlot : privateRawAt B old block s ticket slot p) :
      (∃j : Fin (Candidates.count (pool).card D₀),Candidates.candidate peers v j=some next ∧
        PrivateEvidence.ticket D₀ (pool).card here.val raw=j.val+1) ↔ rawPeer B (privateWire B p) v.val next.val := by
    let left:=((Z).hostFields T vertexCode ((blocks B).src (privateWire B p)).1.2).2
    let right:=((Z).hostFields T vertexCode ((blocks B).dst (privateWire B p)).1.2).2
    have first:=flag.2 ⟨p,atSlot⟩
    have parent : vertexCode ((Z).rootVertex T p.1.2)=old:=congrArg Prod.fst atSlot.2.1
    have low:=coords p atSlot
    rw [PrivateEvidence.ticket_read peers _ here left right next raw first low.1 low.2]
    unfold rawPeer incidentWords
    rw [←installed p atSlot]
    have leftVal : raw 1=left.val:=low.1
    have rightVal : raw 2=right.val:=low.2
    let row:=(Z).expand T vertexCode p.1.2 raw
    let base:=(pool).card*old.val
    have flagWord : row 0=1:=by simp [row,ResetInput.expand,first]
    have srcWord : row 1=left.val+base:=by simp [row,ResetInput.expand,first,leftVal,parent,base]
    have dstWord : row 2=right.val+base:=by simp [row,ResetInput.expand,first,rightVal,parent,base]
    change _ ↔ row 0=1 ∧ ((row 1=v.val ∧ row 2=next.val) ∨ (row 2=v.val ∧ row 1=next.val))
    rw [flagWord,srcWord,dstWord]
    have pairVal (shape : Fin (pool).card) : (finProdFinEquiv (old.castLE prev,shape)).val=shape.val+base:=rfl
    constructor
    · rintro (⟨l,rfl⟩|⟨r,rfl⟩)
      · exact ⟨rfl,Or.inl ⟨(congrArg (fun t : Fin (pool).card=>t.val+base) l).trans (pairVal here).symm,(pairVal right).symm⟩⟩
      · exact ⟨rfl,Or.inr ⟨(congrArg (fun t : Fin (pool).card=>t.val+base) r).trans (pairVal here).symm,(pairVal left).symm⟩⟩
    · rintro ⟨_,⟨l,r⟩|⟨r,l⟩⟩
      · exact Or.inl ⟨Fin.ext (Nat.add_right_cancel (l.trans (pairVal here))),Fin.ext (r.symm.trans (pairVal right).symm)⟩
      · exact Or.inr ⟨Fin.ext (Nat.add_right_cancel (r.trans (pairVal here))),Fin.ext (l.symm.trans (pairVal left).symm)⟩
  constructor
  · intro seen
    by_cases yes : ∃p,privateRawAt B old block s ticket slot p
    · obtain ⟨p,atSlot⟩:=yes
      exact ⟨p,atSlot,(each p atSlot).1 seen⟩
    · obtain ⟨j,_,positive⟩:=seen
      rw [blank (fun p h=>yes ⟨p,h⟩)] at positive
      simp [PrivateEvidence.ticket] at positive
  · rintro ⟨p,atSlot,hits⟩
    exact (each p atSlot).2 hits

/-- A private wire at either endpoint belongs to the original host recovered
by taking the high digit of that endpoint's actual published ordinal. -/
theorem private_peer_host {H : ℕ} (prev : Fintype.card input.V≤H) (old : Fin (Fintype.card input.V))
    (here : Fin (pool).card) (next : Fin (H*(pool).card)) (p : PrivateOccurrence B)
    (touches : rawPeer B (privateWire B p) (finProdFinEquiv (old.castLE prev,here)).val next.val) :
    vertexCode ((Z).rootVertex T p.1.2)=old := by
  let e:=privateWire B p
  have endpoints:=private_endpoint_roots B p
  have high (u : Host) (root : receiverRoot B u=((Z).rootVertex T p.1.2,(Z).rootBlock T p.1.2))
      (idx : ((Z).rawHostRank T vertexCode u.1.2).val=(finProdFinEquiv (old.castLE prev,here)).val) :
      vertexCode ((Z).rootVertex T p.1.2)=old := by
    have atom : position (Z).graph u.1.2.val=(Z).rootVertex T p.1.2:=congrArg Prod.fst root
    let low:=((Z).hostFields T vertexCode u.1.2).2
    have narrow : (finProdFinEquiv (vertexCode ((Z).rootVertex T p.1.2),low) : Fin ((Fintype.card input.V)*(pool).card))=
        finProdFinEquiv (old,here) := by
      apply Fin.ext
      exact (congrArg (fun z => low.val+(pool).card*(vertexCode z).val) atom).symm.trans idx
    exact congrArg Prod.fst (finProdFinEquiv.injective narrow)
  rcases touches.2 with ⟨left,_⟩|⟨right,_⟩
  · exact high _ endpoints.1 ((signed_header B e false).2.1.trans left)
  · exact high _ endpoints.2 ((signed_header B e true).2.1.trans right)

/-- Existential union over the actual common blocks and dense private socket
bank. The sign, root ticket, and device edge number witness completeness. -/
theorem private_ticket_union {H D₀ : ℕ} (prev : Fintype.card input.V≤H)
    (peers : Fin H→Fin D₀→Option (Fin H)) (old : Fin (Fintype.card input.V)) (here : Fin (pool).card)
    (next : Fin (H*(pool).card))
    (code : Block (T).commonDepth→Bool→(Z).RootTicket T→Fin capacity→ℕ)
    (read : ∀g₀ s t i₀,let v:=finProdFinEquiv (old.castLE prev,here)
      (∃j : Fin (Candidates.count (pool).card D₀),Candidates.candidate peers v j=some next ∧ code g₀ s t i₀=j.val+1) ↔
        ∃p,privateRawAt B old g₀ s t i₀ p ∧ rawPeer B (privateWire B p) v.val next.val) :
    let v:=finProdFinEquiv (old.castLE prev,here)
    (∃(g₀ : Block (T).commonDepth) (s : Bool) (t : (Z).RootTicket T) (i₀ : Fin capacity) (j : Fin (Candidates.count (pool).card D₀)),Candidates.candidate peers v j=some next ∧ code g₀ s t i₀=j.val+1) ↔
      ∃p,rawPeer B (privateWire B p) v.val next.val := by
  intro v
  constructor
  · rintro ⟨g₀,s,t,i₀,j,atPeer,selected⟩
    obtain ⟨p,_,hits⟩:=(read g₀ s t i₀).1 ⟨j,atPeer,selected⟩
    exact ⟨p,hits⟩
  · rintro ⟨p,hits⟩
    have owner:=private_peer_host B prev old here next p hits
    let block:=(Z).rootBlock T p.1.2
    let ticket:=(Z).rootTicket T p.1.2
    let slot:=(privateTicket B p).2.2
    have atSlot : privateRawAt B old block p.1.1 ticket slot p:=⟨rfl,Prod.ext owner rfl,rfl⟩
    exact ⟨block,p.1.1,ticket,slot,(read block p.1.1 ticket slot).2 ⟨p,atSlot,hits⟩⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
