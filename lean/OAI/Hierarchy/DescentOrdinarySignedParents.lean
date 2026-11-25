import OAI.Hierarchy.DescentOrdinarySignedRanks
import OAI.Hierarchy.DescentIncidentFilter
import OAI.Hierarchy.DescentParentFilterTables

namespace OAI
/-! Recover the ordinary ranker's entire comparison record from the eleven
donor and receiver fields. Both peer and source are measured in the receiver's
halo; ghosts and nonincident donor records are filtered before comparison. -/
namespace Hierarchy.DescentOrdinarySignedParents
open DescentHaloWalkRAM DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentResetSignedScan DescentOrdinarySignedRanks DescentSIMDLookup DescentPackedZip
open scoped Classical
noncomputable section
variable {oldH D Q K L b : ℕ} {R:Fin oldH→Fin D→Option (Fin oldH)}
local notation "P" => breadth D
local notation "pc" => P*P*Q

def code (D Q K L b:ℕ) (x:Cell (b*11)) : Cell (b*5):=
  let f:=(encode b 11).symm x
  let e:=PackedBase.decode (breadth D * breadth D * Q) K L (Machine.scalar D Q K L b x)
  encode b 5 (literal b (e.map (fun y=>⟨y.peer.val,(f 6).val,y.ticket.val,y.weight.val⟩)))

def actual (r:Option (Fused.Raw R Q K L b)):Option Parent:=
  r.bind (fun u=>(filter R u.receiver u.path u.host u.parent).map
    (fun y=>⟨y.peer.val,(peer R u.receiver.1 u.path u.parent.src).val,y.ticket.val,y.weight.val⟩))

theorem decoded (r:Option (Fused.Raw R Q K L b)):
    code D Q K L b (encode b 11 (Fused.columns r))=encode b 5 (literal b (actual r)):=by
  unfold code
  rw [Fused.field_read,PackedBase.back,Equiv.symm_apply_apply]
  cases r <;> rfl

theorem code_zero (D Q K L b:ℕ):code D Q K L b 0=0:=by
  have zero (m:ℕ):encode b m (fun _=>0)=0:=by apply Fin.ext;simp [encode]
  unfold code;rw [Machine.absent]
  have neg:PackedBase.decode (breadth D*breadth D*Q) K L 0=none:=by
    have silent:PackedBase.word (none:Option (Entry (breadth D*breadth D*Q) K L))=0:=by apply Fin.ext;rfl
    rw [←silent,PackedBase.back]
  rw [neg];exact zero 5

theorem fits (r:Option (Fused.Raw R Q K L b)) (one:1<2^b) (peerBound:pc≤2^b)
    (ticket:K≤2^b) (mass:L<2^b):DescentResetSignedScan.Fits b (actual r):=by
  cases r with
  | none=>trivial
  | some u=>
    change DescentResetSignedScan.Fits b ((filter R u.receiver u.path u.host u.parent).map _)
    cases h:filter R u.receiver u.path u.host u.parent with
    | none=>trivial
    | some y=>exact ⟨one,y.peer.isLt.trans_le peerBound,(peer R u.receiver.1 u.path u.parent.src).isLt.trans_le peerBound,
        y.ticket.isLt.trans_le ticket,y.weight.isLt.trans_le mass⟩

section Truth
variable {U E X T V:Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T] {n O : ℕ} {B:Ends U n}
  (C:Blocks B E) (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u i,R v i=some u→∃j,R u j=some v)
  (Z:Measured C R X T V Q O K L) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K L) i,Machine.fields R (Z.venue h) path (Z.loc x).1 s i<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
local notation "roster" => Measured.roster C R symm Z
local notation "census" => Incidence.of_measured C R symm Z orders
local notation "fetched" => Fused.fetched C R Z shelf small
local notation "otherCode" => (fun h (e : Local C h) => Fin.val (Entry.peer (DescentPackedOperand.Public.Roster.entry roster h e)))

theorem truthful (h:U) (j:Fin (P*O)):
    actual (fetched h j)=(resident ((census).addr h) j).map (parent C census otherCode h):=by
  have whole:=Fused.fetched_read C R symm Z shelf small h j
  by_cases hit:∃e,(roster).address h e=j
  · obtain ⟨e,rfl⟩:=hit
    rw [Incidence.Filter.at_raw C R symm Z shelf small h e,place_at] at whole
    change filter R (Z.venue h) (Measured.visit C R symm Z h e) (Z.old h e) (Z.read h e)=some ((roster).entry h e) at whole
    rw [Incidence.Filter.at_raw C R symm Z shelf small h e]
    change _=(resident ((roster).address h) ((roster).address h e)).map _
    rw [resident_at];simp only [actual,Option.bind_some,whole,Option.map_some]
    rfl
  · rw [place_empty _ _ _ (not_exists.mp hit)] at whole
    change _=(resident ((roster).address h) j).map _
    rw [resident_miss _ _ (not_exists.mp hit)]
    cases v:fetched h j with
    | none=>rfl
    | some r=>
      rw [v] at whole
      change filter R r.receiver r.path r.host r.parent=none at whole
      simp [actual,whole]

variable {AX H gg : ℕ} (home:Fin AX→Fin H→Fin gg→Option U)
def queryRaw (x:Fin AX) (p:Fin 3) (j:Fin (P*O)) (v:Fin H) (g:Fin gg):=
  (request C census home x p j v g).bind (fun z=>fetched z.1 ((census).addr z.1 z.2))
def itemRaw (x:Fin AX) (p:Fin 3) (j a:Fin (P*O)) (v:Fin H) (g:Fin gg):=
  (request C census home x p j v g).bind (fun z=>fetched z.1 a)

theorem queryCode (x:Fin AX) (p:Fin 3) (j:Fin (P*O)) (v:Fin H) (g:Fin gg):
    actual (queryRaw C R symm Z shelf small orders home x p j v g)=query C census otherCode home x p j v g:=by
  cases eqn:request C census home x p j v g with
  | none=>simp [queryRaw,query,eqn,actual]
  | some z=>simp [queryRaw,query,eqn,truthful C R symm Z shelf small orders,resident_at]
theorem itemCode (x:Fin AX) (p:Fin 3) (j a:Fin (P*O)) (v:Fin H) (g:Fin gg):
    actual (itemRaw C R symm Z shelf small orders home x p j a v g)=items C census otherCode home x p j a v g:=by
  cases eqn:request C census home x p j v g with
  | none=>simp [itemRaw,items,eqn,actual]
  | some z=>simp [itemRaw,items,eqn,truthful C R symm Z shelf small orders]
end Truth
end
end Hierarchy.DescentOrdinarySignedParents

end OAI
