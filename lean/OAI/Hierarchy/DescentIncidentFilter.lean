import OAI.Hierarchy.DescentIncidentMeasuredOrder
import OAI.Hierarchy.DescentParentFilterFused

namespace OAI
/-! # The same true eleven columns issue all-neighbor rank rows as well as parallel rank rows -/
namespace Hierarchy.DescentParallelBase.Incidence.Filter
open DescentSharedCableNames DescentHaloWalkRAM DescentSIMDLookup DescentPackedZip ParentFilter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D H Q K L b G M w:ℕ}
local notation "P"=>breadth D
local notation "cap"=>P*P*Q
local notation "wd"=>PackedBase.width 1 (cap*K) L

def scalar (D Q K L b:ℕ) (x:Cell (b*11)):Cell (PackedBase.width 1 (breadth D*breadth D*Q*K) L):=
  let peerCapacity:=breadth D*breadth D*Q
  let f:=(encode b 11).symm x
  let seen:=PackedBase.decode peerCapacity K L (Machine.scalar D Q K L b x)
  PackedBase.word (seen.bind (fun e=>if ok:(f 6).val<peerCapacity then some (Incidence.row ⟨(f 6).val,ok⟩ e.ticket e.weight) else none))

variable {R : Fin H→Fin D→Option (Fin H)}

def directed (a:Option (Fused.Raw R Q K L b)):Option (Entry 1 (cap*K) L):=a.bind (fun r=>
  (ParentFilter.filter R r.receiver r.path r.host r.parent).map (fun e=>Incidence.row (peer R r.receiver.1 r.path r.parent.src) e.ticket e.weight))

theorem empty : scalar D Q K L b 0=0:=by
  simp only [scalar, Machine.absent, Stream.word_zero]
  apply Fin.ext
  rfl

theorem read (r:Option (Fused.Raw R Q K L b)):
    scalar D Q K L b (encode b 11 (Fused.columns r))=PackedBase.word (directed r):=by
  cases r with
  | none=>
    have dead:encode b 11 (Fused.columns (none:Option (Fused.Raw R Q K L b)))=0:=by apply Fin.ext;simp [Fused.columns,encode]
    rw [dead,empty];rfl
  | some r=>
    have old:=Fused.field_read (some r)
    change Machine.scalar D Q K L b (encode b 11 (Fused.columns (some r)))=PackedBase.word (ParentFilter.filter R r.receiver r.path r.host r.parent) at old
    simp only [scalar,old,PackedBase.back,Equiv.symm_apply_apply]
    have key: (Fused.columns (some r) 6).val=(peer R r.receiver.1 r.path r.parent.src).val:=rfl
    simp only [key,dite_eq_left (peer R r.receiver.1 r.path r.parent.src).isLt,directed,Option.bind_some]
    cases ParentFilter.filter R r.receiver r.path r.host r.parent <;> rfl

section Shelf
variable {U E X T V:Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T] {n O:ℕ} {B:Ends U n}
  (C:Blocks B E) (R:Fin H→Fin D→Option (Fin H)) (symm:∀v u i,R v i=some u→∃j,R u j=some v)
  (Z:Measured C R X T V Q O K L) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K L) i,Machine.fields R (Z.venue h) path (Z.loc x).1 s i<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
local notation "res"=>Measured.roster C R symm Z
local notation "census"=>Incidence.of_measured C R symm Z orders
local notation "fetched"=>Fused.fetched C R Z shelf small

theorem at_raw (h:U) (e:Local C h) :
    fetched h ((res).address h e)=some (⟨Z.venue h,Measured.visit C R symm Z h e,Z.old h e,Z.read h e,small h _ _ _⟩:Fused.Raw R Q K L b):=by
  have selectPath := Resident.visit_read C h (fun v=>(Z.venue v).1) Z.loc (Z.raw h)
    (Gather.reaching R) (Measured.near C R symm Z h) e
  change Gather.select _ _ (Measured.visit C R symm Z h e)=_ at selectPath
  have coords : finProdFinEquiv.symm ((res).address h e) =
      (Measured.visit C R symm Z h e, (Z.loc (Z.raw h e)).2) :=
    finProdFinEquiv.symm_apply_apply _
  unfold Fused.fetched Resident.collected
  dsimp only
  rw [coords]
  rw [selectPath,Option.bind_some,Resident.old_at,Fused.previous,shelf.covers]
  rfl

theorem truthful (h:U) (j:Fin (P*O)):
    directed (fetched h j)=place ((census).addr h) (Incidence.entry C census h) j:=by
  change directed (fetched h j)=place ((res).address h) (Incidence.entry C census h) j
  have shared:=Fused.fetched_read C R symm Z shelf small h j
  by_cases accepted:∃e,(res).address h e=j
  · obtain ⟨e,rfl⟩:=accepted
    rw [at_raw C R symm Z shelf small h e,place_at] at shared
    change ParentFilter.filter R (Z.venue h) (Measured.visit C R symm Z h e) _ (Z.read h e)=some ((res).entry h e) at shared
    rw [at_raw C R symm Z shelf small h e,place_at];simp [directed,shared,Incidence.entry,of_measured,srcKey,Measured.roster,Measured.entry]
  · rw [place_empty _ _ _ (not_exists.mp accepted)] at shared ⊢
    cases seen:fetched h j with
    | none=>rfl
    | some r=>rw [seen] at shared;change ParentFilter.filter R r.receiver r.path r.host r.parent=none at shared;simp [directed,shared]

variable {EHosts Groups : ℕ} (hosts:Fin EHosts→Fin Groups→Option U)
local notation "raw"=>Fused.cell C R Z shelf small hosts

theorem full (j:Fin (P*O)) (v:Fin EHosts) (g:Fin Groups): directed (raw j v g)=Incidence.items C census hosts j v g:=by
  cases live:hosts v g with
  | none=>simp [Fused.cell,live,directed,Incidence.items]
  | some h=>simp only [Fused.cell,live,Option.bind_some,Incidence.items];exact truthful C R symm Z shelf small orders h j

local notation "Join"=>DescentPacking.PackedMatch.Local.Gather.assembly

/-- Consume the eleven genuine physical input fields that also drive the
shared peer ranker, keeping its source code in the all-neighbor comparison. -/
theorem cpu (fit:∀u,(B.incident u).card≤L) (j:Fin (P*O)) (joins:Fin 11→Tables) (field:Fin (P*O)→Fin 11→Expr)
    (format compare:Tables) (out:Bank) (m:Memory w)
    (bounds:∀i,DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w) joins (field i) out.base)
    (fixed:∀i,Static (joins i) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) i) M m)
    (original:∀i t,DescentPackedZip.Source (field i t) (fun v g=>Fused.columns (raw i v g) t) M m)
    (formatFit:∀i,DescentPackedZip.Fits format (Join joins (field i)) (.lit 0) (b*11) 0 M out.base w)
    (printer:Static format (fun x (_:Cell 0)=>scalar D Q K L b x) M m)
    (pairFit:∀i,DescentPackedZip.Fits compare (Fused.expression joins (field j) format) (Fused.expression joins (field i) format) wd wd M out.base w)
    (checker:Static compare (Stream.compareWord 1 (cap*K) L) M m)
    (space:out.base+EHosts*chunks Groups M<2^w):
    let f:=Fused.operation j joins field format compare
    let done:=image out.base (EHosts*chunks Groups M) f m
    let cells:=Incidence.items C census hosts
    (scan w out.base (EHosts*chunks Groups M) f).Exec m done (4+EHosts*chunks Groups M*(2*f.work+4)) ∧
    DescentPackedColony.Reads out (Stream.totalWord (cells j) cells (Incidence.capacity C census hosts fit j)) M done ∧ CheapCode (scan w out.base (EHosts*chunks Groups M) f):=by
  apply Incidence.run C census hosts fit j compare _ out m pairFit checker _ space
  intro i
  have ass:=DescentPacking.PackedMatch.Local.Gather.collected joins (field i) out.base (bounds i) m fixed (fun v g=>Fused.columns (raw i v g)) (original i) (List.finRange 11)
  have joined:DescentPackedZip.Source (Join joins (field i)) (fun v g=>encode b 11 (Fused.columns (raw i v g))) M m:=by simpa [DescentPacking.PackedMatch.Local.Gather.assembly] using ass
  have zero:DescentPackedZip.Source (.lit 0) (fun _:Fin EHosts=>fun _:Fin Groups=>(0:Cell 0)) M m:=by intro p;change 0=(((finFunctionFinEquiv (fun i:Fin M=>if _:p.2.val*M+i.val<Groups then (0:Cell 0) else 0)).val:ℕ):Word w);simp []
  have issued:=read_data format (Join joins (field i)) (.lit 0) out.base (formatFit i) (fun x (_:Cell 0)=>scalar D Q K L b x) empty m printer _ _ joined zero
  simpa only [Fused.expression,read,full C R symm Z shelf small orders hosts] using issued

end Shelf
end
end Hierarchy.DescentParallelBase.Incidence.Filter

end OAI
