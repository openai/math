import OAI.Hierarchy.DescentContactSenderSearch
import OAI.Hierarchy.DescentContactTicketRun
import OAI.Hierarchy.DescentReservedProbeInputs
import OAI.Hierarchy.DescentFallbackMeasuredWindow
import OAI.Hierarchy.DescentResetCandidateDate
import OAI.Hierarchy.DescentResetOppositeRectangle

namespace OAI
/-! # Issuing all local contact labels from the old signed window and the shared measured book -/
namespace Hierarchy.DescentOldContactSender
open DescentRotorWindowArchive DescentSIMDLookup DescentPackedZip DescentContactTicketRun
open DescentResetLocalRoster DescentSharedCableNames DescentFallbackPeriod DescentPackedFallbackTree
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r b Ht : ℕ}
local notation "N" => L*(2*cap)
local notation "Y" => 2^n
local notation "B" => DescentSharedBookScan.width r Y D
abbrev Measure (D L cap n r b : ℕ) := RowData D L cap b × (Fin (DescentSharedBookScan.width r (2^n) D)→Cell b)

/-- The rotor archive supplies the signed, near, and peer coordinates. The rank cells come
from the separately installed shared book, since the rotor-only projection zero-fills them. -/
def window (x : Measure D L cap n r b) : Packet D L cap n r b
  | .inl i=>x.1 (.inl (.inl i))
  | .inr (.inl i)=>x.1 (.inl (.inr i))
  | .inr (.inr q)=>x.2 q

def withRank (a : RowData D L cap b) (v : Packet D L cap n r b) : Measure D L cap n r b :=
  (a,fun j=>v (.inr (.inr j)))

theorem window_observed (v : Packet D L cap n r b) (order : Fin L→Fin L→Bool) («meta» : Fin D→Fin D→Fin 6→Cell b) :
    window (withRank (observed v order «meta») v)=v := by
  funext i
  rcases i with i|(i|i) <;> rfl

def treePanel {l slots : ℕ} (p : DescentPackedPrivateMenu.Key (n:=n) r Ht slots l) :
    Option (Cell (DescentPackedFallbackTree.width Ht slots)) :=
  match p with
  | some (.inr (_,_,v))=>some v
  | _=>none

theorem tree_layer {l l' : ℕ} (s : Bool) (t) (v : Packet D L cap n r b) :
    treePanel (DescentFallbackPeriod.key (Ht:=Ht) (l:=l) s t v)=
      treePanel (DescentFallbackPeriod.key (Ht:=Ht) (l:=l') s t v) := by
  unfold DescentFallbackPeriod.key
  split
  · split <;> rfl
  · rfl

def treeSocket {slots : ℕ} (panel : Cell (DescentPackedFallbackTree.width Ht slots)) (j : Fin slots) : ℕ×ℕ :=
  let xs:=(encode (Ht+2) (slots+1)).symm panel
  ((xs j.succ).val-1,(xs 0).val)

theorem treeSocket_read {slots : ℕ} (height : ℕ) (values : Panel Ht slots) (j : Fin slots) (k : Fin (2^Ht))
    (bounded : height<2^(Ht+2)) (found : values j=some k) :
    treeSocket (pack Ht height values) j=(k.val,height) := by
  simp [treeSocket,DescentPackedFallbackTree.pack,found,DescentPackedFallbackTree.port,
    Fin.val_cast_of_lt bounded]

/-- The numeric read shared by both orientations. The columns are the portable joint, true
book height and old directed peer. Filling the unused oriented face with zero is essential at loops. -/
def point (Ht : ℕ) (s : Bool) (x : Measure D L cap n r b) (j : Fin L×Fin (2*cap)) : Fin 3→ℕ :=
  let win:=window x
  match DescentFallbackPeriod.arrival win s j.1 j.2 with
  | none=>fun _=>0
  | some (peer,far)=>
    let own:=localWord win j.1
    match DescentSenderRootStencil.choose r Y own far with
    | none=>fun _=>0
    | some (.inl t)=>
      match DescentRotorWindowScore.entry win s j with
      | none=>fun _=>0
      | some a=>
        let row:=fieldRow (n:=n) (r:=r) x.1 s j peer a
        let col:=DescentPackedReservationColumn.column n D b (2^r)
          (encode b (DescentPackedReservationColumn.fields D) row)
        ![(DescentContactSenderTicket.join Ht r Y ((rootId r Y (.inl t)).val+1) col.val 0).val,0,peer.val]
    | some (.inr t)=>
      match treePanel (DescentFallbackPeriod.key (Ht:=Ht) (l:=0) s t win) with
      | none=>fun _=>0
      | some book=>
        let addr:=treeSocket book (finProdFinEquiv j)
        ![(DescentContactSenderTicket.join Ht r Y ((rootId r Y (.inr t)).val+1) addr.1 addr.2).val,addr.2,peer.val]

theorem blank (s : Bool) (x : Measure D L cap n r b) (j : Fin L×Fin (2*cap))
    (empty : DescentFallbackPeriod.arrival (window x) s j.1 j.2=none) :
    point Ht s x j=fun _=>0 := by simp [point,empty]

theorem choice_read (s far : ℕ) (q : Root r Y) (x : Fin 3→Cell b) (live : (x 0).val≠0)
    (localAt : (x 1).val=s) (farAt : (x 2).val=far)
    (correct : (DescentSenderRootStencil.owner r Y x).val=(rootId r Y q).val+1) :
    DescentSenderRootStencil.choose r Y s far=some q := by
  simp only [DescentSenderRootStencil.owner,ite_eq_right live,localAt,farAt] at correct
  cases root : DescentSenderRootStencil.choose r Y s far with
  | none=>simp [root,Packed.token] at correct
  | some p=>
    have eqn : (rootId r Y p).val=(rootId r Y q).val:=by simpa [root,Packed.token] using correct
    rw [(rootId r Y).injective (Fin.ext eqn)]

theorem paid (s : Bool) (x : Measure D L cap n r b) (j : Fin L×Fin (2*cap)) (p : Fin D) (far : ℕ)
    (t : DescentResetHostSize.Code r) (a : DescentRotorWindowScore.Entry) (socket : Fin Y)
    (seen : DescentFallbackPeriod.arrival (window x) s j.1 j.2=some (p,far))
    (root : DescentSenderRootStencil.choose r Y (localWord (window x) j.1) far=some (.inl t))
    (good : DescentRotorWindowScore.entry (window x) s j=some a)
    (measured : (DescentPackedReservationColumn.column n D b (2^r) (encode b _
      (fieldRow (n:=n) (r:=r) x.1 s j p a))).val=socket.val) :
    point Ht s x j = ![(rootId r Y (.inl t)).val*(Y+2^Ht)+socket.val+1,0,p.val] := by
  simp only [point,seen,root,good,measured]
  rw [DescentContactSenderTicket.join_good Ht r Y t socket 0]

theorem exceptional (s : Bool) (x : Measure D L cap n r b) (j : Fin L×Fin (2*cap)) (p : Fin D) (far : ℕ)
    (t : DescentResetHostSize.Code r×Option (Fin Y)) (height : ℕ) (leaf : Fin height→Bool)
    (fits : height≤Ht) (entries : Panel Ht N) (l : ℕ)
    (seen : DescentFallbackPeriod.arrival (window x) s j.1 j.2=some (p,far))
    (root : DescentSenderRootStencil.choose r Y (localWord (window x) j.1) far=some (.inr t))
    (book : treePanel (DescentFallbackPeriod.key (Ht:=Ht) (l:=l) s t (window x))=some (pack Ht height entries))
    (hit : ∃k : Fin (2^Ht),entries (finProdFinEquiv j)=some k ∧ k.val=DescentTreePrefixIntervals.start Ht leaf) :
    point Ht s x j = ![(rootId r Y (.inr t)).val*(Y+2^Ht)+(Y+(DescentRotor.bitWord height leaf).val)+1,height,p.val] := by
  obtain ⟨k,found,low⟩:=hit
  have small : height<2^(Ht+2):=(fits.trans_lt (Nat.lt_two_pow_self (n:=Ht))).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  have alt:=(tree_layer (Ht:=Ht) (l:=0) (l':=l) s t (window x)).trans book
  simp only [point,seen,root,alt,treeSocket_read height entries _ k small found,low]
  rw [DescentContactSenderTicket.join_fallback Ht r Y t height leaf fits]

def count (D L cap n r : ℕ) := DescentRotorWindowArchive.count D L cap+DescentSharedBookScan.width r (2^n) D
def decode (x : Fin (count D L cap n r)→Cell b) : Measure D L cap n r b :=
  (fun i=>x (finSumFinEquiv (.inl (DescentRotorWindowArchive.ix i))),fun j=>x (finSumFinEquiv (.inr j)))
def lanes (L cap : ℕ) := 2*((L*(2*cap))*3)
def lane (s : Bool) (j : Fin (L*(2*cap))) (f : Fin 3) : Fin (lanes L cap) :=
  finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv (j,f))
def bundle (n r Ht : ℕ) (x : Fin (count D L cap n r)→Cell b) : Cell (b*lanes L cap) :=
  encode b (lanes L cap) (fun k=>let a:=finProdFinEquiv.symm k
    let u:=finProdFinEquiv.symm a.2
    point Ht (finTwoEquiv a.1) (decode x) (finProdFinEquiv.symm u.1) u.2)

theorem bundle_read (x : Fin (count D L cap n r)→Cell b) (s : Bool) (j : Fin L×Fin (2*cap)) (f : Fin 3)
    (wide : point Ht s (decode x) j f<2^b) :
    (((encode b (lanes L cap)).symm (bundle n r Ht x)) (lane s (finProdFinEquiv j) f)).val=point Ht s (decode x) j f := by
  simp only [bundle,lane,Equiv.symm_apply_apply,Equiv.apply_symm_apply,Fin.val_cast_of_lt wide]

def measureFields {T : Type} (board : Fin (DescentRotorWindowArchive.count D L cap)→T) (rank : Fin B→T) :
    Fin (count D L cap n r)→T :=
  fun i=>Sum.elim board rank (finSumFinEquiv.symm i)

theorem measure_read (board : RowData D L cap b) (rank : Fin B→Cell b) :
    decode (measureFields (fun i=>board (DescentRotorWindowArchive.ix.symm i)) rank)=(board,rank) := by
  apply Prod.ext
  · funext i
    simp [decode,measureFields]
  · funext i
    simp [decode,measureFields]

theorem measure_sources {H G M w : ℕ} (before : Memory w)
    (board : Fin (DescentRotorWindowArchive.count D L cap)→Expr) (rank : Fin B→Expr)
    (x : Fin H→Fin G→RowData D L cap b) (y : Fin H→Fin G→Fin B→Cell b)
    (seen : ∀i,Source (board i) (fun h g=>x h g (DescentRotorWindowArchive.ix.symm i)) M before)
    (book : ∀i,Source (rank i) (fun h g=>y h g i) M before) (i : Fin (count D L cap n r)) :
    Source (measureFields board rank i)
      (fun h g=>measureFields (fun j=>x h g (DescentRotorWindowArchive.ix.symm j)) (y h g) i) M before := by
  obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective i
  cases j with
  | inl j=>simpa [measureFields] using seen j
  | inr j=>simpa [measureFields] using book j

/-- Read one of the three cells from the common bundle on the predecessor of the
reciprocal kernel. The same bank holds every orientation and donor. -/
theorem projected {H G M w : ℕ} (s : Bool) (j : Fin L×Fin (2*cap)) (f : Fin 3)
    (banks : DescentSIMDLookup.Banks) (out : ℕ) (x : Fin H→Fin G→Fin (count D L cap n r)→Cell b)
    (mem : Memory w) (safe : DescentSIMDLookup.Fits banks (b*lanes L cap) b M H G w out)
    (arr : DescentPackedColony.Reads banks.source (fun h g=>bundle n r Ht (x h g)) M mem)
    (dict : DescentPackedFallbackTree.Image.resident (DescentFallbackPeriod.project (field:=b) (bytes:=b) (lane s (finProdFinEquiv j) f) 0)
      banks H G M mem) :
    Source (DescentSIMDLookup.lookup banks) (fun h g=>(point Ht s (decode (x h g)) j f : Cell b)) M mem := by
  let values:=fun h g i=>let a:=finProdFinEquiv.symm (i : Fin (lanes L cap))
    let u:=finProdFinEquiv.symm a.2
    (point Ht (finTwoEquiv a.1) (decode (x h g)) (finProdFinEquiv.symm u.1) u.2:Cell b)
  have seen:=DescentFallbackPeriod.projected banks out (lane s (finProdFinEquiv j) f) 0 values mem safe arr dict
  simpa only [values,lane,Equiv.symm_apply_apply,Equiv.apply_symm_apply,Nat.cast_zero,add_zero,Fin.cast_val_eq_self] using seen

/-- The sender book is gathered and evaluated once for all donors on each host/common-lane.
The two constituent banks are the rotor archive and the actual measured rank directory. -/
theorem issued {H G M w : ℕ} (base : ℕ) (m : Memory w) (reads : Fin (count D L cap n r)→Expr)
    (x : Fin H→Fin G→Fin (count D L cap n r)→Cell b) (pos : 0<M)
    (inputs : ∀i,Source (reads i) (fun h g=>x h g i) M m)
    (low : ∀i,(reads i).Fits w base) (room : (DescentResetCandidateDate.Shape.mk base 1 M H G).endAddress
      (count D L cap n r) b<2^w) (packed : M*max (b*count D L cap n r) (b*lanes L cap)≤w/2) :
    let A:=DescentResetCandidateDate.Shape.mk base 1 M H G
    let law:=bundle (D:=D) (L:=L) (cap:=cap) (b:=b) n r Ht
    let ctl:=fun _ : ℕ=>reads
    let out:=A.image law ctl m
    (A.code law ctl w).Exec m out (A.ticks law ctl) ∧ CheapCode (A.code law ctl w) ∧
      Source (.lookup (A.output (count D L cap n r) b 0) .row) (fun h g=>law (x h g)) M out ∧
      ∀addr,addr<base ∨ A.endAddress (count D L cap n r) b≤addr → out addr=m addr := by
  intro A law ctl out
  obtain ⟨go,cheap,frame⟩:=A.any law ctl m (fun _ _ i=>low i) room
  exact ⟨go,cheap,A.words law ctl m (fun _ _ i=>low i) room pos packed
    (fun _=>x) (fun _ _ i=>inputs i) 0 (by change 0<1; decide),frame⟩

end
end Hierarchy.DescentOldContactSender

end OAI
