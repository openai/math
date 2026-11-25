import OAI.Hierarchy.DescentNextSignedRAM

namespace OAI
/-! # A paid rectangular lookup brings the new source rank back to the old donor -/
namespace Hierarchy.DescentParallelBase.SourceReturn.RAM
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H P Q G b M w : ℕ}
local notation "T"=>P*(Q*P)
local notation "a"=>Packed.bits T

def key (p:Fin P) (low:Fin Q) (rev:Fin P) : Fin T:=finProdFinEquiv (p,finProdFinEquiv (low,rev))
def parts (j:Fin T) : Fin P×(Fin Q×Fin P):=((finProdFinEquiv.symm j).1,finProdFinEquiv.symm (finProdFinEquiv.symm j).2)
@[simp] theorem parts_key (p:Fin P) (low:Fin Q) (rev:Fin P):parts (key p low rev)=(p,low,rev):=by simp [parts,key]

def choose (j:Fin T) (q:Cell a) (x:Cell b):Cell b:=if q=Packed.token (some j) then x else 0

def field (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (j:Fin T) (v:Fin H) (g:Fin G):Cell b:=
  let z:=parts j;(R v z.1).elim 0 (fun u=>rank z.2.1 z.2.2 u g)

def output (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (q:Fin H→Fin G→Option (Fin T)) (v:Fin H) (g:Fin G):Cell b:=
  (q v g).elim 0 (fun j=>field R rank j v g)

theorem actual (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (q:Fin H→Fin G→Option (Fin T))
    (v u:Fin H) (g:Fin G) (p:Fin P) (low:Fin Q) (rev:Fin P)
    (issued:q v g=some (key p low rev)) (arrive:R v p=some u):output R rank q v g=rank low rev u g:=by simp [output,issued,field,arrive]

def body (K:Fin T→Tables) (ports:Ports P) (bank:Fin Q→Fin P→Bank) (query:Expr) (H:ℕ):Expr:=
  total (fun j=>K j |>.read query (peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1)) (List.finRange T)

/-- The source rank banks are read at the authentic halo endpoint. Only
the queried short (forward path, source low digits, return path) survives.
A physical source can be many hops from the raw donor or the receiver. -/
theorem run_sources (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (q:Fin H→Fin G→Option (Fin T))
    (K:Fin T→Tables) (ports:Ports P) (bank:Fin Q→Fin P→Bank) (query:Expr) (out:Bank) (m:Memory w)
    (bounds:∀j,DescentPackedZip.Fits (K j) query (peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1) a b M out.base w)
    (static:∀j,Static (K j) (choose (b:=b) j) M m)
    (inputs:Source query (fun v g=>Packed.token (q v g)) M m)
    (fetched:∀j,Source (peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1) (field R rank j) M m) (room:out.base+H*chunks G M<2^w):
    let f:=body K ports bank query H
    let after:=image out.base (H*chunks G M) f m
    (scan w out.base (H*chunks G M) f).Exec m after (4+H*chunks G M*(2*f.work+4)) ∧ Reads out (output R rank q) M after ∧ CheapCode (scan w out.base (H*chunks G M) f):=by
  intro f after
  let emit (j:Fin T):=(K j).read query (peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1)
  let value (j:Fin T) (v:Fin H) (g:Fin G):=choose j (Packed.token (q v g)) (field R rank j v g)
  have got (j:Fin T):Source (emit j) (value j) M m:=by
    apply read_data _ _ _ out.base (bounds j) (choose j) _ m (static j) _ _ inputs (fetched j)
    simp [choose]
  have chooseEq (i j:Fin T):Packed.token (some i)=Packed.token (some j) ↔ i=j:=by
    constructor
    · intro same;have eqn:=congrArg (Packed.readToken T) same;simpa using eqn
    · rintro rfl;rfl
  have empty (j:Fin T):Packed.token none≠Packed.token (some j):=by
    intro same;have eqn:=congrArg (Packed.readToken T) same;simp at eqn
  have totalValue (v:Fin H) (g:Fin G):(∑j,(value j v g).val)=(output R rank q v g).val:=by
    cases yes:q v g with
    | none=>simp [value,output,choose,yes,empty]
    | some i=>rw [Fintype.sum_eq_single i (fun j diff=>by simp [value,choose,yes,chooseEq,Ne.symm diff])];simp [value,choose,output,yes]
  have ok (j:Fin T):(emit j).Fits w out.base:=by
    let k:=bounds j;exact ⟨k.apply,k.right,k.shift,k.left⟩
  refine ⟨scan_exec _ _ _ _ (fits_total _ ok _) room,?_,by apply scan_cheap⟩
  intro x
  dsimp only [after]
  rw [ProtocolRAMGeneratedWrite.read_image out.base (H*chunks G M) f m (row H G M x)]
  change (total emit (List.finRange T)).eval m _=_
  have sum:=DescentNextSignedWindow.Native.sumEval emit (fun j=>(data (value j) x).val) m _ (fun i=>got i x) (List.finRange T)
  rw [←List.ofFn_eq_map,List.sum_ofFn,DescentNextSignedWindow.Native.laneSum value _ x totalValue] at sum;exact sum

theorem run (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (q:Fin H→Fin G→Option (Fin T))
    (K:Fin T→Tables) (ports:Ports P) (bank:Fin Q→Fin P→Bank) (query:Expr) (out:Bank) (m:Memory w)
    (access:∀l r,Accessible ports (bank l r) H G M w out.base) (neighbors:Mounted ports R m G M)
    (bounds:∀j,DescentPackedZip.Fits (K j) query (peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1) a b M out.base w)
    (static:∀j,Static (K j) (choose (b:=b) j) M m)
    (inputs:Source query (fun v g=>Packed.token (q v g)) M m)
    (ranks:∀l r,Reads (bank l r) (rank l r) M m) (room:out.base+H*chunks G M<2^w):
    let f:=body K ports bank query H
    let after:=image out.base (H*chunks G M) f m
    (scan w out.base (H*chunks G M) f).Exec m after (4+H*chunks G M*(2*f.work+4)) ∧ Reads out (output R rank q) M after ∧ CheapCode (scan w out.base (H*chunks G M) f) :=by
  apply run_sources R rank q K ports bank query out m bounds static inputs _ room
  intro j;exact peerSource ports _ out.base (access (parts j).2.1 (parts j).2.2) R m neighbors _ (ranks (parts j).2.1 (parts j).2.2) (parts j).1

theorem work (K:Fin T→Tables) (ports:Ports P) (bank:Fin Q→Fin P→Bank) (query:Expr) (H:ℕ):
    (body K ports bank query H).work≤1+T*(query.work+57):=by
  let f (j:Fin T):=(K j).read query (peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1)
  have localCost (j:Fin T):(f j).work≤query.work+56:=by
    have cost:(peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1).work=45:=rfl
    simp only [f,DescentPackedZip.work,cost];omega
  have bound:=work_total f _ localCost (List.finRange T);simpa only [body,f,List.length_finRange,Nat.add_assoc,Nat.reduceAdd] using bound

end
end Hierarchy.DescentParallelBase.SourceReturn.RAM

end OAI
