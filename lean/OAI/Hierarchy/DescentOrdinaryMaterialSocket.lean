import OAI.Hierarchy.DescentOrdinaryMaterialRoute
import OAI.Hierarchy.DescentScalarBookReshape
import OAI.Hierarchy.DescentActorRechunk

namespace OAI
/-! Receiving a physical parent across the old halo and projecting its actual group into a new block. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H K G M a r w D : ℕ}
local notation "P" => breadth D
abbrev Port := Fin 9

/-- Two rooted endpoints, receiver path, and six local parent fields, respectively. -/
def donorField : Port→Fin 9 := ![0,1,6,2,3,6,4,8,5]
def gated (f : Port) := decide (f.val=2 ∨ f.val=5)

def stamp (pitch : ℕ) (p : Fin P) (f : Port) (h : Fin K) : Cell a :=
  (if f.val=5 then h.val%pitch else p.val : ℕ)

def choose (gate : Bool) (i : Fin r) (v : Cell (a*r)) (mark : Cell a) : Cell a :=
  let old:=(encode a r).symm v i
  if gate then if old.val=0 then 0 else mark else old

private theorem zeroBook (a r : ℕ) : (encode a r).symm 0=fun _=>0 :=by
  apply (encode a r).symm_apply_eq.mpr
  apply Fin.ext
  change 0=(finFunctionFinEquiv (fun _:Fin r=>(0:Cell a))).val
  simp []

theorem choose_empty (gate : Bool) (i : Fin r) (mark : Cell a) : choose gate i 0 mark=0 :=by
  simp [choose,zeroBook]

def selected (R : Fin H→Fin D→Option (Fin H)) (pitch : ℕ) (p : Fin P) (h : Fin K) : Option (Fin H) :=
  (receiver H pitch h).bind (fun v=>Gather.select (Gather.reaching R) v p)

def value (R : Fin H→Fin D→Option (Fin H)) (pitch : ℕ) (p : Fin P) (f : Port) (i : Fin r)
    (x : Fin H→Fin (G*r)→Cell a) (h : Fin K) (g : Fin G) : Cell a :=
  (selected R pitch p h).elim 0 (fun v=>
    let y:=x v (finProdFinEquiv (g,i))
    if gated f then if y.val=0 then 0 else stamp pitch p f h else y)

theorem evaluated (R : Fin H→Fin D→Option (Fin H)) (pitch : ℕ) (p : Fin P) (f : Port) (i : Fin r)
    (x : Fin H→Fin (G*r)→Cell a) (h : Fin K) (g : Fin G) :
    choose (gated f) i ((receiver H pitch h).elim 0 (fun v=>
      (Gather.select (Gather.reaching R) v p).elim 0 (fun u=>groupedRows x u g))) (stamp pitch p f h)=
      value R pitch p f i x h g :=by
  cases eqn:receiver H pitch h with
  | none=>simp [value,selected,eqn,choose_empty]
  | some v=>
    cases hit:Gather.select (Gather.reaching R) v p with
    | none=>simp [value,selected,eqn,hit,choose_empty]
    | some u=>simp [value,selected,eqn,hit,choose,groupedRows]

def stampValue (K G M a pitch paths : ℕ) (i : ℕ) : ℕ :=
  let rows:=K*chunks G M
  if valid : i<(paths+1)*rows then
    let q : Fin (paths+1)×Row K G M:=(finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr (row K G M).symm)) ⟨i,valid⟩
    (data (fun (h : Fin K) (_:Fin G)=>((if q.1.val=paths then h.val%pitch else q.1.val : ℕ):Cell a)) q.2).val
  else 0

def stampId (f : Port) (p : Fin P) : Fin (P+1) :=if f.val=5 then Fin.last P else p.castSucc
def stampBank (K G M base : ℕ) (f : Port) (p : Fin P) : Bank :=
  ⟨base+(stampId f p).val*(K*chunks G M),Nat.clog 2 (K*chunks G M+1)⟩

theorem stamp_read (K G M a pitch base : ℕ) (m : Memory w) (f : Port) (p : Fin P) :
    Reads (stampBank K G M base f p) (fun (h : Fin K) (_:Fin G)=>(stamp pitch p f h:Cell a)) M
      (DescentStaticWordColumn.image base (stampValue K G M a pitch P) m ((P+1)*(K*chunks G M))) :=by
  intro z
  let i:=(finProdFinEquiv (stampId f p,row K G M z):Fin ((P+1)*(K*chunks G M)))
  have addr:(stampBank K G M base f p).base+(row K G M z).val=base+i.val:=by
    simp [i,stampBank,finProdFinEquiv_apply_val,Nat.mul_comm (K*chunks G M) (stampId f p).val];omega
  rw [addr,DescentStaticWordColumn.read _ _ _ _ i.isLt]
  rw [stampValue, dite_eq_left i.isLt]
  simp only [Fin.eta, i, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply]
  by_cases low:f.val=5
  · simp [stampId,stamp,low]
  · simp [stampId,stamp,low,Nat.ne_of_lt p.isLt]

def projected (B : DescentOrdinaryDonorRankDirectory.Banks) (ports : Ports P) (src mapB markB : Bank)
    (oldHosts groups lanes : ℕ) (p : Fin P) (tables : Tables) : Expr :=
  tables.read (lift mapB (oldHosts*chunks groups lanes) (peerExpr (keepPorts B ports) src oldHosts p)) (.lookup markB .row)

theorem source (R : Fin H→Fin D→Option (Fin H)) (B : DescentOrdinaryDonorRankDirectory.Banks) (ports : Ports P)
    (src mapB markB : Bank) (pitch out : ℕ) (m : Memory w) (p : Fin P) (f : Port) (i : Fin r) (T : Tables)
    (x : Fin H→Fin (G*r)→Cell a) (hm : 0<M) (hr : 0<r)
    (old : Reads src x (M*r) m) (roster : Mounted ports (Gather.reaching R) m G M)
    (ranks : DescentOrdinaryDonorRankDirectory.Reads R B m) (early : Accessible (keepPorts B ports) src H G M w out)
    (mapFit : mapB.Fits w out) (mapSize : K*chunks G M≤ mapB.size) (safe : H*chunks G M<2^w)
    (mapRead : ∀z : Row K G M,m (mapB.base+(row K G M z).val)=(index H pitch z:Word w))
    (markSize : K*chunks G M≤ markB.size) (markRead : Reads markB (fun (h : Fin K) (_:Fin G)=>(stamp pitch p f h:Cell a)) M m)
    (pages : Static T (choose (a:=a) (gated f) i) M m)
    (fit : DescentPackedZip.Fits T (lift mapB (H*chunks G M) (peerExpr (keepPorts B ports) src H p))
      (.lookup markB .row) (a*r) a M out w) :
    Source (projected B ports src mapB markB H G M p T) (value (K:=K) R pitch p f i x) M m :=by
  have prior:=old_field R B ports src mapB pitch out m p hm hr x old roster ranks early mapFit mapSize safe mapRead
  have mark:=source_column markB out fit.right.1 m _ markSize markRead
  have result:=read_data T _ _ out fit _ (choose_empty (gated f) i _) m pages _ _ prior mark
  simpa only [projected,evaluated] using result

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route

end OAI
