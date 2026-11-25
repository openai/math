import OAI.Hierarchy.DescentNextSignedWindow
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentColonySplitRAM
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Numerical SIMD publication of the complete next signed six-field cable panel -/
namespace Hierarchy.DescentNextSignedWindow.Native
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D cap b H G M w c : ℕ}
local notation "s" => DescentSignedCableCodec.width D cap

def fields : Option (Record D cap)→Fin 8→ℕ
  | none=>fun _=>0
  | some r=>![1,r.side.toNat,r.neighbor.val,r.marked.toNat,r.position,r.shared,r.atSource,r.count]

def word (b : ℕ) (r : Option (Record D cap)) :=encode b 8 (fun i=>(fields r i:Cell b))

def decode (D cap b : ℕ) (x : Cell (b*8)) : Option (Record D cap):=
  let f:=(encode b 8).symm x
  if (f 0).val=0 then none else if ok:(f 2).val<D then
    some ⟨decide ((f 1).val=1),⟨_,ok⟩,decide ((f 3).val=1),(f 4).val,(f 5).val,(f 6).val,(f 7).val⟩ else none

theorem back (r : Option (Record D cap)) (ok : ∀i,fields r i<2^b) : decode D cap b (word b r)=r :=by
  simp only [decode,word,Equiv.symm_apply_apply,Fin.val_cast_of_lt (ok _)]
  cases r with
  | none=>rfl
  | some r=>
    change (if 1=0 then none else if hl:r.neighbor.val<D then some ⟨decide (r.side.toNat=1),⟨_,hl⟩,decide (r.marked.toNat=1),r.position,r.shared,r.atSource,r.count⟩ else none)=some r
    cases r with | mk side peer marked anchor shared atSource count=>cases side <;> cases marked <;> simp [peer.isLt]

def table (j : Fin (2*cap)) (x : Cell (b*8)) : Cell s :=DescentSignedCableCodec.encode ((decode D cap b x).bind (fun r=>read r j))

private theorem zero (j : Fin (2*cap)) : table (D:=D) (b:=b) j 0=0:=by
  have all0 : (encode b 8).symm 0=(fun _=>0):=by
    apply (encode b 8).symm_apply_eq.mpr;apply Fin.ext;change 0=(finFunctionFinEquiv (fun _:Fin 8=>(0:Cell b))).val;simp
  simp [table,decode,all0];rfl

theorem laneSum {b : ℕ} (get : Fin c→Fin H→Fin G→Cell b) (target : Fin H→Fin G→Cell b) (p : Row H G M)
    (correct : ∀h g,(∑i,(get i h g).val)=(target h g).val) :
    (∑i,(data (get i) p).val)=(data target p).val :=by
  have val (v : Fin H→Fin G→Cell b): (data v p).val=∑j:Fin M,(if h:p.2.val*M+j.val<G then (v p.1 ⟨_,h⟩).val else 0)*(2^b)^j.val:=by
    change (finFunctionFinEquiv _).val=_;rw [finFunctionFinEquiv_apply];apply Finset.sum_congr rfl;intro j _
    by_cases yes:p.2.val*M+j.val<G <;> simp [yes]
  simp_rw [val];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro j _
  by_cases yes:p.2.val*M+j.val<G
  · simp [yes,←Finset.sum_mul,correct]
  · simp [yes]

def op (tables : Tables) (field : Fin c→Expr) := total (fun i=>tables.read (field i) (.lit 0)) (List.finRange c)

theorem sumEval {α : Type} (f : α→Expr) (a : α→ℕ) (m : Memory w) (index : Word w)
    (ok : ∀j,(f j).eval m index=(a j:Word w)) (xs : List α) : (total f xs).eval m index=((xs.map a).sum:Word w) :=by
  induction xs with | nil=>rfl | cons i is ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ok,ih]

/-- Source fields are true previously issued parent windows, one packed
column per old-donor candidate. The result can mount directly as the next
stage's genuine sibling census and reverse-matcher source. -/
theorem run (j : Fin (2*cap)) (tables : Tables) (field : Fin c→Expr) (out : Bank) (m : Memory w)
    (rows : Fin H→Fin G→Fin c→Option (Record D cap)) (target : Fin H→Fin G→Option (Stage.Live D cap))
    (fit : ∀i,DescentPackedZip.Fits tables (field i) (.lit 0) (b*8) 0 M out.base w)
    (actual : ∀i,Source (field i) (fun h g=>word b (rows h g i)) M m)
    (small : ∀h g i t,fields (rows h g i) t<2^b) (rom : Static tables (fun x (_:Cell 0)=>table (D:=D) (b:=b) j x) M m)
    (empty : ∀h g,target h g=none→∀i,(rows h g i).bind (fun r=>read r j)=none)
    (live : ∀h g r,target h g=some r→∃i,(rows h g i).bind (fun u=>read u j)=some r ∧ ∀l,l≠i→(rows h g l).bind (fun u=>read u j)=none)
    (room : out.base+H*chunks G M<2^w) :
    let result:=image out.base (H*chunks G M) (op tables field) m
    (scan w out.base (H*chunks G M) (op tables field)).Exec m result (4+H*chunks G M*(2*(op tables field).work+4)) ∧
    DescentPackedColony.Reads out (fun h g=>DescentSignedCableCodec.encode (target h g)) M result ∧ CheapCode (scan w out.base (H*chunks G M) (op tables field)) :=by
  intro result
  let issued (i:Fin c) (h:Fin H) (g:Fin G):=DescentSignedCableCodec.encode ((rows h g i).bind (fun r=>read r j))
  have ghost:DescentSignedCableCodec.encode (none:Option (Stage.Live D cap))=0:=by apply Fin.ext;rfl
  have correct (h:Fin H) (g:Fin G) : (∑i,(issued i h g).val)=(DescentSignedCableCodec.encode (target h g)).val:=by
    cases hit:target h g with
    | none=>simp [issued,empty h g hit,ghost]
    | some x=>obtain ⟨i,yes,no⟩:=live h g x hit;rw [Fintype.sum_eq_single i (fun other ne=>by simp [issued,no other ne,ghost])];simp [issued,yes]
  have all0:Source (.lit 0) (fun _:Fin H=>fun _:Fin G=>(0:Cell 0)) M m:=by
    intro p;change 0=(((finFunctionFinEquiv (fun i:Fin M=>if _:p.2.val*M+i.val<G then (0:Cell 0) else 0)).val:ℕ):Word w);simp
  have get (i : Fin c) : Source (tables.read (field i) (.lit 0)) (issued i) M m:=by
    have got:=read_data tables (field i) (.lit 0) out.base (fit i) (fun x (_:Cell 0)=>table (D:=D) (b:=b) j x) (zero _) m rom _ _ (actual i) all0
    simpa only [table,back _ (small _ _ _),issued] using got
  have fits i : (tables.read (field i) (.lit 0)).Fits w out.base:=by simp [Tables.read,Expr.Fits,(fit i).left,(fit i).shift,(fit i).apply]
  refine ⟨scan_exec _ _ _ _ (fits_total _ fits _) room,?_,by apply scan_cheap⟩
  intro p
  dsimp only [result]
  rw [ProtocolRAMGeneratedWrite.read_image out.base (H*chunks G M) (op tables field) m (row H G M p)]
  have sum:=sumEval _ _ m _ (fun i=>get i p) (List.finRange c)
  rw [←List.ofFn_eq_map,List.sum_ofFn,laneSum issued _ p correct] at sum;exact sum

end
end Hierarchy.DescentNextSignedWindow.Native

end OAI
