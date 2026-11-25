import OAI.Hierarchy.DescentPackedChildNeighborSIMDROM

namespace OAI
/-! # Read the actual peer query from an admitted parent at either live endpoint -/
namespace Hierarchy.DescentPackedChildNeighbor.PeerQuery
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentParallelBase PackedBase
open DescentHaloWalkRAM DescentParallelBase.ParentFilter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {T K cap H G M w E Q : ℕ}

def number (e : Option (Entry T K cap)) :=Packed.token (e.map Entry.peer)
def chip (T K cap : ℕ) (x : Cell (width T K cap)) :=number (decode T K cap x)

theorem chip_at (e : Option (Entry T K cap)) : chip T K cap (word e)=number e := by simp only [chip,back]
theorem chip_zero (T K cap : ℕ) : chip T K cap 0=0 :=by simp [chip,Stream.word_zero,number,Packed.token]

def tableWord (T K cap M i : ℕ) :=if yes:i<2^(width T K cap*M) then (DescentSIMDLookup.table (M:=M) (chip T K cap) ⟨i,yes⟩).val else 0

theorem rows (x : Fin H→Fin G→Option (Entry T K cap)) (p : Row H G M) :
    DescentSIMDLookup.table (chip T K cap) (data (fun h g=>word (x h g)) p)=data (fun h g=>number (x h g)) p :=by
  simp only [DescentSIMDLookup.table,data,Equiv.symm_apply_apply]
  apply congrArg (encode _ _);funext i
  by_cases inside:p.2.val*M+i.val<G <;> simp [inside,chip_at,chip_zero]

def expr (T K cap M base : ℕ) (input : Bank) : Expr :=.lookup ⟨base,width T K cap*M⟩ (.lookup input .row)
def program (T K cap M base : ℕ) (input : Bank) (out H G w : ℕ) :=
  (DescentStaticWordColumn.program w base (tableWord T K cap M) (2^(width T K cap*M))).seq (scan w out (H*chunks G M) (expr T K cap M base input))

theorem run (base out : ℕ) (input : Bank) (m : Memory w) (x : Fin H→Fin G→Option (Entry T K cap))
    (fit : input.Fits w base) (len : H*chunks G M≤ input.size) (sep : base+2^(width T K cap*M)≤out) (last : out+H*chunks G M<2^w)
    (installed : ∀p : Row H G M,m (input.base+(row H G M p).val)=((data (fun h g=>word (x h g)) p).val:Word w)) :
    let size:=2^(width T K cap*M);let mid:=DescentStaticWordColumn.image base (tableWord T K cap M) m size
    let e:=expr T K cap M base input;let n:=H*chunks G M;let done:=image out n e mid
    (program T K cap M base input out H G w).Exec m done ((4+10*size)+(4+n*28)) ∧
      (∀p : Row H G M,done (out+(row H G M p).val)=((data (fun h g=>number (x h g)) p).val:Word w)) ∧
      (∀u,u<base ∨ out+n≤u→done u=m u) :=by
  intro size mid e n done
  have top:=((Nat.le_add_right ..).trans_lt last : out<2^w)
  have lo:=sep.trans_lt top
  have moved:input.Fits w out:=⟨fit.1,fit.2.1,fit.2.2.trans ((Nat.le_add_right ..).trans sep)⟩
  let dict:Bank:=⟨base,width T K cap*M⟩
  have dictFits:dict.Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt lo,sep⟩
  have before (j:ℕ) (h:j<base):mid j=m j:=DescentStaticWordColumn.frame _ _ _ _ _ (.inl h)
  have first : (DescentStaticWordColumn.program w base (tableWord T K cap M) size).Exec m mid (4+10*size) :=
    DescentStaticWordColumn.mount base size (tableWord T K cap M) m lo
  have fitExpr:e.Fits w out:=⟨dictFits,moved,trivial⟩
  have ran : (scan w out n e).Exec mid done (4+n*28) := scan_exec out n e mid fitExpr last
  refine ⟨first.then ran,?_,?_⟩
  · intro p
    apply (ProtocolRAMGeneratedWrite.read_image out n e mid (row H G M p)).trans
    let key:=data (fun h g=>word (x h g)) p
    have small: (row H G M p).val < input.size:=(row H G M p).isLt.trans_le len
    change dict.read mid (input.read mid ((row H G M p).val : Word w))=_
    rw [bank_read _ _ small moved,before _ ((Nat.add_lt_add_left small _).trans_le fit.2.2),installed,bank_read dict mid key.isLt dictFits]
    change DescentStaticWordColumn.image base (tableWord T K cap M) m size (base+key.val)=_
    rw [DescentStaticWordColumn.read base size _ m key.isLt]
    simp only [tableWord,dite_eq_left key.isLt,Fin.eta,key,rows]
  · intro u away;rcases away with early|late
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u (.inl (early.trans_le ((Nat.le_add_right ..).trans sep)))).trans (before _ early)
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u (.inr late)).trans (DescentStaticWordColumn.frame _ _ _ _ _ (.inr (sep.trans ((Nat.le_add_right ..).trans late))))

/-- An admitted positive cable always requests the opposite host's ticket;
when both endpoints coincide, the source branch of the real filter wins. -/
theorem source (R : Fin H→Fin E→Option (Fin H)) (symm_ : ∀v u i,R v i=some u→∃j,R u j=some v)
    (s t : Fin H×Fin Q) (donor : Fin H) (p : Fin (breadth E)) (r : ParentFilter.Source (breadth E) Q K cap)
    (toward : Gather.reaching R s.1 p=some donor) (real : Witness R donor r s t) (live : 0<r.weight.val) :
    (number (filter R s p donor r)).val=(peer R s.1 p r.dst).val+1 :=by
  rw [accepted R symm_ s s t donor p r toward real];simp [live.ne',number,Packed.token]

theorem target (R : Fin H→Fin E→Option (Fin H)) (symm_ : ∀v u i,R v i=some u→∃j,R u j=some v)
    (s t : Fin H×Fin Q) (donor : Fin H) (p : Fin (breadth E)) (r : ParentFilter.Source (breadth E) Q K cap)
    (toward : Gather.reaching R t.1 p=some donor) (real : Witness R donor r s t) (live : 0<r.weight.val) (separate : t≠s) :
    (number (filter R t p donor r)).val=(peer R t.1 p r.src).val+1 :=by
  rw [accepted R symm_ t s t donor p r toward real];simp [live.ne',separate,number,Packed.token]

end
end Hierarchy.DescentPackedChildNeighbor.PeerQuery

end OAI
