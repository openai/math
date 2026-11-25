import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Select the reciprocal sender using the two actual packed endpoint rosters -/
namespace Hierarchy.DescentPackedFlowReturn
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H J M a w : ℕ}

structure Index where
  starts : Bank
  hosts : Bank

structure Header (C : Index) (dst : ℕ) (mem : Memory w) (D H J M : ℕ) : Prop where
  starts : C.starts.Fits w dst
  host : C.hosts.Fits w dst
  n : H≤C.starts.size
  rows : H*chunks J M≤C.hosts.size
  read (v : Fin H) : mem (C.starts.base+v.val)=((v.val*D:ℕ):Word w)
  self (p : Row H J M) : mem (C.hosts.base+(row H J M p).val)=(p.1.val:Word w)

def reverseID (C : Index) (P : Ports D) (i j : Fin D) : Expr :=
  .lookup P.roster (.op .add (.lookup C.starts (neighborID P i)) (.lit j.val))

def gated (C : Index) (P : Ports D) (src : Bank) (H : ℕ) (i j : Fin D) : Expr :=
  .branch .eq (neighborID P i) (.lit H) (.lit 0)
    (.branch .eq (reverseID C P i j) (.lookup C.hosts .row) (peerExpr P src H i) (.lit 0))

def back (next : Fin H→Fin D→Option (Fin H)) (v : Fin H) (i j : Fin D) : Option (Fin H) :=
  (next v i).bind fun t=>if next t j=some v then some t else none

private theorem card_slot (v : Fin H) (i : Fin D) : v.val*D+i.val<H*D := by
  calc _<v.val*D+D:=Nat.add_lt_add_left i.isLt _
       _=(v.val+1)*D:=(Nat.succ_mul ..).symm
       _≤_:=Nat.mul_le_mul_right D v.isLt

open private Hierarchy.DescentPackedColony.digit_read
  from OAI.Hierarchy.DescentPackedPorts

private theorem selected_data (X : Fin H→Fin J→Cell a) (p : Row H J M)
    (select : Fin H→Option (Fin H)) :
    (data (fun v g=>(select v).elim 0 (fun t=>X t g)) p).val =
      (select p.1).elim 0 (fun t=>(data X (t,p.2)).val) :=
  Hierarchy.DescentPackedColony.digit_read X p (select p.1)

open DescriptorExpr in
theorem source (C : Index) (P : Ports D) (src : Bank) (out : ℕ)
    (next : Fin H→Fin D→Option (Fin H)) (i j : Fin D) (m : Memory w)
    (header : Header C out m D H J M) (fit : Accessible P src H J M w out)
    (mounted : Mounted P next m J M) (X : Fin H→Fin J→Cell a) (old : Reads src X M m) :
    DescentPackedZip.Source (gated C P src H i j) (fun v g=>(back next v i j).elim 0 (fun t=>X t g)) M m := by
  intro p
  have hH : H<2^w := fit.offRoom.trans_lt fit.offsets.2.1
  have who := DescentPackedZip.bank_read _ m ((row H J M p).isLt.trans_le (fit.idsRoom i)) (fit.ids i)
  have idx : (neighborID P i).eval m ((row H J M p).val:Word w)=(target (next p.1 i):Word w) := by
    simp only [neighborID,Expr.eval,who,mounted.ids,
      DescentPackedZip.bank_read _ _ ((card_slot p.1 i).trans_le fit.rosterRoom) fit.roster,mounted.roster]
  have get:=peerSource P src out fit next m mounted X old i p
  rw [selected_data X p (fun v=>next v i)] at get
  rw [selected_data X p (fun v=>back next v i j)]
  have neq (v : Fin H) : Comparison.eq.test (v.val:Word w) (H:Word w)=false := by
    simp [Comparison.test,Fin.ext_iff,Fin.val_cast_of_lt (v.isLt.trans hH),Fin.val_cast_of_lt hH,Nat.ne_of_lt v.isLt]
  have nr (v : Fin H) (z : Option (Fin H)) :
      Comparison.eq.test (target z:Word w) (v.val:Word w)=true ↔ z=some v := by
    cases z with
    | none=>simp [Comparison.test,target,Fin.ext_iff,Fin.val_cast_of_lt (v.isLt.trans hH),
        Fin.val_cast_of_lt hH,(Nat.ne_of_lt v.isLt).symm]
    | some t=>simp [Comparison.test,target,Fin.ext_iff,Fin.val_cast_of_lt (t.isLt.trans hH),Fin.val_cast_of_lt (v.isLt.trans hH)]
  cases actual:next p.1 i with
  | none=>simp [gated,Expr.eval,idx,actual,target,back,Comparison.test]
  | some u=>
    have reverse : (reverseID C P i j).eval m ((row H J M p).val:Word w)=(target (next u j):Word w) := by
      simp only [reverseID,Expr.eval,idx,actual,target,Option.elim_some,
        DescentPackedZip.bank_read _ _ (u.isLt.trans_le header.n) header.starts,header.read,
        RowOp.opcode,BinaryOp.eval,←Nat.cast_add,DescentPackedZip.bank_read _ _ ((card_slot u j).trans_le fit.rosterRoom) fit.roster,mounted.roster]
    have target_u : target (some u)=u.val := rfl
    simp only [gated,Expr.eval,idx,actual,target_u,neq,Bool.false_eq_true,ite_false,
      reverse,DescentPackedZip.bank_read _ _ ((row H J M p).isLt.trans_le header.rows) header.host,header.self,nr,
      back,Option.bind_some]
    by_cases returns : next u j=some p.1
    · simpa only [ite_eq_left returns,actual,Option.elim_some] using get
    · simp [returns]

theorem safe (C : Index) (P : Ports D) (src : Bank) (out : ℕ) (m : Memory w) (i j : Fin D)
    (header : Header C out m D H J M) (fit : Accessible P src H J M w out) :
    (gated C P src H i j).Fits w out := by
  simp [gated,reverseID,neighborID,peerExpr,Expr.Fits,fit.ids,fit.roster,fit.source,fit.offsets,fit.chunks,header.starts,header.host]

theorem cost (C : Index) (P : Ports D) (src : Bank) (i j : Fin D) :
    (gated C P src H i j).work≤110 := by
  simp only [gated,reverseID,peerExpr,neighborID,Expr.work]; decide

end
end Hierarchy.DescentPackedFlowReturn

end OAI
