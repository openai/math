import OAI.Hierarchy.DescentResetSourceTicketStream
import OAI.Hierarchy.DescentResetParentCodec

namespace OAI
/-! # Packed prefix counts evaluated with the true reset-local word comparison -/
namespace Hierarchy.DescentResetSourceTicketCompare
open DescentSIMDLookup DescentResetSourceTicketRAM DescentResetSignedScan
open DescentPackedSumWords (lanes_val)
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {K b paid H G M n : ℕ} (prior : ℕ→ℕ→Bool)

def asked (x : Fields K b) (j : Fin K) := if field x j 3=0 then none else query x j

def located (x : Fields K b) (j : Fin K) (side : Bool) :=
  if field x j 3=0 then none else face x j side

def operands (x : Fields K b) : Fin (K+K)→Option Parent :=
  Fin.addCases (fun j=>located x j false) (fun j=>located x j true)

theorem word_fits (x : Fields K b) (j : Fin K) (p : 1<2^b) :
    DescentResetSignedScan.Fits b (asked x j) ∧ ∀s,DescentResetSignedScan.Fits b (located x j s) := by
  by_cases off : field x j 3=0
  · simp [asked,located,off,DescentResetSignedScan.Fits]
  · simpa only [asked,located,ite_eq_right off] using fields_fit x j p

def feeAt (x : Fields K b) (target i : Fin K) :=
  if field x target 3≠0 ∧ (field x i 0=field x target 0 ∨ field x i 1=field x target 0) ∧ prior (field x i 2) (field x target 2)=true
  then field x i 3 else 0

def faceCost (q a : Option Parent) : ℕ :=
  match q,a with
  | some x,some y=>if y.peer=x.peer ∧ prior y.ticket x.ticket=true then y.units else 0
  | _,_=>0

def scanLaw (b paid : ℕ) (q a : Cell (b*5)) : Cell paid :=
  ((faceCost prior (unpack b q) (unpack b a):ℕ):Cell paid)

theorem scanEmpty (b paid : ℕ) : scanLaw prior b paid 0 0=0 := by
  have eqn:=unpack_literal b none (by trivial)
  rw [show encode b 5 (literal b none)=0 from DescentPacking.PackedMatch.Local.Gather.encode_zero b 5] at eqn
  simp [scanLaw,eqn,faceCost]

theorem exactFaces (x : Fields K b) (target : Fin K) :
    (∑i,faceCost prior (asked x target) (operands x i))=∑j,feeAt prior x target j := by
  rw [Fin.sum_univ_add,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change faceCost prior (asked x target) (operands x (Fin.castAdd K j)) +
    faceCost prior (asked x target) (operands x (Fin.natAdd K j))=feeAt prior x target j
  simp only [operands,Fin.addCases_left,Fin.addCases_right]
  by_cases dead : field x target 3=0
  · simp [asked,dead,faceCost,feeAt]
  by_cases absent : field x j 3=0
  · simp [located,absent,faceCost,asked,dead,query,feeAt]
  by_cases loop : field x j 0=field x j 1 <;> by_cases src : field x j 0=field x target 0 <;>
    by_cases dst : field x j 1=field x target 0 <;> by_cases cmp : prior (field x j 2) (field x target 2)=true <;>
    simp_all [asked,located,query,face,faceCost,feeAt]

def totalWord (q : Fin H→Fin G→Option Parent) (rows : Fin n→Fin H→Fin G→Option Parent)
    (fit : ∀h g,(∑i,faceCost prior (q h g) (rows i h g))<2^paid) (h : Fin H) (g : Fin G) : Cell paid := ⟨_,fit h g⟩

theorem sumCells (q : Fin H→Fin G→Option Parent) (rows : Fin n→Fin H→Fin G→Option Parent)
    (fit : ∀h g,(∑i,faceCost prior (q h g) (rows i h g))<2^paid) (r : Row H G M) :
    (∑i,(data (fun h g=>((faceCost prior (q h g) (rows i h g):ℕ):Cell paid)) r).val)=
      (data (totalWord prior q rows fit) r).val := by
  simp_rw [lanes_val]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases live : r.2.val*M+i.val<G
  · simp only [dite_eq_left live,totalWord,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have on:=Finset.single_le_sum (fun u _=>Nat.zero_le (faceCost prior (q r.1 ⟨_,live⟩) (rows u r.1 ⟨_,live⟩))) (Finset.mem_univ j)
    rw [Fin.val_cast_of_lt (on.trans_lt (fit _ _))]
  · simp [live]

theorem nat_fee (x : Fields K b) (j i : Fin K) (live : field x j 3≠0) : feeAt (fun a b=>decide (a<b)) x j i=fee x j i := by simp [feeAt,fee,live]
end
end Hierarchy.DescentResetSourceTicketCompare

end OAI
