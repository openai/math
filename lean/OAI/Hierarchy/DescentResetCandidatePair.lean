import OAI.Hierarchy.DescentResetParentNumberSheet

namespace OAI
/-! # The two consecutive public sheets of receiver metadata and original parent numbers -/
namespace Hierarchy.DescentResetCandidatePair
open DescentResetFieldAssembler CandidateSheet DescentSIMDLookup DescentPackedColony DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {X s c p H G M w : ℕ}
abbrev Inputs (X s c p : ℕ) := Fin X→Sector s c p→Expr

def originalBase (base X K bits : ℕ) :=base+X*K*2^bits
def endAddress (base X K bits : ℕ) :=originalBase (originalBase base X K bits) X K bits
def prices (base X K bits H G M : ℕ) (e : ℕ→Expr) :=
  DescentPackedFlowBatch.passes base (H*chunks G M) (2^bits) e 0 (X*K)
local notation "K" => size s c p

def program (base bits H G M w : ℕ) (header raw : Inputs X s c p) :=
  (ProtocolRAM.program w (prices base X K bits H G M (terms header))).seq
    (ProtocolRAM.program w (prices (originalBase base X K bits) X K bits H G M (terms raw)))
def time (base bits H G M : ℕ) (header raw : Inputs X s c p) :=
  clock (prices base X K bits H G M (terms header))+clock (prices (originalBase base X K bits) X K bits H G M (terms raw))
def memory (base bits H G M : ℕ) (header raw : Inputs X s c p) (m : Memory w) :=
  result (prices (originalBase base X K bits) X K bits H G M (terms raw))
    (result (prices base X K bits H G M (terms header)) m)

private theorem frame_pass (base bits H G M : ℕ) (src : Inputs X s c p) (m : Memory w)
    (fits : ∀i j,(src i j).Fits w base) (rows : H*chunks G M≤2^bits)
    (top : originalBase base X K bits<2^w) :
    let ps:=prices base X K bits H G M (terms src)
    (ProtocolRAM.program w ps).Exec m (result ps m) (clock ps) ∧
    (∀i,i<base ∨ originalBase base X K bits≤ i → result ps m i=m i) := by
  intro ps
  have early (j : ℕ) (h : j<X*K) : (terms src j).Fits w base := by rw [terms,dite_eq_left h]; apply fits
  obtain ⟨exec,_,lower⟩:=DescentPackedFlowBatch.execute base (H*chunks G M) (2^bits) (X*K) (terms src) m early top rows
  refine ⟨exec,?_⟩
  rintro i (low|high)
  · exact lower _ low
  · exact DescentPackedFlowBatch.above base _ _ (terms src) m 0 _ i rows (by simpa [originalBase] using high)

theorem any (base bits H G M : ℕ) (header raw : Inputs X s c p) (m : Memory w)
    (fh : ∀x j,(header x j).Fits w base) (fr : ∀x j,(raw x j).Fits w base)
    (rows : H*chunks G M≤2^bits) (room : endAddress base X K bits<2^w) :
    (program base bits H G M w header raw).Exec m (memory base bits H G M header raw m) (time base bits H G M header raw) ∧
    (∀i,i<base ∨ endAddress base X K bits≤ i → memory base bits H G M header raw m i=m i) ∧
    CheapCode (program base bits H G M w header raw) := by
  let mid:=originalBase base X K bits
  have first:base≤ mid:=Nat.le_add_right ..
  have last:mid≤endAddress base X K bits:=Nat.le_add_right ..
  have one:=frame_pass base bits H G M header m fh rows (last.trans_lt room)
  have two:=frame_pass mid bits H G M raw (result (prices base X K bits H G M (terms header)) m)
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ first (fr x j)) rows room
  refine ⟨(by
    intro labels regs slots machine
    exact Procedure.Exec.then one.1 two.1 machine),?_,cheap_seq (@ProtocolRAM.program_cheap _ _) (@ProtocolRAM.program_cheap _ _)⟩
  rintro i (lo|hi)
  · exact (two.2 i (.inl (lo.trans_le first))).trans (one.2 i (.inl lo))
  · exact (two.2 i (.inr hi)).trans (one.2 i (.inr (last.trans hi)))

theorem bank_room (base bits : ℕ) (x : Fin X) (j : Fin K) (room : originalBase base X K bits<2^w) :
    (output base bits x j).Fits w (originalBase base X K bits) := by
  let i:=finProdFinEquiv (x,j)
  have le:=Nat.mul_le_mul_right (2^bits) (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at le
  change base+X*K*2^bits<2^w at room
  change 0<2^bits ∧ 2^bits<2^w ∧ base+i.val*2^bits+2^bits≤base+X*K*2^bits
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

theorem read_pair {bh bt : ℕ} (base bits : ℕ) (header raw : Inputs X s c p)
    (actual : Fin X→Fin K→Fin H→Fin G→Cell bh) (original : Fin X→Fin K→Fin H→Fin G→Cell bt) (m : Memory w)
    (fh : ∀x j,(header x j).Fits w base) (fr : ∀x j,(raw x j).Fits w base)
    (ah : ∀x j,Source (header x j) (actual x (index s c p j)) M m)
    (ar : ∀x j,Source (raw x j) (original x (index s c p j)) M m)
    (rows : H*chunks G M≤2^bits) (room : endAddress base X K bits<2^w) :
    let out:=memory base bits H G M header raw m
    (∀x j,Reads (output base bits x j) (actual x j) M out) ∧
      ∀x j,Reads (output (originalBase base X K bits) bits x j) (original x j) M out := by
  intro out
  let mid:=originalBase base X K bits
  let first:=result (prices base X K bits H G M (terms header)) m
  have le:base≤ mid:=Nat.le_add_right ..
  have last:mid≤endAddress base X K bits:=Nat.le_add_right ..
  have one:=CandidateSheet.run header base bits actual m fh ah rows (last.trans_lt room)
  have seen (x j) : Source (raw x j) (original x (index s c p j)) M first := by
    intro a
    exact (eval_below _ _ m first (fr x j) (fun i hi=>one.2.2.2 i (.inl hi))).trans (ar x j a)
  have two:=CandidateSheet.run raw mid bits original first
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ le (fr x j)) seen rows room
  refine ⟨?_,two.2.2.1⟩
  intro x j a
  refine Eq.trans (two.2.2.2 _ (.inl ?_)) (one.2.2.1 x j a)
  let q:=finProdFinEquiv (x,j)
  have h:=(row H G M a).isLt
  have bound:=Nat.mul_le_mul_right (2^bits) (Nat.succ_le_of_lt q.isLt)
  rw [Nat.succ_mul] at bound
  change base+q.val*2^bits+(row H G M a).val<base+X*K*2^bits
  omega

end
end Hierarchy.DescentResetCandidatePair

end OAI
