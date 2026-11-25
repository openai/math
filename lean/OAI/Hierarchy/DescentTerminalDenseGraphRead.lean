import OAI.Hierarchy.DescentTerminalDenseWindowRAM
import OAI.Hierarchy.DescentTerminalGraphPositions
import OAI.Hierarchy.DescentTerminalPaidRows

namespace OAI
/-! # Two-load readback of genuine dense cable bits and exterior port bits -/

namespace Hierarchy.DescentTerminalDenseGraphRead
open Computability.BorderVNP.Crossing DescentTerminalPorts DescentTerminalDenseWindow
open Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

variable {D rows B n q p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (G : Network D P bits)

/-- The two reserved source rows beyond the true paid data are blank.
The same function handles a group with no remaining active slots. -/
def stream (pay : RowBit rows B→Bool) (k : ℕ) : Bool :=
  if h : k<rows*B then pay (finProdFinEquiv.symm ⟨k,h⟩) else false

private theorem stream_at (pay : RowBit rows B→Bool) (slot : RowBit rows B) :
    stream pay (finProdFinEquiv slot).val=pay slot := by
  unfold stream
  rw [dite_eq_left (finProdFinEquiv slot).isLt]
  exact congrArg pay (finProdFinEquiv.symm_apply_apply slot)

theorem raw_at (pay : RowBit rows B→Bool) (r : Fin rows) (j : Fin B) :
    wordBits B (dense B (stream pay) r.val) j=pay (r,j) := by
  simp only [dense,Equiv.apply_symm_apply]
  have ix : r.val*B+j.val=(finProdFinEquiv (r,j)).val := by
    change _=j.val+B*r.val
    ring
  rw [ix]
  exact stream_at pay (r,j)

theorem raw_sentinel (pay : RowBit rows B→Bool) (k : ℕ) (past : rows ≤ k) :
    dense B (stream pay) k=0 := by
  apply (wordBits B).injective
  funext j
  have h := Nat.mul_le_mul_right B past
  simp [dense,stream,show ¬(k*B+j.val<rows*B) by omega,wordBits_zero]

omit [Fintype P] in
theorem dense_at (code : G.Edge ↪ ℕ) (room : (∑e,G.width e) ≤ rows*B) (pay : RowBit rows B→Bool)
    (e : G.Edge) (j : Fin (G.width e)) :
    stream pay (ProtocolRAMPortRanks.«prefix» G.width code e+j.val)=
      takeBits G (denseBits G code room) pay e j := by
  let dest := denseBits G code room ⟨e,j⟩
  have addr := denseBits_address G code room e j
  change (finProdFinEquiv dest).val=_ at addr
  rw [←addr]
  exact stream_at pay dest

def publicStream (code : P ↪ ℕ) (outer : Ports bits) (addr : ℕ) : Bool :=
  if h : addr<∑z,bits z then
    let z := (ProtocolRAMPortRanks.enumerate bits code code.injective).symm ⟨addr,h⟩
    outer z.1 z.2
  else false

theorem public_at (code : P ↪ ℕ) (outer : Ports bits) (z : P) (j : Fin (bits z)) :
    publicStream code outer (ProtocolRAMPortRanks.«prefix» bits code z+j.val)=outer z j := by
  let k := ProtocolRAMPortRanks.enumerate bits code code.injective ⟨z,j⟩
  change publicStream code outer k.val=_
  unfold publicStream
  rw [dite_eq_left k.isLt]
  exact congrArg (fun address : (a : P) × Fin (bits a)=>outer address.1 address.2)
    ((ProtocolRAMPortRanks.enumerate bits code code.injective).symm_apply_apply ⟨z,j⟩)

def pieceSize (p length k : ℕ) := min p (length-k*p)

open ThreeFlat.Routing

/-- B=q*p is at least a constant fraction of the native width. Thus a
dense row per B true bits, together with two empty guard rows, has linear
cost measured in full machine words or full machine bits. -/
theorem dense_price (total B wordSize K : ℕ) (ratio : wordSize ≤ K*B) :
    (poolBatchCount total B+2)*wordSize ≤ K*(total+B)+2*wordSize := by
  have rounded : poolBatchCount total B*B ≤ total+B :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)
  have scaled := Nat.mul_le_mul_left (poolBatchCount total B) ratio
  have paid := Nat.mul_le_mul_left K rounded
  nlinarith only [scaled,paid]

def cableLengths (p length : ℕ) (k : Fin (poolBatchCount length p)) := pieceSize p length k.val

theorem prefix_eq_sum {m : ℕ} (len : Fin m→ℕ) (k : ℕ) :
    pref len k=∑j ∈ Finset.range k,lengthAt len j := by
  induction k with
  | zero=>simp [pref]
  | succ k ih=>rw [pref,ih,Finset.sum_range_succ]

theorem prefix_pieces (positive : 0<p) (length k : ℕ) :
    pref (cableLengths p length) k=min length (k*p) := by
  induction k with
  | zero=>simp [pref]
  | succ k ih=>
    rw [pref,ih,Nat.succ_mul]
    by_cases live : k<poolBatchCount length p
    · simp only [lengthAt,dite_eq_left live,cableLengths,pieceSize]
      omega
    · have cover := CallPool.count_le_batches_mul length p positive
      have larger := Nat.mul_le_mul_right p (Nat.le_of_not_lt live)
      rw [Nat.mul_comm p] at cover
      simp only [lengthAt,dite_eq_right live,Nat.add_zero]
      omega

theorem prefix_before (positive : 0<p) (length : ℕ) (k : Fin (poolBatchCount length p)) :
    pref (cableLengths p length) k.val=k.val*p := by
  rw [prefix_pieces positive,min_eq_right]
  by_contra! h
  have le : poolBatchCount length p ≤ k.val := by
    apply (ceilDiv_le_iff_le_mul positive).mpr
    exact (by simpa [Nat.mul_comm] using h.le)
  exact (Nat.not_le_of_lt k.isLt) le

theorem full_cable (positive : 0<p) (length : ℕ) :
    pref (cableLengths p length) (poolBatchCount length p)=length := by
  rw [prefix_pieces positive,min_eq_left]
  simpa only [Nat.mul_comm] using CallPool.count_le_batches_mul length p positive

private theorem active {length k : ℕ} (j : Fin p) :
    j.val<pieceSize p length k ↔ k*p+j.val<length := by
  unfold pieceSize
  have h := j.isLt
  omega

variable (len : Fin n→ℕ) (positive : 0<q*p) (small : ∀i,len i ≤ p) (base r : ℕ)

def fetched (all : ℕ→Bool) : Computability.VPVNP.BurstRAM.Word (q*p) :=
  let a := first len q base r/(q*p)
  word (format len positive small base r) (dense (q*p) all a) (dense (q*p) all (a+1))

omit [Fintype P] in
/-- The cluster allocator supplies the start/cutoff of the old cable
piece. The true contents are then read from the graph's global paid
assignment, without a per-finest-slot machine load. -/
theorem cable_slot (code : G.Edge ↪ ℕ) (room : (∑e,G.width e) ≤ rows*(q*p))
    (pay : RowBit rows (q*p)→Bool) (e : G.Edge) (k : ℕ) (s : Fin q)
    (start : begin len q base r s=ProtocolRAMPortRanks.«prefix» G.width code e+k*p)
    (length : lengthAt len (r*q+s.val)=pieceSize p (G.width e) k) (j : Fin p) :
    wordBits _ (fetched len positive small base r (stream pay)) (finProdFinEquiv (s,j))=
      TaggedShorterFields.slice p (takeBits G (denseBits G code room) pay e) k j := by
  change wordBits _ (word _ _ _) _=_
  rw [fetch]
  rw [length,start]
  unfold TaggedShorterFields.slice
  by_cases h : k*p+j.val<G.width e
  · rw [ite_eq_left ((active j).mpr h),dite_eq_left h,Nat.add_assoc]
    exact dense_at G code room pay e ⟨k*p+j.val,h⟩
  · rw [ite_eq_right (fun hj=>h ((active j).mp hj)),dite_eq_right h]

theorem exterior_slot (code : P ↪ ℕ) (outer : Ports bits) (z : P) (k : ℕ) (s : Fin q)
    (start : begin len q base r s=ProtocolRAMPortRanks.«prefix» bits code z+k*p)
    (length : lengthAt len (r*q+s.val)=pieceSize p (bits z) k) (j : Fin p) :
    wordBits _ (fetched len positive small base r (publicStream code outer)) (finProdFinEquiv (s,j))=
      TaggedShorterFields.slice p (outer z) k j := by
  change wordBits _ (word _ _ _) _=_
  rw [fetch,length,start]
  unfold TaggedShorterFields.slice
  by_cases h : k*p+j.val<bits z
  · rw [ite_eq_left ((active j).mpr h),dite_eq_left h,Nat.add_assoc]
    exact public_at code outer z ⟨k*p+j.val,h⟩
  · rw [ite_eq_right (fun hj=>h ((active j).mp hj)),dite_eq_right h]

end
end Hierarchy.DescentTerminalDenseGraphRead

end OAI
