import OAI.Computability.BorderVNP.PackedBankPacketBox

/-! # Binding paid-site staging to the shared cable bank

The relocated equality records tie each input bundle to its canonical physical
word and each staged lane to the corresponding input bit. Their valid
assignments are exactly the one canonical two-region bit string, regardless
of which directory slot contains the site's private matrix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidBinding

open private affine from OAI.Computability.BorderVNP.PackedBankBoxWords
open BankPacket BankPacket.Paid PaidBox CellSparse Crossing.CellBox

variable {n : ℕ} (w : Fin n → ℕ) (copies off id : ℕ) (physical : Fin n → ℕ)

/-- The complete actual operands of the merged paid-site emitter. -/
def fields : Input n (∑ r,w r) → ℕ :=
  Sum.elim (fun _ => off) (Sum.elim (fun _ => id) (Sum.elim (PaidBox.header w copies) physical))

/-- Physical cable-major bits in the shared cell bank, reindexed to single-copy
lane order, prior to the staging guesses. -/
def data (bank : ℕ → Bool) (i : Fin copies) (k : Fin (∑ r,w r)) : Bool :=
  let b := (finSigmaFinEquiv (n := w)).symm k
  bank (physical b.1 + i.val*w b.1 + b.2.val)

/-- The unique canonical bit string in this site's auxiliary slab. -/
def canonical (bank : ℕ → Bool) : ℕ → Bool :=
  stageBank (copies := copies) (inputBank w (data w copies physical bank)) (copies*∑ r,w r) (src w copies)

private theorem decode_shape :
    decode w (PaidBox.header w copies) =
      stageRecords copies (copies * ∑ r,w r) (src w copies) ++ [.box 0 (copies*∑ r,w r) copies (∑ r,w r)] := by
  unfold decode
  simp only [PaidBox.header,affine,stageRecords,stagePort,src,Nat.mul_comm copies,Nat.add_zero]

private theorem rows_shape :
    (rows w).map (RecordCode.read (fields w copies off id physical)) =
      ((stageRecords copies (copies * ∑ r,w r) (src w copies)).map (fun r => r.shift off) ++
        [.box id (off + copies*∑ r,w r) copies (∑ r,w r)]) ++
      List.ofFn (bundleTie w (fields w copies off id physical)) := by
  rw [read_rows]
  change ((decode w (PaidBox.header w copies)).map (fun r => withBoxID id (r.shift off))) ++ _ = _
  rw [decode_shape,List.map_append]
  congr 2
  simp [stageRecords,List.map_ofFn,Record.shift,withBoxID,Function.comp_def]

private theorem tie_iff (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (∀ r, (bundleTie w (fields w copies off id physical) r).Valid boxes bank) ↔
    ∀ (i : Fin copies) (k : Fin (∑ r,w r)), bank (off + (src w copies k).atBit i.val 0) =
      data w copies physical bank i k := by
  constructor
  · intro h i k
    let b := (finSigmaFinEquiv (n := w)).symm k
    have hv := h b.1 i.val i.isLt b.2.val b.2.isLt
    change bank (physical b.1 + i.val*w b.1 + b.2.val*1) =
      bank (off+start w b.1 * copies+i.val*w b.1+b.2.val*1) at hv
    change bank (off+(copies*start w b.1+b.2.val+i.val*w b.1+0*1)) = _
    dsimp only [data]
    simpa only [Nat.mul_one,Nat.zero_mul,Nat.add_zero,Nat.zero_add,Nat.mul_comm copies,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,b] using hv.symm
  · intro h r i hi l hl
    let k := finSigmaFinEquiv (n := w) ⟨r,⟨l,hl⟩⟩
    have hv := h ⟨i,hi⟩ k
    change bank (off + (copies*start w ((finSigmaFinEquiv (n := w)).symm k).1 +
      ((finSigmaFinEquiv (n := w)).symm k).2.val + i*w ((finSigmaFinEquiv (n := w)).symm k).1 + 0*1)) =
      bank (physical ((finSigmaFinEquiv (n := w)).symm k).1 + i*w ((finSigmaFinEquiv (n := w)).symm k).1 +
        ((finSigmaFinEquiv (n := w)).symm k).2.val) at hv
    have hback : (finSigmaFinEquiv (n := w)).symm k = ⟨r,⟨l,hl⟩⟩ :=
      (finSigmaFinEquiv (n := w)).symm_apply_apply _
    rw [hback] at hv
    simp only [Nat.zero_mul,Nat.add_zero] at hv
    change bank (physical r+i*w r+l*1) = bank (off+start w r*copies+i*w r+l*1)
    simpa only [Nat.mul_one,Nat.mul_comm copies,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hv.symm

private theorem stage_lt {d c : ℕ} (i : Fin c) (k : Fin d) : i.val*d+k.val < c*d := by
  simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using
    (finProdFinEquiv (i,k)).isLt

/-- Validity of the merged paid-site rows, expressed solely in terms of the box
ID's presence and the unique allocation of auxiliary bits. Canonical wire
addresses may refer to internal or supplied storage. -/
theorem valid_iff (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (∀ r ∈ (rows w).map (RecordCode.read (fields w copies off id physical)), r.Valid boxes bank) ↔
      id < boxes.length ∧ ∀ t < copies*(∑ r,w r) + copies*(∑ r,w r),
        bank (off+t) = canonical w copies physical bank t := by
  let base := copies*(∑ r,w r)
  let source := src w copies
  let old := inputBank w (data w copies physical bank)
  let localBank := fun t => bank (off+t)
  have hsrc (i : Fin copies) (k : Fin (∑ r,w r)) := src_lt w i k
  have hcanonical := stageBank_valid old base source hsrc boxes
  rw [rows_shape]
  simp only [List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton,List.forall_mem_ofFn_iff,
    Record.valid_shift]
  constructor
  · rintro ⟨⟨hs,hid⟩,ht⟩
    have hi := (tie_iff w copies off id physical boxes bank).mp ht
    refine ⟨hid, stageBank_unique old localBank base source hsrc (fun t h => ?_) boxes hs⟩
    obtain ⟨i,k,rfl⟩ := src_cover w h
    exact (hi i k).trans (inputBank_read w _ i k).symm
  · rintro ⟨hid,he⟩
    refine ⟨⟨(stageRecords_valid_iff _ _ _ _).2 ?_,hid⟩,(tie_iff w copies off id physical boxes bank).2 ?_⟩
    · intro i k
      have hlt := stage_lt i k
      have hp : base + (i.val*(∑ r,w r)+k.val) < base+base := Nat.add_lt_add_left hlt base
      have hr := (hsrc i k).trans_le (Nat.le_add_right base base)
      rw [he _ hp, he _ hr]
      exact (stageRecords_valid_iff _ _ _ _).1 hcanonical.2 i k
    · intro i k
      rw [he _ ((hsrc i k).trans_le (Nat.le_add_right base base))]
      exact (hcanonical.1 _ (hsrc i k)).trans (inputBank_read w _ i k)

end Packing.PaidBinding

end BorderVNP
end Computability
end OAI
