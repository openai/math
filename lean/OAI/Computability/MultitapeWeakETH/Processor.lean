import OAI.Computability.MultitapeWeakETH.BlockSubtraction
import OAI.Computability.MultitapeWeakETH.Payload
import OAI.Computability.MultitapeWeakETH.Terminals
import OAI.Computability.MultitapeWeakETH.Tables

/-! # Local correction, borrow propagation and folded payload coordinates -/

namespace OAI.Computability.MultitapeWeakETH.Difference

open VPVNP
open scoped Classical
noncomputable section

/-- A physical block message is low bit first. Missing high bits are zero. -/
def message (b j : ℕ) (xs : List Bool) : Word b :=
  fun r => xs[j*b+r.val]?.getD false

def unpack (n j : ℕ) {b : ℕ} (bits : Word b) : List Bool :=
  (List.ofFn bits).take (n-j*b)

private theorem get_chunk {xs : List Bool} {s k r : ℕ} (hr : r < k) :
    (chunk s k xs)[r]? = xs[s+r]? := by simp [chunk,hr]

theorem unpack_message {n : ℕ} (b j : ℕ) (xs : List Bool) (size : xs.length = n) :
    unpack n j (message b j xs) = chunk (j*b) b xs := by
  apply List.ext_getElem
  · simp [unpack,chunk,size,min_comm]
  · intro r hl hr
    have rb : r < b := by simpa [chunk,List.length_take] using (lt_of_lt_of_le hr (by simp [chunk]))
    have ix : j*b+r < xs.length := by simp [chunk] at hr; omega
    simp [unpack,message,chunk,List.getElem?_eq_getElem ix]

/-- The local mask corrects an approximate word back to the exact product. -/
def correction {b : ℕ} (raw mask : Word b) : Word b := fun r => raw r ^^ mask r

def maskFor {b : ℕ} (raw target : Word b) : Word b := fun r => raw r ^^ target r

@[simp] theorem correction_mask {b : ℕ} (raw target : Word b) :
    correction raw (maskFor raw target) = target := by
  funext r
  cases hr : raw r <;> cases ht : target r <;> simp [correction,maskFor,hr,ht]

/-- Process one pair of corrected blocks. Outgoing difference bits are
zero-padded only after subtracting the actual (possibly short) block. -/
def process (n j : ℕ) {b : ℕ} (left right maskL maskR : Word b) (carry : Bool) : Word b × Bool :=
  let ans := TapeWord.subScan carry (unpack n j (correction left maskL)) (unpack n j (correction right maskR))
  (message b 0 ans.1,ans.2)

theorem process_residues {n : ℕ} (b j : ℕ) (x y : Fin (2^n)) (rawL rawR : Word b) :
    let X := BurstRAM.wordBits x
    let Y := BurstRAM.wordBits y
    process n j rawL rawR (maskFor rawL (message b j X)) (maskFor rawR (message b j Y))
        (borrow X Y (j*b)) =
      (message b j (BurstRAM.wordBits (x-y)),borrow X Y ((j+1)*b)) := by
  dsimp only
  simp only [process,correction_mask,unpack_message _ _ _ (BurstRAM.length_wordBits _),
    subtract_residues,Nat.succ_mul]
  apply Prod.ext
  · funext r
    simp only [message,zero_mul,zero_add,get_chunk r.isLt]
  · rfl

/-- One payload bit is read from its own position in the folded difference block. -/
theorem payload_bit {n s L : ℕ} (value : Fin (2^n)) (word : Fin (2^L))
    (interval : (value.val/2^s)%(2^L) = word.val) (j : Fin L) :
    value.val.testBit (s+j.val) = word.val.testBit j.val := by
  rw [← interval,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  simp [j.isLt,add_comm]

theorem message_bit {n b : ℕ} (hb : 0 < b) (x : Fin (2^n)) (i : ℕ) (hi : i < n) :
    message b (i/b) (BurstRAM.wordBits x) ⟨i%b,Nat.mod_lt _ hb⟩ = x.val.testBit i := by
  have idx : i/b*b+i%b = i := Nat.div_add_mod' i b
  have bound : i < (List.ofFn (residueWord n x)).reverse.length := by simpa using hi
  rw [message,idx,← residueWord_reverse,List.getElem?_eq_getElem bound,Option.getD_some,
    List.getElem_reverse,List.getElem_ofFn,residueWord_digit]
  simp only [List.length_ofFn]
  congr 1
  omega

/-- The two processors send the displayed bit to terminals separated by exactly
the shift, including payloads with a nonaligned starting offset. -/
theorem shifted_terminal {N b q : ℕ} [NeZero N] [NeZero b] (t : Fin N) (s : ℕ)
    (j : Fin (q*(N*b))) :
    Fin.ofNat N ((s+t.val*b+j.val)/b) = foldedTerminal s j + t := by
  apply Fin.ext
  simp only [Fin.val_ofNat,Fin.val_add,foldedTerminal_val]
  rw [show s+t.val*b+j.val = (s+j.val)+b*t.val by ring,Nat.add_mul_div_left _ _ (NeZero.pos b)]
  rw [Nat.mod_add_mod]

end
end OAI.Computability.MultitapeWeakETH.Difference
