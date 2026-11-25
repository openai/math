import OAI.Computability.BorderVNP.DiagonalTallyScatterLoop
import OAI.Computability.VPVNP.RAMTapeWord

/-! # Native little-endian packing of broadcast subtotal bits

Registers 50 through 53 contain the first bit address, word count, bits per
word, and first destination address. Register 63 contains one. The fragment
consumes consecutive one-word bits, advances both cursors, and verifies the
encoding and machine width on the actual instruction path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyBits
open scoped Fin.CommRing

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (word word_val TraceOK effect effect_runs)

/-- Consume one Boolean digit and advance its address, power of two, and position. -/
def digitUpdate : Code := .block [.binary .mul 60 59 57, .binary .add 56 56 60,
  .binary .add 57 57 57, .binary .add 50 50 63, .binary .add 55 55 63]

/-- Read and reject a nonbinary digit before arithmetic uses it. -/
def bitBody : Code := .seq (.load 59 50) (.ifLt 63 59 .reject digitUpdate)

/-- Start a subtotal with zero bits, accumulator zero, and place value one. -/
def startWord : Code := .block [.constant 55 0, .constant 56 0, .copy 57 63]

/-- Store the packed word and advance the destination and completed-word counter. -/
def finishWord : Code := .block [.store 53 56, .binary .add 53 53 63, .binary .add 54 54 63]

/-- Pack one word from its low bit upwards. -/
def wordBody : Code := .seq startWord (.seq (.whileLt 55 52 bitBody) finishWord)

/-- For positive width test the highest requested place value. Shifting beyond the
physical word width gives zero, which rejects. Zero requested bits always fit. -/
def widthGuard : Code := .seq (.constant 60 0) (.ifEq 52 60 .nop
  (.seq (.binary .sub 61 52 63) (.seq (.binary .shiftLeft 61 63 61)
    (.ifEq 61 60 .reject .nop))))

/-- Validate the width and pack every claimed subtotal. -/
def pack : Code := .seq widthGuard (.seq (.constant 54 0) (.whileLt 54 51 wordBody))

/-- Bits laid out consecutively in the physical input memory, one full word each. -/
def BitsAt {w : ℕ} (m : Memory w) : ℕ → List Bool → Prop
  | _, [] => True
  | p, b :: bs => (m p).val = b.toNat ∧ BitsAt m (p+1) bs

/-- Register bank agreement outside a finite list of destinations. -/
def Preserves {w : ℕ} (d : List Reg) (s t : Bank w) : Prop := ∀ i ∉ d, t i = s i

/-- Word registers touched by the digit loop. -/
def digitScratch : List Reg := [50,55,56,57,59,60]

/-- Word registers touched by the complete packing fragment. -/
def scratch : List Reg := [50,53,54,55,56,57,59,60,61]

/-- Untouched registers are preserved across a sequence of instructions. -/
theorem Preserves.trans {w : ℕ} {d : List Reg} {s t z : Bank w}
    (h : Preserves d s t) (h' : Preserves d t z) : Preserves d s z :=
  fun i hi => (h' i hi).trans (h i hi)

private theorem word_eq {w a : ℕ} (x : Word w) (h : x.val = a) : x = word w a := by
  rw [← h]
  exact Fin.ext (word_val w _ x.isLt).symm

/-- One legal bit consumes seven native ticks. Arithmetic takes place in words,
so the last doubling may wrap without altering the accumulated result. -/
theorem bitBody_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (b : Bool) (hone : (s 63).val = 1)
    (hb : (m (s 50).val).val = b.toNat) :
    ∃ es t, Runs pub mac bitBody s m es t m ∧ TraceOK es [] 7 ∧ Preserves digitScratch s t ∧
      t 50 = s 50+1 ∧ t 55 = s 55+1 ∧ t 56 = s 56 + word w b.toNat * s 57 ∧ t 57 = s 57+s 57 := by
  let u := Function.update s (59 : Reg) (m (s 50).val)
  let e := effect false u m digitUpdate
  have h63 : s 63 = 1 := word_eq _ hone
  have h59 : m (s 50).val = word w b.toNat := word_eq _ hb
  have hle : ¬ u 63 < u 59 := by
    change ¬ (u 63).val < (u 59).val
    cases b <;> simp [u, hone, hb]
  have update := effect_runs pub mac false u m digitUpdate (by decide)
  have hm : e.mem = m := rfl
  change Runs pub mac digitUpdate u m e.trace e.bank e.mem at update
  rw [hm] at update
  have step := Runs.seq (Runs.load pub mac 59 50 s m)
    (Runs.ifLt (a := .reject) (x := 63) (y := 59) (b := digitUpdate)
      (s := u) (by simpa only [ite_eq_right hle] using update))
  refine ⟨_,e.bank,step,?_,?_,?_⟩
  · simp [e, digitUpdate, Code.block, effect, TraceOK, tick]
  · intro i hi
    simp only [digitScratch,List.mem_cons,not_or] at hi
    simp [e,digitUpdate,Code.block,effect,u,Function.update,hi]
  · simp [e,digitUpdate,Code.block,effect,u,Function.update,BinaryOp.eval,h63,h59]

/-- The digit loop at an arbitrary current position adds the natural value of the
remaining little-endian bits times the current place. It performs no writes. -/
theorem bitLoop_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bs : List Bool) {p j width : ℕ}
    (hp : (s 50).val = p) (hj : (s 55).val = j) (hw : (s 52).val = width) (hone : (s 63).val = 1)
    (hlen : j+bs.length = width) (hfit : p+bs.length < 2^w) (hbits : BitsAt m p bs) :
    ∃ es t, Runs pub mac (.whileLt 55 52 bitBody) s m es t m ∧ TraceOK es [] (8*bs.length+1) ∧
      Preserves digitScratch s t ∧ (t 50).val = p+bs.length ∧
      t 56 = s 56 + s 57 * word w (VPVNP.TapeWord.value bs) := by
  induction bs generalizing s p j with
  | nil =>
    have heq : s 55 = s 52 := Fin.ext (by simp_all)
    refine ⟨_,s,.whileDone (by simp [heq]),?_,(fun _ _ => rfl),by simpa using hp,?_⟩
    · simp [TraceOK,tick]
    · simp [VPVNP.TapeWord.value]
  | cons b bs ih =>
    obtain ⟨hb,hrest⟩ := hbits
    obtain ⟨es,t,run,htrace,hpres,hp',hj',ha',hv'⟩ := bitBody_runs pub mac s m b hone (hp ▸ hb)
    have hval1 : (1 : Word w).val = 1 := by
      rw [← show s 63 = 1 from word_eq _ hone,hone]
    have hp'' : (t 50).val = p+1 := by
      rw [hp', Fin.val_add_eq_of_add_lt (by simp only [hp,hval1]; simp at hfit; omega), hp,hval1]
    have hj'' : (t 55).val = j+1 := by
      have hbound : width < 2^w := hw ▸ (s 52).isLt
      rw [hj', Fin.val_add_eq_of_add_lt (by simp only [hj,hval1]; simp at hlen; omega),hj,hval1]
    have hguard : s 55 < s 52 := by
      change (s 55).val < (s 52).val
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨fs,z,next,hft,hpZ,hptr,hacc⟩ := ih t hp'' hj'' ((congrArg Fin.val (hpres 52 (by decide))).trans hw)
      ((congrArg Fin.val (hpres 63 (by decide))).trans hone) (by simp at hlen; omega)
      (by simp at hfit; omega) hrest
    refine ⟨_,z,.whileStep hguard run next,?_, hpres.trans hpZ, ?_, ?_⟩
    · have he : 7+(8*bs.length+1)+1 = 8*(b::bs).length+1 := by simp; omega
      simpa only [he, List.nil_append] using (htrace.append hft).cons_tick
    · simp only [List.length_cons]; omega
    · rw [hacc,ha',hv']
      rw [VPVNP.TapeWord.value, DiagonalResidueRAM.word_add,
        show word w (2 * VPVNP.TapeWord.value bs) = word w 2 * word w (VPVNP.TapeWord.value bs) from Fin.ext (Nat.mul_mod ..),
        DiagonalResidueRAM.word_two]
      ring

end DiagonalTallyBits

end BorderVNP
end Computability
end OAI
