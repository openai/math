import OAI.Computability.BorderVNP.DiagonalResidueRAMSources
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-!
# Installing the second part of the evaluator's scratch frame

The distributed literal stream starts with the residue reader's payload.
The next 81 words, at the physical width, initialize frame positions 31
through 111. The reference column follows in the same stream. This routine
packs only the 81 words, and all other shared words retain their contents.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ExtendedFrame

open VPVNP VPVNP.BurstRAM
open DiagonalTallyBits

/-- Read the delivered bit-bank base, residue payload word count, and machine
width. Compute the suffix address and initialize the ordinary packing ABI. -/
def setup : Code := .block [
  readFrame 48 62 63 28, readFrame 49 62 63 29, readFrame 52 62 63 30,
  .binary .mul 49 49 52, .binary .add 50 48 49, .publicWord 53 0,
  .constant 51 31, .binary .add 53 53 51, .constant 51 81, .constant 63 1]

/-- The fixed instruction fragment installing frame slots 31 through 111. -/
def install : Code := .seq setup pack

/-- The three length-only parameters installed by the preceding ordinary boot. -/
def Loaded (pub : Arg → ℕ) (mem : ℕ → ℕ) (dense entryWords width : ℕ) : Prop :=
  frameField pub mem 28 = dense ∧ frameField pub mem 29 = entryWords ∧ frameField pub mem 30 = width

/-- The dense suffix is in RAM after the entire extended frame. -/
structure Fits (w frame dense entryWords : ℕ) : Prop where
  /-- One sentinel beyond the frame also fits. -/
  frameBound : frame+112 < 2^w
  /-- Actual source and destination do not overlap. -/
  separate : frame+112 ≤ dense
  /-- All 81 machine-word encodings and their end sentinel fit. -/
  inputBound : dense+entryWords*w+81*w < 2^w

private theorem readFrame_safe {w : ℕ} (d : Reg) (f : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) :
    (readFrame d 62 63 f).safeReadOnly w pub mem s ↔ pub 0+f.val < 2^w := by
  simp (config := {decide:=true}) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits]
  omega

private theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (dense entryWords : ℕ)
    (loaded : Loaded (readings pub) (readings m) dense entryWords w)
    (fit : Fits w (pub 0).val dense entryWords) :
    ∃ es t, Runs pub mac setup s m es t m ∧ traceCost es ≤ setup.slots ∧
      readings t 50 = dense+entryWords*w ∧ readings t 53 = (pub 0).val+31 ∧
      readings t 51 = 81 ∧ readings t 52 = w ∧ readings t 63 = 1 := by
  obtain ⟨h28,h29,h30⟩ := loaded
  have bound : readings pub 0+112 < 2^w := fit.frameBound
  have source := fit.inputBound
  have hw : w ≠ 0 := by rintro rfl; simp at bound
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide:=true}) [setup,Code.block,Code.safeReadOnly,Code.evalNat,readFrame_safe,
      readFrameFixed,addressOp,addressOpFits,h28,h29,h30]
    omega
  obtain ⟨es,t,run,cost,he⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨es,t,run,cost,?_⟩
  rw [he]
  simp (config := {decide:=true}) [setup,Code.block,Code.evalNat,readFrameFixed,addressOp,h28,h29,h30,readings]

/-- Exact scratch image after the fixed-width words have been decoded. -/
def installed {w : ℕ} (m : Memory w) (frame : ℕ) (fields : Fin 81 → Word w) : Memory w :=
  outputMemory m (frame+31) ((List.ofFn fields).map BurstRAM.wordBits)

/-- Every addressed frame word receives its own decoded field. -/
theorem installed_at {w : ℕ} (m : Memory w) (frame : ℕ) (fields : Fin 81 → Word w)
    (i : Fin 81) : installed m frame fields (frame+31+i.val) = fields i := by
  have all := DiagonalResidueRAM.words_after_pack m (frame+31) (List.ofFn fields)
  exact (all ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩).trans (by simp only [List.getElem_ofFn])

/-- All addresses outside the new frame preserve their former contents. -/
theorem installed_outside {w : ℕ} (m : Memory w) (frame : ℕ) (fields : Fin 81 → Word w)
    (a : ℕ) (h : a < frame+31 ∨ frame+112 ≤ a) : installed m frame fields a = m a :=
  outputMemory_outside m _ a _ (by simpa [Nat.add_assoc] using h)

/-- Actual native instructions install all 81 scalar fields, preserve the
other words, spend O(w) ticks and take no private guesses or negative signs. -/
theorem install_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (dense entryWords : ℕ) (fields : Fin 81 → Word w)
    (loaded : Loaded (readings pub) (readings m) dense entryWords w)
    (fit : Fits w (pub 0).val dense entryWords)
    (input : WordsAt m (dense+entryWords*w) ((List.ofFn fields).map BurstRAM.wordBits)) :
    ∃ es t, Runs pub mac install s m es t (installed m (pub 0).val fields) ∧
      traceCost es ≤ setup.slots+8*81*(w+1)+8 ∧ ∀ e ∈ es, e.choices = [] ∧ e.sign = .plus := by
  obtain ⟨fs,t,first,cost,h50,h53,h51,h52,h63⟩ := setup_run pub mac s m dense entryWords loaded fit
  let xs := (List.ofFn fields).map BurstRAM.wordBits
  have length : xs.length = 81 := by simp [xs]
  have wordLengths : ∀ b ∈ xs, b.length = w := by
    intro b hb
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
    simp [BurstRAM.wordBits]
  obtain ⟨gs,z,last,trace,_,_,_⟩ := pack_runs pub mac t m xs h50 h53 (h51.trans length.symm) h52
    h63 le_rfl wordLengths (by rw [length]; exact fit.inputBound)
    (by rw [length]; exact fit.frameBound) (Or.inr (by rw [length]; have := fit.separate; omega)) input
  let run : Runs pub mac install s m (fs++gs) z (installed m (pub 0).val fields) := first.seq last
  refine ⟨_,z,run,?_,run.unsigned_events (by decide)⟩
  have len := last.deterministic_cost (by decide)
  have bound := ticks_le 81 w
  have ct := trace.1
  rw [length] at ct
  change RAMBuckets.cost _ (fs++gs) ≤ _
  rw [RAMBuckets.cost_append]
  change traceCost fs + traceCost gs ≤ _
  omega

/-- If the 81-word suffix was placed in the specified processor literals, the
actual advice copy satisfies the input premise of the decoder. -/
theorem suffix_delivered {w : ℕ} (f : BroadcastFrame) (a : AdviceLayout)
    (before after : Memory w) (entryWords : ℕ) (fields : Fin 81 → Word w)
    (image : readings after = a.copied f (readings before) a.count)
    (room : entryWords*w + (((List.ofFn fields).map BurstRAM.wordBits).flatten.length) ≤ a.count)
    (bits : ∀ i : Fin (((List.ofFn fields).map BurstRAM.wordBits).flatten.length),
      (before (a.src f (entryWords*w+i.val))).val =
        (((List.ofFn fields).map BurstRAM.wordBits).flatten[i.val]).toNat) :
    WordsAt after (a.dst+entryWords*w) ((List.ofFn fields).map BurstRAM.wordBits) := by
  apply DiagonalResidueRAM.wordsAt_of_flat
  intro i
  have hi := i.isLt
  change readings after (a.dst+entryWords*w+i.val) = _
  rw [Nat.add_assoc,image,a.copied_at f (readings before) (by omega)]
  exact bits i

end RoutingISA.ExtendedFrame

end BorderVNP
end Computability
end OAI
