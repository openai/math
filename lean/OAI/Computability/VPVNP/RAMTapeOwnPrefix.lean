import OAI.Computability.VPVNP.RAMTapePublicGeometry
import OAI.Computability.VPVNP.RAMTapeSiteRecordWords
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeParameters

/-!
# Packing the processor's own parsed prefix

The prefix remains on the processor's input-reader stack. A fixed stack
routine extends these bits to the physical word width and counts their
actual length into a second word. It takes the prefix solely as data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.OwnPrefix

open BurstRAM TapeWord Function
open SiteRecordWords (Port)

private def counterPorts : UnaryWord.Port → Port
  | .src => .header
  | .pending => .count
  | .number => .addressWord
  | .unit => .width
  | .tmp => .tmp

private theorem counterPorts_inj : Injective counterPorts := by decide

private def count := FiniteRoutine.ofStackCode (UnaryWord.code 0) counterPorts .count (· == .done)

/-- Extend the copied prefix and count its bits. The same stack table is
used for every processor and every program on the input tape. -/
def program : FiniteRoutine Port :=
  ((SiteRecordWords.extendHeader.followedBy
    (WordCopy.mapWord .tmp .addressWord (fun _ => false) .width)).followedBy
    (WordCopy.mapWord .tmp .count (fun _ => true) .header)).followedBy count

/-- Step count for padding and packing the parsed prefix and computing its length as a word. -/
def steps (w P : ℕ) := (5*w + 13*P + 7) + (5*w+2) + (5*P+2) + (P*(4*w+3)+1)

theorem steps_le {w P : ℕ} (h : P ≤ w) : steps w P ≤ 43*(w+1)^2 := by
  have hp := Nat.mul_le_mul_right (4*w+3) h
  unfold steps
  nlinarith only [h, hp, Nat.zero_le w, Nat.zero_le (w*w)]

/-- `.header` is the saved prefix and `.width` the saved unary word width.
The two output fields receive its packed bits and its packed length. -/
theorem runs (s : Stacks Port) (w : ℕ) (hfit : (s .header).length ≤ w)
    (hw : s .width = List.replicate w true) (hb : s .headerWord = [])
    (hl : s .addressWord = []) (hc : s .count = []) (ht : s .tmp = []) :
    program.Runs (steps w (s .header).length) s
      (update (update s .headerWord (s .header ++ List.replicate (w-(s .header).length) false))
        .addressWord (wordBits (Fin.ofNat (2^w) (s .header).length))) := by
  let P := (s .header).length
  let v := update s Port.headerWord (s .header ++ List.replicate (w-P) false)
  let z := update v Port.addressWord (List.replicate w false)
  let ready := update z Port.count (List.replicate P true)
  let out := update v Port.addressWord (wordBits (Fin.ofNat (2^w) P))
  have hv := SiteRecordWords.extendHeader_runs s w hfit hw hb hc ht
  have hz : (WordCopy.mapWord .tmp .addressWord (fun _ => false) .width).Runs (5*w+2) v z := by
    have hr := WordCopy.mapWord_run Port.tmp Port.addressWord (fun _ => false)
      (by decide : Port.width ≠ .tmp) (by decide) (by decide) v (by simpa [v] using ht)
    simpa [v, z, hw, hl, List.map_const'] using hr
  have hm : (WordCopy.mapWord .tmp .count (fun _ => true) .header).Runs (5*P+2) z ready := by
    have hr := WordCopy.mapWord_run Port.tmp Port.count (fun _ => true)
      (by decide : Port.header ≠ .tmp) (by decide) (by decide) z (by simpa [z, v] using ht)
    simpa [P, ready, z, v, hc, List.map_const'] using hr
  have hcount : count.Runs (P*(4*w+3)+1) ready out := by
    apply FiniteRoutine.runs_ofStackCode_framed counterPorts_inj (normal := (· == .done))
      rfl rfl (fun q h => by cases q <;> first | rfl | contradiction)
      (UnaryWord.count_fixed 0 w P (s .header) (s .width) (hfit.trans_lt Nat.lt_two_pow_self))
    · intro j
      cases j <;> simp [counterPorts, ready, z, v, UnaryWord.store, ht]
    · intro j
      cases j <;> simp [counterPorts, out, v, UnaryWord.store, hc, ht]
    · intro j hj
      cases j <;> first | rfl | exact (hj .number rfl).elim | exact (hj .pending rfl).elim
  exact ((hv.followedBy hz).followedBy hm).followedBy hcount

theorem prefixWordBits (p : UniversalMachine.Program) {w : ℕ} (hf : (UniversalMachine.programPrefix p).length ≤ w) :
    UniversalMachine.programPrefix p ++ List.replicate (w-(UniversalMachine.programPrefix p).length) false =
      wordBits (SiteRecordWords.addressWord hf (PrimedInputRAM.Opcodes.packedPrefix p)) := by
  have h : wordBits (PrimedInputRAM.Opcodes.packedPrefix p) = UniversalMachine.programPrefix p := by
    simp [wordBits, PrimedInputRAM.Opcodes.packedPrefix]
  simpa only [h] using SiteRecordWords.address_bits hf (PrimedInputRAM.Opcodes.packedPrefix p)

end RAMTape.OwnPrefix

end VPVNP
end Computability
end OAI
