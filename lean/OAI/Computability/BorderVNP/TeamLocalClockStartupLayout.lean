import OAI.Computability.BorderVNP.TeamLocalClock
import OAI.Computability.BorderVNP.TeamLocalClockPC

/-!
# Wiring the successor decoder directly into the local processor

Register words land on the architectural ISA register stacks and the last
word lands on clock register two. Status, PC, scratch and unread incident
data have their own ports beside the existing local clock bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock.Startup

open VPVNP RAMTape BurstRAM TeamTapeHandoff

variable {p r k w : ℕ}

/-- Physical startup stacks beside the architecture and meter. -/
inductive Port (r k : ℕ) where
  | wire | width | tmp | tag | pc | clock (u : TeamLocalClock.Port r k)
  deriving DecidableEq, Fintype

/-- The first word is the PC, the middle words are ISA registers and the last is elapsed time. -/
def fieldPort : Fin (r + 2) → Port r k :=
  Fin.cons .pc (Fin.snoc (fun i => .clock (.isa (.reg i))) (.clock (.meter (.reg 2))))

/-- Installation of the canonical frame decoder at the startup bank. -/
def codecPorts : Codec.Port r → Port r k
  | .field i => fieldPort i
  | .wire => .wire
  | .width => .width
  | .tmp => .tmp
  | .tag => .tag

private def sourcePort : Port r k → Codec.Port r
  | .clock (.isa (.reg i)) => .field i.castSucc.succ
  | .clock (.meter (.reg _)) => .field (Fin.last r).succ
  | .pc => .field 0
  | .wire => .wire
  | .width => .width
  | .tmp => .tmp
  | .tag => .tag
  | .clock _ => .tmp

theorem codecPorts_injective : Function.Injective (@codecPorts r k) := by
  apply Function.LeftInverse.injective (g := sourcePort)
  intro a
  cases a with
  | field i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.lastCases ?_ (fun x => ?_) j <;>
        simp only [codecPorts, fieldPort, Fin.cons_succ, Fin.snoc_last, Fin.snoc_castSucc,
          sourcePort]
  | _ => rfl

/-- Architectural register values recovered from a canonical incoming frame. -/
def registers : Frame w r → Fin r → Word w
  | .live _ regs _ => regs
  | .accepted _ => fun _ => 0

private def pcWord : Frame w r → Word w
  | .live pc _ _ => pc
  | .accepted _ => 0

private theorem words_eq (f : Frame w r) :
    f.words = List.ofFn (Fin.cons (pcWord f) (Fin.snoc (registers f) f.elapsed)) := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [List.ofFn_succ']
  cases f <;> simp [Frame.words, Frame.elapsed, registers, pcWord, List.concat_eq_append,
    List.ofFn_const]

private theorem field_word (f : Frame w r) (i : Fin (r + 2)) :
    Codec.fields f i =
      wordBits ((Fin.cons (pcWord f) (Fin.snoc (registers f) f.elapsed) :
        Fin (r + 2) → Word w) i) := by
  unfold Codec.fields
  congr 1
  simp only [List.get_eq_getElem, Fin.val_cast, words_eq f, List.getElem_ofFn]

/-- Bank after a decoded frame has been installed, with the public local block and global count. -/
def decoded (pub : Fin k → Word w) (f : Frame w r) (H global max : Word w)
    (suffix : List Bool) : Stacks (Port r k)
  | .wire => suffix
  | .width => List.replicate w true
  | .tag => [f.halted]
  | .pc => wordBits (pcWord f)
  | .tmp => []
  | .clock (.isa u) => ISA.bank pub 0 (registers f) [] u
  | .clock (.meter u) => ISA.bank Fin.elim0 0 (chargeRegisters H global f.elapsed 0) [] u
  | .clock .stamp | .clock .copyScratch => []
  | .clock .maxBurst => wordBits max

/-- The entry stack bank contains raw incident bits, public initialization words and
empty decoder destinations. It depends only on the raw message and public parameters. -/
noncomputable def input (pub : Fin k → Word w) (H limit max : Word w) (raw : List Bool) :
    Stacks (Port r k) :=
  installStacks codecPorts (decoded pub (.accepted 0) H limit max []) (Codec.incoming r w raw)

theorem decoded_codec (pub : Fin k → Word w) (f : Frame w r) (H g max : Word w)
    (suffix : List Bool) (u : Codec.Port r) :
    decoded pub f H g max suffix (codecPorts u) = Codec.bank f suffix u := by
  cases u with
  | field i =>
    change decoded pub f H g max suffix (fieldPort i) = Codec.fields f i
    rw [field_word]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.lastCases ?_ (fun x => ?_) j <;>
        simp [fieldPort, decoded, ISA.bank, chargeRegisters]
  | _ => rfl

private theorem decoded_outside (pub : Fin k → Word w) (f : Frame w r) (H g max : Word w)
    (suffix : List Bool) (u : Port r k) (outside : ∀ v, codecPorts v ≠ u) :
    decoded pub f H g max suffix u = decoded pub (.accepted 0) H g max [] u := by
  cases u with
  | wire => exact (outside .wire rfl).elim
  | width => exact (outside .width rfl).elim
  | tmp => exact (outside .tmp rfl).elim
  | tag => exact (outside .tag rfl).elim
  | pc => exact (outside (.field 0) rfl).elim
  | clock u =>
    cases u with
    | isa u =>
      cases u with
      | reg i =>
        apply False.elim (outside (.field i.castSucc.succ) ?_)
        simp [codecPorts, fieldPort]
      | _ => rfl
    | meter u =>
      cases u with
      | reg i =>
        have h : i ≠ 2 := by
          rintro rfl
          apply outside (.field (Fin.last r).succ)
          simp [codecPorts, fieldPort]
        fin_cases i <;> first | rfl | contradiction
      | _ => rfl
    | _ => rfl

/-- Frame decoding installs real register and clock words into their final physical ports. -/
theorem decoded_install (pub : Fin k → Word w) (f : Frame w r) (H g max : Word w)
    (suffix : List Bool) :
    installStacks codecPorts (input pub H g max (f.bits ++ suffix)) (Codec.bank f suffix) =
      decoded pub f H g max suffix := by
  apply installStacks_frame codecPorts_injective (decoded_codec pub f H g max suffix)
  intro u hu
  exact (decoded_outside pub f H g max suffix u hu).trans (installStacks_outside _ _ hu).symm

/-- A live frame gives exactly the bank expected by the local clock dispatcher. -/
theorem decoded_clock (pub : Fin k → Word w) (pc : Fin p) (z elapsed : Word w)
    (regs : Fin r → Word w) (H g max : Word w) (suffix : List Bool) (u : TeamLocalClock.Port r k) :
    decoded pub (.live z regs elapsed) H g max suffix (.clock u) =
      TeamLocalClock.bank pub ⟨pc, regs⟩ H g elapsed max u := by
  cases u <;> rfl

/-- Updating the clock bank leaves the instruction fields and unread link suffix in place. -/
theorem meter_install (pub : Fin k → Word w) (f : Frame w r) (H g g' max : Word w)
    (suffix : List Bool) :
    installStacks (Port.clock ∘ TeamLocalClock.Port.meter) (decoded pub f H g max suffix)
      (ISA.bank Fin.elim0 0 (chargeRegisters H g' f.elapsed 0) []) =
      decoded pub f H g' max suffix := by
  apply installStacks_frame (fun _ _ h => TeamLocalClock.Port.meter.inj (Port.clock.inj h))
  · intro u; rfl
  · intro u hu
    cases u with
    | clock u =>
      cases u with
      | meter v => exact (hu v rfl).elim
      | _ => rfl
    | _ => rfl

end TeamLocalClock.Startup

end BorderVNP
end Computability
end OAI
