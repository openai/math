import OAI.Computability.VPVNP.LiveEvaluatorAdviceFrameSetup
import OAI.Computability.VPVNP.LiveEvaluatorAdviceFrameStore
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.PrimedCounterCallPaths
import OAI.Computability.VPVNP.PrimedStackRAMLeafVisit

/-!
# Publishing the four midpoint operand frames

The native initializer reads the packed prefix length at offset 22, checks
its capacity, and writes the operands of the prefix packer, input copy,
runtime skeleton and exponent scatter. Their frames start at offsets 0, 8,
13 and 17. The three holes at 5–7 and the stored length at 22 are preserved.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceFrames

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The register-to-frame assignment for the four midpoint workers, reserving holes at offsets
5 through 7. -/
def slots : List (Option (Fin 32)) :=
  [some 16,some 8,some 6,some 15,some 17,none,none,none,
   some 9,some 10,some 8,some 6,some 15,
   some 11,some 12,some 19,some 20,
   some 13,some 14,some 21,some 11,some 12]

/-- Compute the midpoint operands and store them into their assigned slots in the shared frame. -/
def body : FrameCode := .seq setup (storeFlow slots)

/-- One deterministic native call. Its normal exit accepts the stage. -/
def template := body.template none

/-- The five operands for packing the evaluator prefix, including source, destination, field
width, actual bit count, and row count. -/
def prefixFrame (pub : FramePub w) (m : Memory w) : Fin 5 → Word w :=
  ![pub 0+pub 2, pub 4, pub 2, actualLength pub m, prefixRows pub m]

/-- The five words supplying the input-copy worker with its input size, tape location, packed
advice location, field width, and prefix length. -/
def copyFrame (pub : FramePub w) (m : Memory w) : Fin 5 → Word w :=
  ![pub 5, pub 6, pub 4, pub 2, actualLength pub m]

/-- The runtime skeleton's two size parameters, computed base address, and total length. -/
def skeletonFrame (pub : FramePub w) (m : Memory w) : Fin 4 → Word w :=
  ![pub 7, pub 8, runtimeBase pub m, skeletonSize pub]

/-- The five operands used to scatter production exponents into the runtime area. -/
def scatterFrame (pub : FramePub w) (m : Memory w) : Fin 5 → Word w :=
  ![pub 9, pub 10, scatterBase pub m, pub 7, pub 8]

/-- The external memory after computing and writing all four midpoint operand frames. -/
def published (pub : FramePub w) (m : Memory w) : Memory w :=
  frameMemory slots (ready pub (fun _ => 0) m) m

/-- The successful initializer's complete load, calculation, and frame-store event sequence. -/
def events (pub : FramePub w) (m : Memory w) : List (Event w) :=
  setupEvents pub m ++ storeEvents slots (ready pub (fun _ => 0) m)

private theorem body_exec (pub : FramePub w) (st : Word w) (m : Memory w)
    (hcap : actualLength pub m ≤ pub 1) (hw : 0 < pub 2) :
    Flow.Exec pub st body (fun _ => 0) m (events pub m)
      (storeRegs slots (ready pub (fun _ => 0) m)) (published pub m) :=
  .seq ((setup_iff pub st _ m _ _ _).mpr ⟨hcap,hw,rfl,rfl,rfl⟩) (store_exec ..)

/-- The sole length read and 19 operand writes are the only external probes. -/
theorem events_cost (pub : FramePub w) (m : Memory w) :
    choiceBits (events pub m) = [] ∧ countProbes (events pub m) = 20 ∧ (events pub m).length = 82 := by
  obtain ⟨hb,hp,hl⟩ := storeEvents_counts slots (ready pub (fun _ => 0) m)
  have h0 : choiceBits (setupEvents pub m) = [] := rfl
  have h1 : countProbes (setupEvents pub m) = 1 := rfl
  have h2 : (setupEvents pub m).length = 40 := rfl
  simp only [events, Flow.choiceBits_append, PrimedStackRAM.probes_append, List.length_append,
    h0,h1,h2,hb,hp,hl]
  decide

theorem execute_frames (pub : FramePub w) (st : Word w) (m : Memory w)
    (hcap : actualLength pub m ≤ pub 1) (hw : 0 < pub 2) :
    let machine := template.instantiate w pub
    execute machine.program 83 (machine.program.start st) m [] = some ⟨events pub m,none⟩ ∧
      after m (events pub m) = published pub m := by
  have he := body_exec pub st m hcap hw
  have ⟨hb,_,hl⟩ := events_cost pub m
  constructor
  · apply (Flow.template_execute_iff body none pub st (fun _ => 0) (fun _ => 0) m 83 [] _).mpr
    exact ⟨_,_,he,rfl,by simp [hl],hb⟩
  · exact PrimedCounter.Call.exec_memory he

/-- A malformed length or a zero word-width parameter rejects at any fuel and on every stream. -/
theorem reject_frames (pub : FramePub w) (st : Word w) (m : Memory w) (bs : List Bool) (fuel : ℕ)
    (hb : pub 1 < actualLength pub m ∨ pub 2 = 0) :
    let machine := template.instantiate w pub
    execute machine.program fuel (machine.program.start st) m bs = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro r hr
  obtain ⟨_,_,he,-⟩ := (Flow.template_execute_iff body none pub st _ _ m fuel bs r).mp hr
  generalize hev : r.events = es at he
  cases he with
  | seq hs _ =>
    obtain ⟨hl,hw,-⟩ := (setup_iff pub st _ m _ _ _).mp hs
    rcases hb with h | h
    · exact (not_lt_of_ge hl) h
    · rw [h] at hw; exact (lt_irrefl _) hw

/-- The exact stored frame payloads as read by the dynamic operand adapter. -/
structure PublishedAt (pub : FramePub w) (m out : Memory w) : Prop where
  prefixWord (i : Fin 5) : out ((pub 3).val + i.val) = prefixFrame pub m i
  copyWord (i : Fin 5) : out ((pub 3).val + 8 + i.val) = copyFrame pub m i
  skeletonWord (i : Fin 4) : out ((pub 3).val + 13 + i.val) = skeletonFrame pub m i
  scatterWord (i : Fin 5) : out ((pub 3).val + 17 + i.val) = scatterFrame pub m i

theorem published_at (pub : FramePub w) (m : Memory w) (hw : 0 < w) (hfit : (pub 3).val+22 ≤ 2^w) :
    PublishedAt pub m (published pub m) := by
  let r := ready pub (fun _ => 0) m
  have h1 : (r 1).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')
  have hv (i : ℕ) (hi : i < 22) :
      published pub m ((pub 3).val+i) = ((slots[i]'hi).map r).getD (m ((pub 3).val+i)) :=
    frameMemory_at slots r m h1 hfit (by decide) i hi
  constructor <;> intro i <;> fin_cases i <;>
    simp only [Nat.add_assoc] <;> rw [hv _ (by decide)] <;> rfl

theorem published_outside (pub : FramePub w) (m : Memory w) (hw : 0 < w)
    (hfit : (pub 3).val+22 ≤ 2^w) (k : ℕ) (hk : k < (pub 3).val ∨ (pub 3).val+22 ≤ k) :
    published pub m k = m k :=
  frameMemory_outside slots _ m (Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')) hfit (by decide) k hk

end LiveEvaluatorAdviceFrames

end VPVNP
end Computability
end OAI
