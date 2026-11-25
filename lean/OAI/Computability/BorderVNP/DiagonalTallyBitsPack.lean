import OAI.Computability.BorderVNP.DiagonalTallyBitsLoop
import OAI.Computability.BorderVNP.DiagonalTallyBitsWidth

/-! # Exact native trace and output words of the broadcast decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyBits

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (word word_val TraceOK)
open VPVNP.TapeWord (value value_lt)

variable {w : ℕ}

/-- Outside the destination interval the final memory agrees with its input. -/
theorem outputMemory_outside (m : Memory w) (d a : ℕ) (xs : List (List Bool))
    (h : a < d ∨ d+xs.length ≤ a) : outputMemory m d xs a = m a := by
  induction xs generalizing d m with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at h
    rw [outputMemory, ih _ _ (by omega),Function.update_of_ne (by omega)]

/-- The output word at each coordinate is the decoded little-endian value of exactly
its own `width` bits, including when the width is zero. -/
theorem outputMemory_word (m : Memory w) (d : ℕ) (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length) :
    outputMemory m d xs (d+i) = word w (value xs[i]) := by
  induction xs generalizing m d i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [outputMemory,outputMemory_outside _ _ _ _ (.inl (Nat.lt_succ_self _))]
    | succ i =>
      have hi' : i < bs.length := by simpa using hi
      simpa [outputMemory,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (Function.update m d (word w (value b))) (d+1) i hi'

/-- The raw value fits without truncation under the checked machine-width condition. -/
theorem outputMemory_word_val (m : Memory w) (d : ℕ) (xs : List (List Bool)) (i : ℕ)
    (hi : i < xs.length) (hfit : xs[i].length ≤ w) :
    (outputMemory m d xs (d+i)).val = value xs[i] := by
  rw [outputMemory_word m d xs i hi]
  exact word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide) hfit))

/-- The exact number of ticks through the width guard, setup, and both packing loops. -/
def ticks (count width : ℕ) := widthTicks width + 1 + (count*(8*width+8)+1)

/-- The decoder has linear cost in the number of input bits and output words. -/
theorem ticks_le (count width : ℕ) : ticks count width ≤ 8*count*(width+1)+8 := by
  unfold ticks widthTicks
  split <;> nlinarith

/-- On a disjoint bounded layout and a canonical bit stream the physical instruction
table decodes every broadcast word. Registers outside the documented ABI scratch
are preserved and the event record has no private guesses or sign changes. -/
theorem pack_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (xs : List (List Bool)) {p d width : ℕ} (hp : (s 50).val = p) (hd : (s 53).val = d)
    (hc : (s 51).val = xs.length) (hw : (s 52).val = width) (hone : (s 63).val = 1)
    (hwidth : width ≤ w) (hwords : ∀ b ∈ xs, b.length = width)
    (hfit : p+xs.length*width < 2^w) (hdfit : d+xs.length < 2^w)
    (hsep : p+xs.length*width ≤ d ∨ d+xs.length ≤ p) (hb : WordsAt m p xs) :
    ∃ es t, Runs pub mac pack s m es t (outputMemory m d xs) ∧
      TraceOK es [] (ticks xs.length width) ∧ Preserves scratch s t ∧
      (t 50).val = p+xs.length*width ∧ (t 53).val = d+xs.length := by
  obtain ⟨es,t,guard,ht,hp₁⟩ := widthGuard_runs pub mac s m hone (hw ▸ hwidth)
  let u := Function.update t (54 : Reg) (0 : Word w)
  have init : Runs pub mac (.constant 54 0) t m [tick w] u m := Runs.localStep _ rfl rfl
  have hu (j : Reg) (h : j ∉ [54,60,61]) : u j = s j := by
    simp at h
    simp [u,h,hp₁ j (by simp [h])]
  obtain ⟨fs,z,run,hfs,hp₂,hz,hz'⟩ := wordsLoop_runs pub mac u m xs
    ((congrArg Fin.val (hu 50 (by decide))).trans hp) ((congrArg Fin.val (hu 53 (by decide))).trans hd)
    (i := 0) (by simp [u]) ((congrArg Fin.val (hu 51 (by decide))).trans hc)
    ((congrArg Fin.val (hu 52 (by decide))).trans hw) ((congrArg Fin.val (hu 63 (by decide))).trans hone)
    (Nat.zero_add _) hwords hfit hdfit hsep hb
  refine ⟨_,z,.seq guard (.seq init run),?_,?_,hz,hz'⟩
  · have h₁ : TraceOK [tick w] [] 1 := by simp [TraceOK,tick]
    simpa [ticks,hw,Nat.add_assoc] using ht.append (h₁.append hfs)
  · intro j hj
    apply (hp₂ j hj).trans
    apply hu
    simp [scratch] at hj
    simp [hj]

/-- Native acceptance at any choice tape is unique for a returning pack execution. -/
theorem pack_execute_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt}
    (h : Runs pub mac pack s m es t mt) (bits : List (List Bool)) (fs : List (TeamRAM.Event w)) :
    TeamRAM.execute (pack.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
      fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  rw [Code.execute_iff_runs (c := pack) (by decide)]
  constructor
  · rintro ⟨⟨z,mz,run⟩,rfl⟩
    obtain ⟨rfl,_,_⟩ := h.unique_of_deterministic (by decide) run
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨t,mt,h⟩,rfl⟩

end DiagonalTallyBits

end BorderVNP
end Computability
end OAI
