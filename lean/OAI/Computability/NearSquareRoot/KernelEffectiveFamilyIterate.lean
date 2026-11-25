import OAI.Computability.NearSquareRoot.KernelEffectiveFamily

/-! # Compile-time iteration of a fixed linear command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveFamily

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

variable {X : Type} [Codec X] {R : ℕ}

def copies (c : Cmd) : ℕ → Cmd
  | 0 => .pass
  | n+1 => (copies c n).join c

theorem effective_copies (c : Cmd) : Effective ltr (copies c) := by
  have h := Computable.nat_rec (σ := File) Computable.id (Computable.const (file ltr (.pass : Cmd)))
    (primrec_joinFile.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.const (file ltr c))).to₂
  apply h.of_eq
  intro n
  change Nat.rec (file ltr (.pass : Cmd)) (fun _ acc => joinFile acc (file ltr c)) n = file ltr (copies c n)
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg (fun s => joinFile s (file ltr c)) ih).trans (joinFile_file ..)

theorem Family.iterate_fixed {f : X → X} (h : RegisterWitness.Easy R f) :
    Family R (fun n : ℕ => f^[n]) := by
  obtain ⟨c,hR,hc⟩ := h
  refine ⟨copies c,effective_copies c,fun n => ?_⟩
  induction n with
  | zero =>
    refine ⟨trivial,1,fun x env r => (Fits.pass _).mono ?_⟩
    simp
  | succ n ih =>
    exact ⟨⟨ih.1,hR⟩, by dsimp only; rw [show f^[n+1] = (fun x => f (f^[n] x)) from funext (Function.iterate_succ_apply' f n)]; exact
      (Runs.comp ih.2 (show Runs c f from hc))⟩

end KernelEffectiveFamily

end NearSquareRoot
end Computability
end OAI
