import OAI.Computability.NearSquareRoot.ScheduleRegisterConstructors
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax
import OAI.Computability.IntegerMultiplication.Interface

/-! # Computable families of register-bounded linear tree commands

The command file depends effectively on its parameter. The running-time
constant may depend on that same parameter, and the occupied register
indices have a common bound across the entire family.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveFamily

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

variable {P Q X Y Z : Type} [Primcodable P] [Primcodable Q] [Codec X] [Codec Y] [Codec Z] {R : ℕ}

/-- Time bound for a specified command, including arbitrary parked data. -/
def Runs (c : Cmd) (f : X → Y) : Prop :=
  ∃ C : ℕ, ∀ x env, Fits.value env c 0 (send x) (send (f x)) (C*(size x+1))

/-- One uniformly generated linear command per parameter. -/
def Family (R : ℕ) (f : P → X → Y) : Prop :=
  ∃ c : P → Cmd, Effective ltr c ∧ ∀ p, Within R (c p) ∧ Runs (c p) (f p)

theorem Runs.comp {c d : Cmd} {f : X → Y} {g : Y → Z} (hs : Runs c f) (ht : Runs d g) :
    Runs (c.join d) (fun x => g (f x)) := by
  have fe : Code.Easy f := ⟨c,hs⟩
  obtain ⟨k,hk⟩ := fe.length
  obtain ⟨u,hu⟩ := hs
  obtain ⟨v,hv⟩ := ht
  refine ⟨u+v*(k+1)+2,fun x env r => ((hu x env r).join (hv (f x) env r)).mono ?_⟩
  have he : size (f x)+1 ≤ (k+1)*(size x+1) := by
    have h := hk x
    simp only [Nat.succ_mul, Nat.mul_succ] at *
    omega
  have hv' := Nat.mul_le_mul_left v he
  simpa only [Nat.add_mul, Nat.mul_assoc] using
    (show u*(size x+1) + v*(size (f x)+1)+2 ≤
      (u+v*(k+1)+2)*(size x+1) by
        rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
        omega)

namespace Family

theorem fixed {f : X → Y} (h : RegisterWitness.Easy R f) :
    Family R (fun _ : P => f) := by
  obtain ⟨c,hR,hc⟩ := h
  exact ⟨fun _ => c,effective_const ltr c,fun _ => ⟨hR,hc⟩⟩

theorem identity : Family R (fun _ : P => id (α := X)) := fixed RegisterWitness.Easy.identity

theorem const (hR : 1 ≤ R) (y : Y) : Family R (fun _ : P => fun _ : X => y) :=
  fixed (RegisterWitness.Easy.const hR y)

theorem reindex {f : P → X → Y} (h : Family R f) (g : Q → P) (hg : Computable g) :
    Family R (fun q => f (g q)) := by
  obtain ⟨c,he,hc⟩ := h
  exact ⟨fun q => c (g q),he.comp hg,fun q => hc (g q)⟩

theorem congr {f g : P → X → Y} (hf : Family R f) (e : ∀ p x, f p x = g p x) : Family R g :=
  (funext fun p => funext (e p)) ▸ hf

theorem ite {f g : P → X → Y} (test : P → Bool) (ht : Computable test)
    (hf : Family R f) (hg : Family R g) : Family R (fun p => if test p then f p else g p) := by
  obtain ⟨c,ce,cs⟩ := hf
  obtain ⟨d,de,ds⟩ := hg
  refine ⟨fun p => if test p then c p else d p, ?_, ?_⟩
  · change Computable fun p => file ltr (if test p then c p else d p)
    apply (Computable.cond ht ce de).of_eq
    intro p
    cases test p <;> rfl
  · intro p
    cases e : test p <;> simp [e,cs p,ds p]

theorem comp {f : P → X → Y} {g : P → Y → Z} (hf : Family R f) (hg : Family R g) :
    Family R (fun p x => g p (f p x)) := by
  obtain ⟨c,ce,cs⟩ := hf
  obtain ⟨d,de,ds⟩ := hg
  refine ⟨fun p => .join (c p) (d p),ce.join de,fun p => ⟨⟨(cs p).1,(ds p).1⟩,?_⟩⟩
  exact Runs.comp (cs p).2 (ds p).2

end Family
end KernelEffectiveFamily

end NearSquareRoot
end Computability
end OAI
