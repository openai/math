import OAI.Computability.NearSquareRoot.KernelEffectiveFamily

/-! # Effective command families with an input-dependent clock

The type of inputs may vary with the generated command, for example with
the arity of a binary table. Its numeric command file is computed from the
outer parameter alone. Runtime promises may refer to mathematical input
data that are absent from the tape encoding.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveTask
open IntegerMultiplication Code CommonRegisters GeneratorSyntax

def Runs {X : Type*} (c : Cmd) (a : X → ℕ) (src dst : X → Tree) : Prop :=
  ∃ C : ℕ, ∀ x env, Fits.value env c 0 (src x) (dst x) (C*(a x+1))

def Family {P : Type} [Primcodable P] (R : ℕ) {X : P → Type}
    (a : ∀ p, X p → ℕ) (src dst : ∀ p, X p → Tree) : Prop :=
  ∃ c : P → Cmd, Effective ltr c ∧
    ∀ p, Within R (c p) ∧ Runs (c p) (a p) (src p) (dst p)

namespace Runs
variable {X Y : Type*} {c d : Cmd} {a b : X → ℕ} {u v w : X → Tree}

theorem on (h : Runs c a u v) (f : Y → X) : Runs c (a ∘ f) (u ∘ f) (v ∘ f) := by
  obtain ⟨C,h⟩ := h
  exact ⟨C,fun x => h (f x)⟩

theorem conform (h : Runs c a u v) {b : X → ℕ} {p q : X → Tree}
    (cost : ∀ x, a x=b x) (src : ∀ x, u x=p x) (dst : ∀ x, v x=q x) : Runs c b p q := by
  rwa [←funext cost,←funext src,←funext dst]

theorem bound (h : Runs c a u v) (K : ℕ) (hk : ∀ x, a x+1 ≤ K*(b x+1)) : Runs c b u v := by
  obtain ⟨C,h⟩ := h
  exact ⟨C*K,fun x env r => (h x env r).mono (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left C (hk x))⟩

theorem comp (h : Runs c a u v) (g : Runs d b v w) : Runs (c.join d) (fun x => a x+b x) u w := by
  obtain ⟨C,h⟩ := h
  obtain ⟨D,g⟩ := g
  refine ⟨C+D+2,fun x env r => ((h x env r).join (g x env r)).mono ?_⟩
  dsimp only
  have hc := Nat.mul_le_mul_left C (show a x+1≤a x+b x+1 by omega)
  have hd := Nat.mul_le_mul_left D (show b x+1≤a x+b x+1 by omega)
  rw [Nat.add_mul,Nat.add_mul]
  omega

end Runs

theorem fixed {P X : Type} [Primcodable P] {R : ℕ} {a : X → ℕ} {f g : X → Tree}
    (h : RegisterWitness.Timed R a f g) : Family (P:=P) R (fun _ => a) (fun _ => f) (fun _ => g) := by
  obtain ⟨c,w,k⟩ := h
  exact ⟨fun _ => c,effective_const _ _,fun _ => ⟨w,k⟩⟩

namespace Family
variable {P D : Type} [Primcodable P] [Primcodable D] {R : ℕ} {X : P → Type}
variable {a b : ∀ p, X p → ℕ} {u v w : ∀ p, X p → Tree}

theorem reindex (h : Family R a u v) (g : D → P) (hg : Computable g) :
    Family R (fun d => a (g d)) (fun d => u (g d)) (fun d => v (g d)) := by
  obtain ⟨c,he,hr⟩ := h
  exact ⟨fun d => c (g d),he.comp hg,fun d => hr (g d)⟩

theorem comp (h : Family R a u v) (j : Family R b v w) :
    Family R (fun p x => a p x+b p x) u w := by
  obtain ⟨c,ec,hc⟩ := h
  obtain ⟨d,ed,hd⟩ := j
  exact ⟨fun p => (c p).join (d p),ec.join ed,
    fun p => ⟨⟨(hc p).1,(hd p).1⟩,(hc p).2.comp (hd p).2⟩⟩

theorem bound (h : Family R a u v) (K : P → ℕ) (hk : ∀ p x, a p x+1≤K p*(b p x+1)) :
    Family R b u v := by
  obtain ⟨c,he,hc⟩ := h
  exact ⟨c,he,fun p => ⟨(hc p).1,(hc p).2.bound (K p) (hk p)⟩⟩

theorem ofLinear {U V : Type} [Codec U] [Codec V] {f : P → U → V}
    (h : KernelEffectiveFamily.Family R f) :
    Family R (fun _ => size) (fun _ => send) (fun p x => send (f p x)) := h

end Family

end EffectiveTask

end NearSquareRoot
end Computability
end OAI
