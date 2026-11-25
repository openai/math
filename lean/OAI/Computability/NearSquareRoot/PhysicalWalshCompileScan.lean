import OAI.Computability.NearSquareRoot.PhysicalWalshCompile
import OAI.Computability.NearSquareRoot.KernelEffectiveFamily

/-! # Named linear scans on bounded intermediate packets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space PhysicalWalsh

variable {I : Type} {V : I → ℕ} {p q r : I → Tree} {c d : Cmd}

/-- A family of serialized values fits in a constant multiple of the budget. -/
def Small (V : I → ℕ) (p : I → Tree) : Prop := ∃ C : ℕ, ∀ i, (p i).count ≤ C*(V i+1)

theorem Small.fork (hp : Small V p) (hq : Small V q) : Small V (fun i => .fork (p i) (q i)) := by
  obtain ⟨C,hc⟩ := hp
  obtain ⟨D,hd⟩ := hq
  refine ⟨C+D+1,fun i => ?_⟩
  have := hc i; have := hd i
  simp only [Tree.count,Nat.add_mul,Nat.one_mul]; omega

theorem Small.left {a b : I → Tree} (h : Small V (fun i => .fork (a i) (b i))) : Small V a := by
  obtain ⟨C,h⟩ := h
  exact ⟨C,fun i => (Nat.le_add_right _ _).trans ((Nat.le_succ _).trans (h i))⟩

theorem Small.right {a b : I → Tree} (h : Small V (fun i => .fork (a i) (b i))) : Small V b := by
  obtain ⟨C,h⟩ := h
  exact ⟨C,fun i => (Nat.le_add_left _ _).trans ((Nat.le_succ _).trans (h i))⟩

/-- A named stack command on a family of bounded-size requests. -/
structure Scan (cmd : Cmd) (V : I → ℕ) (q r : I → Tree) : Prop where
  input : Small V q
  time : ∃ C : ℕ, ∀ i env, Fits.value env cmd 0 (q i) (r i) (C*(V i+1))

namespace Scan

theorem output (h : Scan c V p q) : Small V q := by
  obtain ⟨C,hc⟩ := h.input
  obtain ⟨D,hd⟩ := (show Task V p q from ⟨c,h.time⟩).sizeBound
  exact ⟨C+D,fun i => by rw [Nat.add_mul]; exact (hd i).trans (Nat.add_le_add_right (hc i) _)⟩

theorem seq (h : Scan c V p q) (g : Scan d V q r) : Scan (c.join d) V p r := by
  obtain ⟨C,hc⟩ := h.time
  obtain ⟨D,hd⟩ := g.time
  refine ⟨h.input,C+D+2,fun i env s => ((hc i env s).join (hd i env s)).mono ?_⟩
  simp only [Nat.add_mul]; omega

theorem park (h : Scan c V p q) (z : I → Tree) (hz : Small V z) :
    Scan (left c) V (fun i => .fork (p i) (z i)) (fun i => .fork (q i) (z i)) := by
  obtain ⟨C,hc⟩ := h.time
  refine ⟨h.input.fork hz,C+7,fun i env s => ?_⟩
  apply (fits_pair ((hc i env (pile 0 (z i) s)).join (fits_pack (q i) (z i) s 0 env))).mono
  rw [Nat.add_mul]; omega

theorem linear {A B : Type} [Codec A] [Codec B] {f : A → B} (h : KernelEffectiveFamily.Runs c f)
    (a : I → A) (small : Small V (send ∘ a)) : Scan c V (send ∘ a) (fun i => send (f (a i))) := by
  obtain ⟨D,hd⟩ := h
  obtain ⟨C,hc⟩ := small
  refine ⟨⟨C,hc⟩,D*(C+1),fun i env s => (hd (a i) env s).mono ?_⟩
  have cap := hc i
  change size (a i) ≤ C*(V i+1) at cap
  rw [Nat.mul_assoc,Nat.succ_mul]
  exact Nat.mul_le_mul_left D (by omega)

theorem closed (h : Scan c V p q) : ClosedRuns c V V p q := by
  obtain ⟨C,hc⟩ := h.input
  obtain ⟨D,hd⟩ := h.time
  refine ⟨C+D,fun i env park b hpark => ?_⟩
  have cap := (hpark.pile 0 (p i)).mono (Nat.add_le_add_left (hc i) b)
  have clock : D*(V i+1) ≤ (C+D)*(V i+1) := by rw [Nat.add_mul]; omega
  apply (BoundedFits.of_fits (hd i env park) (cap := b+(C+D)*(V i+1)) (depth := (C+D)*(V i+1)) ?_ clock).mono clock le_rfl le_rfl
  intro j
  have hj := cap j
  rw [Nat.add_mul]; omega

end Scan
end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
