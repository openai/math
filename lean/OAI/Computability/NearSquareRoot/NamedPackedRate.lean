import OAI.Computability.IntegerMultiplication.Strip.Breeze
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask

/-! # Packed computation bounds for a specified physical command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace NamedPacked

open IntegerMultiplication Code Strip

variable {X Y : Type} {c d : Cmd} {a b : X → ℝ} {u v w : X → Tree}

/-- The real-valued P192 run and packet bounds with the executable kept fixed. -/
structure CarriesAt (c : Cmd) (a : X → ℝ) (p q : X → Tree) : Prop where
  budget : ∀ x, 1 ≤ a x
  work : ∃ t : X → ℕ, EffectiveTask.Runs c t p q ∧ ∃ C : ℕ, ∀ x, (t x:ℝ)+1 ≤ C*a x
  small : Volume a p

namespace CarriesAt

theorem forget (h : CarriesAt c a u v) : Carries a u v := by
  obtain ⟨t,r,C,b⟩ := h.work
  exact ⟨⟨h.budget,t,⟨c,r⟩,C,b⟩,h.small⟩

theorem exists_of_carries (h : Carries a u v) : ∃ c : Cmd, CarriesAt c a u v := by
  obtain ⟨pos,t,⟨c,run⟩,C,b⟩ := h.runs
  exact ⟨c,pos,⟨t,run,C,b⟩,h.small⟩

theorem on (h : CarriesAt c a u v) (f : Y → X) : CarriesAt c (a ∘ f) (u ∘ f) (v ∘ f) := by
  obtain ⟨t,r,C,b⟩ := h.work
  exact ⟨fun y => h.budget _,⟨t ∘ f,r.on f,C,fun y => b _⟩,h.small.along f⟩

theorem larger (h : CarriesAt c a u v) (e : ∀ x,a x ≤ b x) : CarriesAt c b u v := by
  obtain ⟨t,r,C,gt⟩ := h.work
  exact ⟨fun x => (h.budget x).trans (e x),⟨t,r,C,fun x => (gt x).trans (by gcongr; exact e x)⟩,
    (h.forget.larger e).small⟩

theorem next (h : CarriesAt c a u v) (g : CarriesAt d a v w) : CarriesAt (c.join d) a u w := by
  obtain ⟨t,r,C,b⟩ := h.work
  obtain ⟨s,f,D,e⟩ := g.work
  exact ⟨h.budget,⟨fun x => t x+s x,r.comp f,C+D,fun x => by push_cast; linarith [b x,e x]⟩,h.small⟩

/-- A natural tape clock which dominates the real allowance works for this very command. -/
theorem bounds (h : CarriesAt c a u v) (t : X → ℕ) (le : ∀x,a x ≤ t x) :
    EffectiveTask.Runs c t u v := by
  obtain ⟨s,r,C,b⟩ := h.work
  apply r.bound (C+1)
  intro x
  have hj : (s x:ℝ)+1 ≤ (C:ℝ)*t x := (b x).trans (mul_le_mul_of_nonneg_left (le x) (Nat.cast_nonneg _))
  have h' : s x+1 ≤ C*t x := by exact_mod_cast hj
  rw [Nat.succ_mul,Nat.mul_succ]; omega

theorem release (h : CarriesAt c a u v) : EffectiveTask.Runs c (fun x => ⌈a x⌉₊) u v :=
  h.bounds _ (fun _ => Nat.le_ceil _)

end CarriesAt

/-- The exponent for polynomial descriptor work may depend on the command,
while its syntax is already fixed. -/
def BreezeAt (c : Cmd) (f : X → ℝ) (r : Regime X) (n l : X → ℕ) (p q : X → Tree) : Prop :=
  (∀ x,1 ≤ f x) ∧ ∃ d,CarriesAt c (runrate f r n l d) p q

namespace BreezeAt

variable {f g : X → ℝ} {r : Regime X} {n l : X → ℕ}

theorem forget (h : BreezeAt c f r n l u v) : Breeze f r n l u v := by
  obtain ⟨pos,D,H⟩ := h; exact ⟨pos,D,H.forget⟩

theorem exists_of_breeze (h : Breeze f r n l u v) : ∃ c : Cmd, BreezeAt c f r n l u v := by
  obtain ⟨pos,D,H⟩ := h
  obtain ⟨c,go⟩ := CarriesAt.exists_of_carries H
  exact ⟨c,pos,D,go⟩

theorem launch (h : Rip r n l u v) (pos : ∀ x,1 ≤ f x) : ∃ c : Cmd, BreezeAt c f r n l u v :=
  exists_of_breeze (Breeze.launch h pos)

theorem on (h : BreezeAt c f r n l u v) (j : Y → X) :
    BreezeAt c (f ∘ j) (r.pull j) (n ∘ j) (l ∘ j) (u ∘ j) (v ∘ j) := by
  obtain ⟨pos,d,h⟩ := h
  exact ⟨fun y => pos (j y),d,h.on j⟩

theorem raise (h : BreezeAt c f r n l u v) (le : ∀ x, f x ≤ g x) : BreezeAt c g r n l u v := by
  obtain ⟨pos,D,h⟩ := h
  exact ⟨fun x => (pos x).trans (le x),D,h.larger fun x =>
    mul_le_mul_of_nonneg_left (le x) (by unfold mass; positivity)⟩

theorem next (h : BreezeAt c f r n l u v) (q : BreezeAt d f r n l v w) :
    BreezeAt (c.join d) f r n l u w := by
  obtain ⟨pos,A,go⟩ := h
  obtain ⟨_,B,run⟩ := q
  exact ⟨pos,A+B,(go.larger fun x => rate_higher x (pos x) (Nat.le_add_right ..)).next
    (run.larger fun x => rate_higher x (pos x) (Nat.le_add_left ..))⟩

end BreezeAt
end NamedPacked

end NearSquareRoot
end Computability
end OAI
