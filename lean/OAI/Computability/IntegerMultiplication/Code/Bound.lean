import OAI.Computability.IntegerMultiplication.Code.Slice
import Mathlib

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Prog
variable {X Y Z : Type*}
/-- Constants-uniform real budget. Includes positivity property ≥1.
Auxiliary measure to avoid ceilings in algorithm algebra; interoperates
with Task natural budgets. -/
def Sized (a : X → ℝ) (p q : X → Tree) :=
  (∀ x, 1 ≤ a x) ∧ ∃ b : X → ℕ, Task b p q ∧ ∃ K : ℕ, ∀ x, (b x:ℝ)+1 ≤ (K:ℝ)*a x

namespace Sized
variable {a d : X → ℝ} {b c : X → ℕ} {p q r : X → Tree}
theorem natural (h : Task b p q) : Sized (fun x => (b x:ℝ)+1) p q :=
  ⟨fun x => by linarith [Nat.cast_nonneg (α:=ℝ) (b x)],
   b,h,1,by simp⟩

theorem adapts (h : Sized a p q) (hd : ∀ x, 1 ≤ d x)
    (J : ℕ) (e : ∀ x, a x ≤ (J:ℝ)*d x) : Sized d p q := by
  obtain ⟨_,b,h,K,u⟩ := h
  refine ⟨hd,b,h,K*J,fun x => le_trans (u x) ?_⟩
  simp only [Nat.cast_mul, mul_assoc]; gcongr; exact e x

theorem mono (h : Sized a p q) (e : ∀ x, a x ≤ d x) : Sized d p q :=
  h.adapts (fun x => (h.1 x).trans (e x)) 1 (by simpa)

theorem along (h : Sized a p q) (f : Y → X) :
    Sized (fun x => a (f x)) (fun x => p (f x)) (fun x => q (f x)) := by
  obtain ⟨i,b,h,D,v⟩ := h
  exact ⟨fun x => i _,_,h.on f,D,fun x => v _⟩

theorem conform (h : Sized a p q) {a' : X → ℝ} {p' q' : X → Tree} (ha : ∀ x, a x=a' x)
    (hp : ∀ x, p x=p' x) (hq : ∀ x, q x=q' x) : Sized a' p' q' := by
  rwa [funext ha,funext hp,funext hq] at h

theorem thenDo (h : Sized a p q) (e : Sized d q r) :
    Sized (fun x => a x+d x) p r := by
  obtain ⟨i,b,h,J,u⟩ := h
  obtain ⟨v,c,e,K,w⟩ := e
  refine ⟨fun x => le_add_of_le_of_nonneg (i x) (by specialize v x; linarith),
    _, h.compose e,J+K,fun x => ?_⟩
  dsimp only; push_cast
  specialize u x; specialize w x
  have H : 0≤(J:ℝ)*d x := by have := v x; exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have Z : 0≤(K:ℝ)*a x := by have := i x; exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

theorem chain (h : Sized a p q) (e : Sized a q r) : Sized a p r :=
  (h.thenDo e).adapts h.1 2 (fun x => by norm_num; linarith)

theorem size_shield (h : ∃ D : ℕ, ∀ x : X, ((p x).count:ℝ) ≤ (D:ℝ)*a x)
    (ha : ∀ x, 1≤a x) (e : Task (fun x => (p x).count) p q) :
    Sized a p q := by
  obtain ⟨D,d⟩ := h
  refine ⟨ha,_,e,D+1,fun x => ?_⟩
  push_cast; specialize d x; specialize ha x; linarith

theorem impact (h : Sized a p q) (e : ∃ D : ℕ, ∀ x : X, ((p x).count:ℝ) ≤ (D:ℝ)*a x) :
    ∃ D : ℕ, ∀ x : X, ((q x).count:ℝ) ≤ (D:ℝ)*a x := by
  obtain ⟨_,b,ht,D,u⟩ := h; obtain ⟨E,i⟩ := e; obtain ⟨C,f⟩ := ht.sizeBound
  refine ⟨E+C*D,fun x => ?_⟩
  calc
   _ ≤ ((p x).count:ℝ)+(C:ℝ)*((b x:ℝ)+1) := by exact_mod_cast f x
   _ ≤ (E:ℝ)*a x + (C:ℝ)*((D:ℝ)*a x) := by gcongr; exacts [i x,u x]
   _ = _ := by push_cast; ring

theorem release (h : Sized a p q) : Task (fun x => ⌈a x⌉₊) p q := by
  obtain ⟨_,b,ht,D,hd⟩ := h
  apply ht.bound D
  intro x
  suffices (b x:ℝ)+1 ≤ (D*(⌈a x⌉₊+1:ℕ) : ℕ) by exact_mod_cast this
  specialize hd x
  push_cast
  calc
   _ ≤ (D:ℝ)*a x := hd
   _ ≤ _ := by gcongr; linarith [Nat.le_ceil (a x)]

end Sized
end Code

end IntegerMultiplication
end Computability
end OAI
