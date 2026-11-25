import OAI.ThreeFlat.RAM.EffectStream
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Reading an individual output of an ordered native effect list -/

namespace ThreeFlat.RAM.EffectStream

open Computability.VPVNP.BurstRAM

variable {w : ℕ}

theorem after_at (updates : List (Record w)) (m : Memory w) (a : ℕ) (v : Word w)
    (writes : ∀ x ∈ updates, x.1.val = a → x.2 = v)
    (set : m a = v ∨ ∃ x ∈ updates, x.1.val = a) : after m (events updates) a = v := by
  induction updates generalizing m with
  | nil => simpa [events, after] using set
  | cons x xs ih =>
    change after (writeMemory m x.1 x.2) (events xs) a = v
    apply ih (writeMemory m x.1 x.2) (fun y hy => writes y (List.mem_cons_of_mem x hy))
    by_cases hit : x.1.val = a
    · exact Or.inl (by simp [writeMemory,hit, writes x (by simp) hit])
    · have keep : writeMemory m x.1 x.2 a = m a := by simp [writeMemory,Ne.symm hit]
      rcases set with old|⟨y,hy,atAddr⟩
      · exact Or.inl (keep.trans old)
      · exact Or.inr ⟨y, (List.mem_cons.mp hy).resolve_left (fun eq => hit (eq ▸ atAddr)), atAddr⟩

/-- In a table with distinct destinations, each generated word can be recovered
at its own physical address, independent of the initial memory. -/
theorem after_ofFn {n : ℕ} (dst val : Fin n → Word w) (m : Memory w)
    (inj : Function.Injective dst) (i : Fin n) :
    after m (events (List.ofFn fun j => (dst j,val j))) (dst i).val = val i := by
  apply after_at
  · intro x hx atAddr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    have eq : j=i := inj (Fin.ext atAddr)
    rw [eq]
  · exact Or.inr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩

theorem after_ofFn_outside {n : ℕ} (dst val : Fin n → Word w) (m : Memory w)
    (a : ℕ) (away : ∀ i, (dst i).val ≠ a) :
    after m (events (List.ofFn fun j => (dst j,val j))) a = m a := by
  apply after_at _ _ _ _ _ (Or.inl rfl)
  intro x hx atAddr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact (away i atAddr).elim

end ThreeFlat.RAM.EffectStream

end OAI
