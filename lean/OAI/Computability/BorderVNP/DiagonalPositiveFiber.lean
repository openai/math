import OAI.Computability.BorderVNP.DiagonalNativeChosenEntry
import OAI.Computability.BorderVNP.RoutingWireSnapshots

/-! # Summing the true positive-mode exterior fibers and the independent pin guess -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open TeamContraction Routing
open scoped BigOperators Classical

variable {I A : Type*} [Fintype I] [AddCommMonoid A] {d : ℕ}

/-- The actual assigned-path type can depend on all raw guessed pin bits.
Rejected binary pins have zero residue contribution, while every encoded
index keeps precisely its own assigned paths. -/
theorem PinCodec.sum_decode_paths (codec : PinCodec I d) (Path : (Fin d → Bool) → Type*)
    [∀ b, Fintype (Path b)] (value : ∀ b, Path b → I → A) :
    (∑ b, ∑ a : Path b, (codec.decode b).elim 0 (value b a)) =
      ∑ i, ∑ a : Path (codec.encode i), value (codec.encode i) a i := by
  let f := fun i => ∑ a : Path (codec.encode i), value (codec.encode i) a i
  refine Eq.trans ?_ (codec.sum_decode f)
  apply Finset.sum_congr rfl
  intro b _
  cases h : codec.decode b with
  | none => simp
  | some i =>
    have eq := (codec.decode_eq_some b i).mp h
    subst b
    rfl

namespace PositiveFiber

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (live : Fin d → Bool) (codec : PinCodec I d)
    (Path : (Fin d → Bool) → Type*) [∀ b, Fintype (Path b)]
    (layout : ∀ b, Path b → WireLayout (R+1) r link)
    (banks : ∀ b a ext, WireSnapshots G live ext (layout b a) w)
    (fixed : ∀ b, Path b → Block (R+1))
    (header : ∀ b a, Fin (layout b a).header → Bool)
    (high payload : ∀ b, Path b → Fin (R+1) → Fin (R+1) → ℕ → Bool)

/-- The actual passing predicate for a completely assigned term, in the
prefix, source, relay and padding snapshots of each processor. -/
abbrev Passes (ext : Exterior R r link → Bool) (b : Fin d → Bool) (a : Path b) :=
  (banks b a ext).Passes (fixed b a) (header b a) (high b a) (payload b a)

/-- Even though every assignment chooses its own wire layout, program
snapshots and reader source memory, it contributes once, at its checked
shared exterior. Reduction modulo the prime may reject padded pin codes
after the native count is taken. -/
theorem sum {A : Type*} [AddCommMonoid A] (hw : 0 < w)
    (v : (Exterior R r link → Bool) → ∀ b, Path b → A) (amount : ∀ b, Path b → I → A)
    (read : ∀ ext b a, Passes G live Path layout banks fixed header high payload ext b a →
      v ext b a = (codec.decode b).elim 0 (amount b a)) :
    (∑ ext : Exterior R r link → Bool, ∑ b : Fin d → Bool, ∑ a : Path b,
      if Passes G live Path layout banks fixed header high payload ext b a then v ext b a else 0) =
    ∑ i, ∑ a : Path (codec.encode i), amount (codec.encode i) a i := by
  rw [Finset.sum_comm]
  refine Eq.trans ?_ (codec.sum_decode_paths Path amount)
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  refine Eq.trans ?_ (sum_physical_snapshots hw (banks b a) (fixed b a) (header b a) (high b a)
    (payload b a) ((codec.decode b).elim 0 (amount b a)))
  apply Finset.sum_congr rfl
  intro ext _
  split <;> first | rfl | exact read ext b a ‹_›

end PositiveFiber
end Diagonal

end BorderVNP
end Computability
end OAI
