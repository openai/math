import OAI.Computability.BorderVNP.TransmissionModel

/-!
# What each substituted consumer reads

A received bit is the value from the endpoint's actual initialized link. A local
data bit comes directly from its source address and a local shared bit is the single
chosen value at that offset. The readback proof covers coincident destinations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM
open scoped Classical

variable {w : ℕ}

/-- The addresses written by one role at the current within-range offset. -/
def Role.writes (mode : Role) (s : Bank w) (a : ℕ) : Prop :=
  match mode with
  | .sharedHere => a = (s 13+s 16).val ∨ a = (s 14+s 16).val
  | .dataHere | .receiveB => a = (s 14+s 16).val
  | .receiveA => a = (s 13+s 16).val
  | .sendData => False

/-- Value delivered to a consumer. In the origin-only role the source is checked against
its physical link and there is no consumer in this row. -/
def Role.payload (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w) (b : Bool) : Word w :=
  match mode with
  | .sharedHere => if b then s 1 else s 2
  | .dataHere | .sendData => m (s 12+s 16).val
  | .receiveA => m (endpointNat 10 pub s m)
  | .receiveB => m (endpointNat 9 pub s m)

/-- The complete addressed update, including every untouched memory word. -/
theorem Role.output_at (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    (b : Bool) (a : ℕ) :
    mode.output pub s m b a = if mode.writes s a then mode.payload pub s m b else m a := by
  cases mode <;> simp only [Role.output,Role.writes,Role.payload,write,Function.update_apply]
  all_goals split_ifs <;> simp_all

/-- The addressed consumer receives the value computed at the nominated bit offset. Later
offsets preserve it whenever they do not write that same address. -/
theorem rangeMemory_readback (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    (bits : ℕ → Bool) {a j k : ℕ} (hj : j < k)
    (hit : mode.writes (Function.update s 16 (Fin.ofNat _ j)) a)
    (later : ∀ i, j < i → i < k → ¬ mode.writes (Function.update s 16 (Fin.ofNat _ i)) a) :
    rangeMemory mode pub s m bits k a =
      mode.payload pub (Function.update s 16 (Fin.ofNat _ j)) (rangeMemory mode pub s m bits j) (bits j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [rangeMemory,Role.output_at]
    by_cases h : j=k
    · subst k; rw [ite_eq_left hit]
    · have hlt : j < k := by omega
      rw [ite_eq_right (later k hlt k.lt_succ_self)]
      exact ih hlt fun i hi hi' => later i hi (hi'.trans k.lt_succ_self)

/-- Readback from the canonical memory transform of a whole selected row. -/
theorem Range.readback (row : Range w) (self : Word w) (pub : Arg → Word w) (m : Memory w)
    (bits : ℕ → Bool) {mode : Role} (hs : row.selected self = some (some mode))
    {a j : ℕ} (hj : j < row.width.val)
    (hit : mode.writes (Function.update (row.bank self) 16 (Fin.ofNat _ j)) a)
    (later : ∀ i, j < i → i < row.width.val →
      ¬ mode.writes (Function.update (row.bank self) 16 (Fin.ofNat _ i)) a) :
    row.apply self pub m bits a =
      mode.payload pub (Function.update (row.bank self) 16 (Fin.ofNat _ j))
        (rangeMemory mode pub (row.bank self) m bits j) (bits j) := by
  rw [Range.apply,hs]
  exact rangeMemory_readback _ _ _ _ _ hj hit later

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
