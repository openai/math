import OAI.Computability.BorderVNP.PackedGridBoxBudget
import OAI.Computability.BorderVNP.DiagonalInitialGrid

/-! # Private zero factors for unused directed cable lanes

Padding is stored in the one-copy private site box. Each unused incident lane gets one
Boolean factor, at both endpoints of the public cable. This realizes the actual
`ChannelPacking.ZeroPad` constraint without exposing any private used-width field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPadding

open Crossing CellSparse
open scoped Classical
variable {D H : ℕ} {P Q : Type} {bits : P → ℕ} [Fintype Q] {N : Network D P bits}
variable {src dst : Q → N.Site} (packing : N.ChannelPacking src dst H) (v : N.Site)

/-- All local public cable bits, prior to dropping the privately used addresses. -/
abbrev LocalLane := {q : Q // src q = v ∨ dst q = v} × Fin H

/-- A padding test is needed precisely for a lane that carries no fine wire bit. -/
def unused (l : LocalLane (H := H) (src := src) (dst := dst) v) : Prop :=
  (l.1.val,l.2) ∉ Set.range packing.address

/-- Store a unary truth-table guard for the bit zero. -/
def zeroFactor (addr : ℕ) : Factor := .truth [addr] [true,false]

/-- The unary truth-table guard accepts exactly a false bit at its actual address. -/
theorem observe_zero (addr : ℕ) (bank : ℕ → Bool) (off copy : ℕ) :
    (zeroFactor addr).observe bank off copy = if bank (off+addr) then none else some (false,none) := by
  cases h : bank (off+addr) <;> simp [zeroFactor,Factor.observe,word,h]

/-- The privately stored padding portion of a single site's box. Only the bit
addresses, not the original fine wire directory, need to be read by the checker. -/
noncomputable def factors (addr : LocalLane (H := H) (src := src) (dst := dst) v → ℕ) : List Factor :=
  ((Finset.univ.filter (unused packing v)).toList).map (fun l => zeroFactor (addr l))

/-- The concrete list of initial padding factors succeeds exactly when all unused bits
on all incident public cable words are zero. -/
theorem factors_pass (addr : LocalLane (H := H) (src := src) (dst := dst) v → ℕ)
    (a : {q : Q // src q = v ∨ dst q = v} → Fin H → Bool)
    (bank : ℕ → Bool) (off copy : ℕ)
    (reads : ∀ l, bank (off+addr l) = a l.1 l.2) :
    ((factors packing v addr).all (fun f => (f.observe bank off copy).isSome)) = true ↔
      ∀ q, packing.ZeroPad q.val (a q) := by
  simp only [List.all_eq_true, factors,List.mem_map,forall_exists_index,and_imp,Finset.mem_toList,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h q i hi
    have hh := h _ (q,i) hi rfl
    rw [observe_zero,reads] at hh
    cases hz : a q i <;> simp_all
  · rintro h _ l hu rfl
    rw [observe_zero,reads,h l.1 l.2 hu]
    rfl

/-- A sparse padding list requires at most one factor per local bit; every copy reuses
this list. A loop's two endpoint occurrences may share the same zero condition. -/
theorem factors_length_le (addr : LocalLane (H := H) (src := src) (dst := dst) v → ℕ) :
    (factors packing v addr).length ≤ Fintype.card {q : Q // src q = v ∨ dst q = v} * H := by
  unfold factors
  rw [List.length_map,Finset.length_toList]
  exact Finset.card_filter_le .. |>.trans_eq (by simp [LocalLane])

/-- The packed grid's local tensor is exactly the result of checking the private
zero factors before reading the original table on its fine subwords. -/
theorem tables_eq {R : Type*} [CommSemiring R] (t : N.Tables R)
    (addr : LocalLane (H := H) (src := src) (dst := dst) v → ℕ)
    (a : {q : Q // src q = v ∨ dst q = v} → Fin H → Bool)
    (x : ∀ p : {p : P // N.attach p = v}, Fin (bits p.val) → Bool)
    (bank : ℕ → Bool) (off copy : ℕ) (reads : ∀ l, bank (off+addr l) = a l.1 l.2) :
    packing.tables t v a x =
      if (factors packing v addr).all (fun f => (f.observe bank off copy).isSome) then
        Diagonal.CellEntries.unpackFactor packing t v a x else 0 := by
  have h := factors_pass packing v addr a bank off copy reads
  by_cases hp : ∀ q, packing.ZeroPad q.val (a q) <;>
    simp [Network.ChannelPacking.tables,Diagonal.CellEntries.unpackFactor,h,hp]

end Packing.GridPadding

end BorderVNP
end Computability
end OAI
