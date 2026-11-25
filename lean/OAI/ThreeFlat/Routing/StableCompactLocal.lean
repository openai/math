import OAI.ThreeFlat.Routing.StableCompactRows
import Mathlib.Data.Fin.Init

namespace OAI
/-! # Replicating a local verifier over all sites

A local pin can refer to a shared register at an xor displacement. Each site has
independent copies of the local verifier's private bits.
-/

open scoped BigOperators
namespace ThreeFlat.Routing.StableCompactRows

variable {F : Type*} {m h p n : ℕ}

/-- Preserve a public operand when appending private registers. -/
def Source.castAdd (s : Source m h) (n : ℕ) : Source m (h+n) :=
  match s with
  | .constant b => .constant b
  | .siteBit j => .siteBit j
  | .pin k => .pin k
  | .hidden reg mask => .hidden (reg.castAdd n) mask

private def localAddress (wire : Fin p → Source m h) : BitSource n p → Source m (h+n)
  | .constant b => .constant b
  | .hidden reg => .hidden (Fin.natAdd h reg) 0
  | .pin j => (wire j).castAdd n

/-- Copy an entire local network, with its private registers allocated after the shared prefix. -/
def ofLocal (S : BitNetwork F p) (wire : Fin p → Source m h) : Template F m (h+S.internal) where
  cells := S.cells
  source i j := localAddress wire (S.source i j)
  table := S.table

@[simp] theorem ofLocal_cells (S : BitNetwork F p) (wire : Fin p → Source m h) :
    (ofLocal S wire).cells = S.cells := rfl

private theorem localAddress_read (wire : Fin p → Source m h) (a : BitSource n p)
    (M X Y : Fin (2^m) → Bool) (H : Fin h → Fin (2^m) → Bool)
    (privateBits : Fin (2^m) → Fin n → Bool) (v : Fin (2^m)) :
    (localAddress wire a).read M X Y (Fin.append H (fun r u => privateBits u r)) v =
      a.read (privateBits v) (fun j => (wire j).read M X Y H v) := by
  cases a with
  | constant b => rfl
  | hidden r => simp [localAddress,Source.read,BitSource.read]
  | pin j =>
    cases eq : wire j <;> simp [localAddress,Source.castAdd,Source.read,BitSource.read,eq]

/-- For each shared register assignment, each site evaluates the original local network on
the data selected by its ports. The product is summed over shared assignments. -/
theorem ofLocal_eval [CommSemiring F] (S : BitNetwork F p) (wire : Fin p → Source m h)
    (M X Y : Fin (2^m) → Bool) :
    (ofLocal S wire).network.eval (pins M X Y) =
      ∑ H : Fin h → Fin (2^m) → Bool, ∏ v : Fin (2^m),
        S.eval (fun j => (wire j).read M X Y H v) := by
  classical
  rw [Template.network_eval]
  let value (allBits : Fin (h+S.internal) → Fin (2^m) → Bool) : F :=
    ∏ v : Fin (2^m), ∏ i : Fin S.cells,
      S.table i fun j => (localAddress wire (S.source i j)).read M X Y allBits v
  change (∑ allBits, value allBits) = _
  rw [← (Fin.appendEquiv (α := Fin (2^m) → Bool) h S.internal).sum_comp value,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro H _
  change (∑ ws : Fin S.internal → Fin (2^m) → Bool, value (Fin.append H ws)) =
    ∏ v : Fin (2^m), ∑ localBits : Fin S.internal → Bool,
      S.weight (fun j => (wire j).read M X Y H v) localBits
  let transpose : (Fin (2^m) → Fin S.internal → Bool) ≃ (Fin S.internal → Fin (2^m) → Bool) :=
    Equiv.piComm (fun _ _ => Bool)
  rw [← transpose.sum_comp (fun ws => value (Fin.append H ws)),Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ws _
  change (∏ v : Fin (2^m), ∏ i : Fin S.cells,
    S.table i (fun j => (localAddress wire (S.source i j)).read M X Y
      (Fin.append H (fun r u => ws u r)) v)) = _
  simp only [localAddress_read,BitNetwork.weight,BitNetwork.factor]

end ThreeFlat.Routing.StableCompactRows

end OAI
