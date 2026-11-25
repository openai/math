import OAI.Computability.BorderVNP.PackedSuppliedOffsets
import OAI.Computability.BorderVNP.PackedCableTriples
import OAI.Computability.BorderVNP.GeometryOutputPrefix

/-! # The packed geometry result array consumed by routing

The cable triples come first. The suffix contains the source/destination supplied
offsets, each cell's supplied length, zeroed per-cell private counters, original
site placement pairs, and live grouped-port placement pairs. Any additional
geometry output and the validity flag follow these fixed regions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddressCircuit CellAddressViews ParseBatchSort VPVNP.VerifierNetwork GeometryFrameEncoding
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private pad pad_value pad_size from OAI.Computability.BorderVNP.PackedCableTriples
open scoped Classical

variable {s m n C d k w J A o : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Five successive routing subarrays. The last two carry pairs per original or live site. -/
abbrev Column (m C J A : ℕ) := ((((Fin m × Fin 2) ⊕ Fin C) ⊕ Fin C) ⊕ (Fin J × Fin 2)) ⊕ (Fin A × Fin 2)

/-- Word length after the cable triples and before further geometry results. -/
def count (m C J A : ℕ) := m*2+C+C+J*2+A*2

/-- Public order agrees with the native pointer arithmetic. -/
def order : Column m C J A ≃ Fin (count m C J A) :=
  (((((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).sumCongr (Equiv.refl _)).trans
    finSumFinEquiv).sumCongr finProdFinEquiv |>.trans finSumFinEquiv).sumCongr finProdFinEquiv |>.trans finSumFinEquiv

private abbrev Work (σ : Type*) (m n C k w : ℕ) :=
  σ ⊕ ((End m n × Fin k) ⊕ (SuppliedOffsets.Result m n C × Fin w))

private noncomputable def prepared : Frame σ (Work σ m n C k w) :=
  (parallelFrame (labels F) (SuppliedOffsets.frame F)).withInput

/-- Choose source on column zero and destination on column one. -/
def endpoint (i : Fin m) (c : Fin 2) : End m n := .inl (if c=0 then .inl i else .inr i)

private def bits (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin A → Fin n) :
    Column m C J A → Fin w → Expr (Work σ m n C k w)
  | .inl (.inl (.inl (.inl (i,c)))),j => .input (.inr (.inr (.inl (endpoint i c),j)))
  | .inl (.inl (.inl (.inr c))),j => .input (.inr (.inr (.inr c,j)))
  | .inl (.inl (.inr _)),_ => .const false
  | .inl (.inr (i,c)),j =>
    if c=0 then pad hk (fun u => .input (.inl (F.owner (old i) u))) j else .const false
  | .inr (i,c),j =>
    if c=0 then pad hk (fun u => .input (.inr (.inl (.inr (ports i),u)))) j
    else .input (.inr (.inr (.inl (.inr (ports i)),j)))

/-- Geometric routing suffix, with rows encoded most-significant-bit first. -/
noncomputable def tail (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin A → Fin n) :
    Frame σ (Fin (count m C J A) × Fin w) :=
  (prepared F).step fun q => bits F hk old ports (order.symm q.1) q.2

/-- Numerical interpretation of the native routing suffix. -/
noncomputable def entry (old : Fin J → Fin s) (ports : Fin A → Fin n) (x : σ → Bool) :
    Column m C J A → ℕ
  | .inl (.inl (.inl (.inl (i,c)))) => value fun j => (SuppliedOffsets.frame F).eval x (.inl (endpoint i c),j)
  | .inl (.inl (.inl (.inr c))) => value fun j => (SuppliedOffsets.frame F).eval x (.inr c,j)
  | .inl (.inl (.inr _)) => 0
  | .inl (.inr (i,c)) => if c=0 then (data F x).owner (old i) else 0
  | .inr (i,c) => if c=0 then (data F x).loc (.inr (ports i))
    else value fun j => (SuppliedOffsets.frame F).eval x (.inl (.inr (ports i)),j)

private theorem zero_value : ∀ w, value (fun _ : Fin w => false) = 0
  | 0 => rfl
  | w+1 => by simp [value,zero_value w]

/-- Every routing suffix word decodes to the computed placement or offset, including
the concrete zero-initialization of the private prefix pass. -/
theorem tail_value (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin A → Fin n) (x : σ → Bool)
    (i : Column m C J A) :
    value (fun j => (tail F hk old ports).eval x (order i,j)) = entry F old ports x i := by
  simp only [tail,Frame.step_eval,Equiv.symm_apply_apply]
  rcases i with ((((⟨i,c⟩ | c) | c) | ⟨i,c⟩) | ⟨i,c⟩)
  · simp [bits,entry,prepared,StatementCircuit.Expr.eval]
  · simp [bits,entry,prepared,StatementCircuit.Expr.eval]
  · exact zero_value w
  · by_cases h : c=0
    · simp only [bits,entry,h,ite_true]
      change wordValue ((prepared F).eval x) (pad hk _) = _
      rw [pad_value]
      simp [wordValue,prepared,StatementCircuit.Expr.eval,data,Function.comp_def]
    · simpa only [bits,entry,ite_eq_right h,StatementCircuit.Expr.eval] using zero_value w
  · by_cases h : c=0
    · simp only [bits,entry,h,ite_true]
      change wordValue ((prepared F).eval x) (pad hk _) = _
      rw [pad_value]
      simp [wordValue,prepared,StatementCircuit.Expr.eval,data]
    · simp [bits,entry,h,prepared,StatementCircuit.Expr.eval]

/-- The two arrays run on the same physical input and precede the caller's further
geometry outputs. The caller's validity bit remains the validity bit of the full program. -/
noncomputable def full (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin A → Fin n) (rest : Frame σ (Outputs o w)) :
    Frame σ (Outputs (m*3+(count m C J A+o)) w) :=
  GeometryOutput.prepend (CableTriples.frame F hk le_rfl) (GeometryOutput.prepend (tail F hk old ports) rest)

/-- Sharing the two address circuits, the routing suffix uses at most one additional
expression node per result bit. -/
theorem tail_size (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin A → Fin n) :
    (tail F hk old ports).size ≤ (labels F).size+(SuppliedOffsets.frame F).size+(count m C J A)*w := by
  have h (i : Column m C J A) (j : Fin w) : (bits F hk old ports i j).size ≤ 1 := by
    rcases i with ((((⟨i,c⟩ | c) | c) | ⟨i,c⟩) | ⟨i,c⟩)
    all_goals simp only [bits]
    all_goals first | exact le_rfl | (split <;> first | exact le_rfl | exact le_of_eq (pad_size _ _ (fun _ => rfl) _))
  have hh := Frame.step_size_le (prepared F) (fun q : Fin (count m C J A) × Fin w =>
    bits F hk old ports (order.symm q.1) q.2) 1 (fun q => h _ _)
  simpa only [tail,prepared,Frame.withInput_size,parallelFrame_size,Fintype.card_prod,Fintype.card_fin,Nat.mul_one] using hh

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
