import OAI.Computability.BorderVNP.PackedSewnRecordSection
import OAI.Computability.BorderVNP.PackedSewnFragmentMaximal

/-! # Compiling sparse sewing intervals and their public site-local operands

The first pass orders and coalesces genuine geometric fragments. Two batched
lookups on the resulting owner words read the measured work and complete old
extent. The final pass freezes the interval descriptors on the same bus.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField Crossing PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

/-- Index a bit of a source site’s work or total-size word. -/
abbrev Amounts (s w : ℕ) := Fin s × Bool × Fin w
/-- Input pins for the merged fragment together with its source-site amount table. -/
abbrev Columns (s n w : ℕ) := Fragment.Pin n w ⊕ Amounts s w

variable {s n w : ℕ} (code : Fin s ↪ Fin (2^w))

private noncomputable def amount (b : Bool) : Frame (Columns s n w) (Fin n × Fin w) :=
  PackedLookup.lookup (layout (Fin s) (Fin n)) code (fun v j => .input (.inr (v,b,j))) (fun i j => .input (.inl (i,.inr (0,j))))

private def readPin : Input n w → Columns s n w ⊕ ((Fin n × Fin w) ⊕ (Fin n × Fin w))
  | .inl z => .inl (.inl z)
  | .inr (i,b,j) => .inr (if b then .inr (i,j) else .inl (i,j))

/-- Look up both true old site prefixes once per active owner in the maximal sparse rectangle. -/
noncomputable def addressFrame : Frame (Columns s n w) (Input n w) :=
  (parallelFrame (amount code false) (amount code true)).withInput.select readPin

private theorem amount_size (b : Bool) : (amount (n:=n) code b).size ≤ lookupCost s n w w := by
  have h := queries_size (layout (Fin s) (Fin n)) (fun v => fixed (σ:=Columns s n w) (code v))
    (fun v j => .input (.inr (v,b,j))) (fun i j => .input (.inl (i,.inr (0,j))))
    1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [amount,PackedLookup.lookup,lookupCost,Fintype.card_fin,Nat.mul_one] using h

/-- Only the two physical sparse key searches contribute new gates in the address frame. -/
theorem addressFrame_size : (addressFrame (n:=n) code).size ≤ 2*lookupCost s n w w := by
  simp only [addressFrame,Frame.select_size,Frame.withInput_size,parallelFrame_size,two_mul]
  exact Nat.add_le_add (amount_size ..) (amount_size ..)

/-- The merged interval frame is forwarded without changing its enable or data words. -/
theorem addressFrame_fragment (x : Columns s n w → Bool) (z : Fragment.Pin n w) :
    (addressFrame code).eval x (.inl z) = x (.inl z) := by simp [addressFrame,readPin]

/-- A real site lookup reads the actual selected old scalar, including leading zeroes. -/
theorem addressFrame_value (x : Columns s n w → Bool) (i : Fin n) (v : Fin s) (b : Bool)
    (owner : (Fragment.parse (x ∘ Sum.inl) i).site = (code v).val) :
    value (fun j => (addressFrame code).eval x (.inr (i,b,j))) = value (fun j => x (.inr (v,b,j))) := by
  let table (a : Fin s) (j : Fin w) : Expr (Columns s n w) := .input (.inr (a,b,j))
  let query (r : Fin n) (j : Fin w) : Expr (Columns s n w) := .input (.inl (r,.inr (0,j)))
  have address : wordValue x (query i) = (code v).val := owner
  have h := PackedLookup.lookup_value (layout (Fin s) (Fin n)) code table query x i v address
  change value (fun j => (amount code b).eval x (i,j)) = value (fun j => x (.inr (v,b,j))) at h
  cases b <;> simpa only [addressFrame,readPin,Frame.select_eval,Frame.withInput_eval_inr,Bool.false_eq_true,
    ite_false,ite_true,parallelFrame_eval_inl,parallelFrame_eval_inr] using h

variable {σ : Type*} [Fintype σ] (raw : Frame σ (Fragment.Pin n w)) (col : Amounts s w → σ)

private noncomputable def together :=
  parallelFrame ((Fragment.maximal n w).subst raw) (Frame.initial col)

/-- The original state, its true geometry, maximal sparse sort, and two authenticated prefix reads. -/
noncomputable def sourceFrame := (addressFrame code).subst (together raw col)

/-- All public sewing words of the new immutable terminal site section. -/
noncomputable def tape := (frame n w).subst (sourceFrame code raw col)

/-- Gate count in terms of the physical fragment rectangle and real old site slots. -/
theorem tape_size : (tape code raw col).size ≤ raw.size + 3000*(n+1)*(w+Nat.clog 2 n+1)^3 +
    2*lookupCost s n w w + (2*n*(1+w)+9*n*w)*(16*w+22) := by
  simp only [tape,sourceFrame,together,Frame.subst_size,parallelFrame_size,Frame.initial_size,Nat.add_zero]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Fragment.maximal_size n w) _) (addressFrame_size code)) frame_size

/-- Real physical merged interval output inside the final encoder. -/
theorem source_fragment (x : σ → Bool) :
    (sourceFrame code raw col).eval x ∘ Sum.inl = (Fragment.maximal n w).eval (raw.eval x) := by
  funext z
  simp [sourceFrame,together,addressFrame_fragment]

/-- The work prefix and old extent are loaded from precisely the owner of the merged slot. -/
theorem source_base (x : σ → Bool) (i : Fin n) (v : Fin s) (b : Bool)
    (owner : (Fragment.parse ((Fragment.maximal n w).eval (raw.eval x)) i).site = (code v).val) :
    value (fun j => (sourceFrame code raw col).eval x (.inr (i,b,j))) = value (fun j => x (col (v,b,j))) := by
  let y := (together raw col).eval x
  have hy : y ∘ Sum.inl = (Fragment.maximal n w).eval (raw.eval x) := by
    funext z; simp [y,together]
  have h := addressFrame_value code y i v b (hy ▸ owner)
  simpa only [sourceFrame,Frame.subst_eval,y,together,parallelFrame_eval_inr,Frame.initial_eval] using h

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
