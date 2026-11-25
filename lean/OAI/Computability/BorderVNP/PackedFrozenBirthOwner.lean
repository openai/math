import OAI.Computability.BorderVNP.PackedFrozenBirthFields

/-! # Live and owner pins of the frozen main birth rows

Each native seed slot has a constant true enable and its actual stable physical
owner number. The payload side reuses the public packet word frame without
duplicating its gates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Birth

open Shortening.StaticRows Crossing ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork BankJoint
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)
    {S σ : Type*} [Fintype S] [Fintype σ] {n d w : ℕ} (seed : S ↪ Fin n) (old : ℕ)
    (packet : Frame σ (S × Output e first × Fin w))

/-- Integer owner in the physical rectangular site directory. -/
noncomputable def slot (z : S × TemplateSite e) : Fin (siteCapacity e old n) := siteSlot e old (seed z.1) z.2

/-- The fixed owner key and its shared always-live flag. -/
private noncomputable def literal (r : Row e first S) : Unit ⊕ Fin d → Bool
  | .inl _ => true
  | .inr b => (numberWords d).symm ⟨(slot e seed old r.1).val % 2^d,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ b

/-- Compiled immutable owner words and the original public packet bits. -/
noncomputable def frame : Frame σ (Pins (Row e first S) (S × Output e first × Fin w) d) :=
  let keys := (Frame.initial (id : σ → σ)).step fun r : Row e first S × (Unit ⊕ Fin d) =>
    .const (literal e first seed old r.1 r.2)
  parallelFrame keys packet

/-- Owner pins cost one constant gate per flag and per key bit. -/
theorem frame_size : (frame (d := d) e first seed old packet).size ≤
    Fintype.card (Row e first S)*(1+d)+packet.size := by
  have h := Frame.step_size_le (Frame.initial (id : σ → σ))
    (fun r : Row e first S × (Unit ⊕ Fin d) => StatementCircuit.Expr.const (literal e first seed old r.1 r.2))
    1 (fun _ => le_rfl)
  simp only [Frame.initial_size,zero_add,Fintype.card_prod,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,mul_one] at h
  unfold frame
  rw [parallelFrame_size]
  exact Nat.add_le_add_right h _

/-- Every represented main row is enabled, including repeated zero-copy boxes. -/
theorem active (x : σ → Bool) (r : Row e first S) :
    (frame (d := d) e first seed old packet).eval x (.inl (r,.inl ())) = true := by
  simp [frame,literal,StatementCircuit.Expr.eval]

/-- The owner circuit names the exact public site, with no truncation at the chosen key width. -/
theorem owner_value (fit : siteCapacity e old n ≤ 2^d) (x : σ → Bool) (r : Row e first S) :
    owner ((frame (d := d) e first seed old packet).eval x) r = (slot e seed old r.1).val := by
  have h := (slot e seed old r.1).isLt.trans_le fit
  simp [owner,frame,literal,StatementCircuit.Expr.eval,Nat.mod_eq_of_lt h]
  exact value_encode ⟨(slot e seed old r.1).val,h⟩

/-- The public packet's scalar bits are forwarded directly to the immutable tape. -/
theorem payload (x : σ → Bool) (z : S × Output e first × Fin w) :
    (frame (d := d) e first seed old packet).eval x (.inr z) = packet.eval x z :=
  parallelFrame_eval_inr ..

end Packing.Inherited.FrozenTape.Birth

end BorderVNP
end Computability
end OAI
