import OAI.Computability.BorderVNP.ShortenPublicParallelNames
import OAI.Computability.BorderVNP.PackedLookup
import OAI.Computability.BorderVNP.PackedInheritedLayerEmit

/-! # Carrying immutable public record fields across a parallel child merge

Only the owner key of a live frozen row changes when its child is placed in the
larger public site rectangle. One batched lookup per child translates these
keys. Every enable, tag and payload bit is forwarded without an arithmetic
gate, regardless of its field width or the private factor table behind it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Shortening.PublicParallel PackedHistogram ParseBatchSort VPVNP.VerifierNetwork Crossing
open scoped Classical

/-- One enable and one owner word per row, with independently named immutable payload pins. -/
abbrev Pins (Row Payload : Type*) (d : ℕ) := (Row × (Unit ⊕ Fin d)) ⊕ Payload

variable {Row Payload : Type*} [Fintype Row] [Fintype Payload] {copies V d d' : ℕ}
variable (oldCode : Fin V ↪ Fin (2^d)) (newCode : Fin (copies*V) ↪ Fin (2^d'))
private abbrev Source := Fin copies × Pins Row Payload d

private noncomputable def lookup (i : Fin copies) :
    Frame (Source (Row := Row) (Payload := Payload) (copies := copies) (d := d)) (Row × Fin d') :=
  PackedLookup.lookup (layout (Fin V) Row) oldCode (fun v => fixed (newCode (flat i v)))
    (fun r j => .input (i,.inl (r,.inr j)))

/-- The degree and the row-padding cost of a single fixed owner translation. -/
def lookupCost (slots queries d d' : ℕ) : ℕ :=
  let b := Nat.clog 2 (slots+queries)
  2^b * ((d+1+d') + ((d'+b)+1+d) + b^2*(24*((d'+b)+1+d)+1) +
    d'*(60*d+16*d'+33) + b^2*(24*(d'+b)+1))

private theorem lookup_size (i : Fin copies) :
    (lookup (Row := Row) (Payload := Payload) oldCode newCode i).size ≤ lookupCost V (Fintype.card Row) d d' := by
  have h := PackedHistogram.queries_size (layout (Fin V) Row)
    (fun v => fixed (σ := Source (Row := Row) (Payload := Payload) (copies := copies) (d := d)) (oldCode v))
    (fun v => fixed (newCode (flat i v))) (fun r j => .input (i,.inl (r,.inr j)))
    1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [lookup,PackedLookup.lookup,lookupCost,Fintype.card_fin,Nat.mul_one] using h

/-- Contract of the public parallel transfer, including raw payload bits and the exact
site rectangle of every live child record. -/
structure Carries (f : Frame (Fin copies × Pins Row Payload d) (Fin copies × Pins Row Payload d')) : Prop where
  /-- Presence is the original child's computed presence, including live zero-width rows. -/
  active : ∀ x i r, f.eval x (i,.inl (r,.inl ())) = x (i,.inl (r,.inl ()))
  /-- The immutable history payload is preserved bit-for-bit. -/
  payload : ∀ x i z, f.eval x (i,.inr z) = x (i,.inr z)
  /-- A live row naming an old site now names the public parallel copy of the same site. -/
  owner : ∀ x i r (v : Fin V), value (fun j => x (i,.inl (r,.inr j))) = (oldCode v).val →
    value (fun j => f.eval x (i,.inl (r,.inr j))) = (newCode (flat i v)).val

/-- One fixed pass for all child arrays. The explicit cost depends on the public row and
site rectangles and word widths and is independent of the private one-copy data. -/
theorem exists_carry :
    ∃ f : Frame (Fin copies × Pins Row Payload d) (Fin copies × Pins Row Payload d'),
      f.size ≤ 1 + copies * lookupCost V (Fintype.card Row) d d' ∧ Carries oldCode newCode f := by
  obtain ⟨all,hsize,heval⟩ := exists_parallelFrames (lookup (Row := Row) (Payload := Payload) oldCode newCode)
  let pick (z : Fin copies × Pins Row Payload d') : Source (Row := Row) (Payload := Payload) (copies := copies) (d := d) ⊕
      (Σ _ : Fin copies, Row × Fin d') :=
    match z.2 with
    | .inl (r,.inl ()) => .inl (z.1,.inl (r,.inl ()))
    | .inl (r,.inr j) => .inr ⟨z.1,r,j⟩
    | .inr payload => .inl (z.1,.inr payload)
  let f := all.withInput.select pick
  refine ⟨f,?_,⟨?_,?_,?_⟩⟩
  · have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => lookup_size (Row := Row) (Payload := Payload) oldCode newCode i
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
    simpa only [f,Frame.select_size,Frame.withInput_size] using hsize.trans (Nat.add_le_add_left hs 1)
  · intro x i r; simp [f,pick]
  · intro x i z; simp [f,pick]
  · intro x i r v hr
    simp only [f,Frame.select_eval,pick,Frame.withInput_eval_inr,heval]
    let request := fun (a : Row) (j : Fin d) => (BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.input (i,Sum.inl (a,Sum.inr j)) : VPVNP.VerifierNetwork.Expr (Fin copies × Pins Row Payload d))
    have h := PackedLookup.lookup_value (layout (Fin V) Row) oldCode
      (fun u => fixed (newCode (flat i u))) request x r v hr
    exact h.trans (fixed_value _ _)

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
