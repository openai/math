import OAI.Computability.BorderVNP.PackedSewnRecordImage
import OAI.Computability.BorderVNP.PackedFrozenFormats

/-! # Sewing the final site tapes on the shared routed and saved history inputs

The current public endpoint fields and the saved selected-program output
occupy separate input banks. The old width columns and chronological rows
come directly from that saved output. No history replay is used by this stage.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
set_option quotPrecheck false

variable {Z Geo : Type} [Fintype Z] [Fintype Geo] {s n w : ℕ} (S : Format)
    (code : Fin s ↪ Fin (2^w)) (raw : Frame Z (Fragment.Pin n w))

private abbrev Joined (Z Geo : Type) (s w : ℕ) (S : Format) := Z ⊕ S.Output Geo s w w

private noncomputable def rawFrame : Frame (Joined Z Geo s w S) (Fragment.Pin n w) :=
  raw.subst (Frame.initial Sum.inl)

private def oldAmount (z : Amounts s w) : Joined Z Geo s w S := .inr (.inl (.inr z))

private noncomputable def earlier : Frame (Joined Z Geo s w S) (Pins S.Rows S.Payload w) :=
  Frame.initial fun z => .inr (.inr z)

/-- Append the sewn record bytes at the native terminal on its shared current and saved banks. -/
noncomputable def terminalHistory : Frame (Z ⊕ S.Output Geo s w w) (Pins (S.Rows ⊕ Row n) (S.Payload ⊕ Payload n w) w) :=
  complete code (rawFrame S raw) (oldAmount S) (earlier S)

private theorem raw_eval (z : Z → Bool) (y : S.Output Geo s w w → Bool) :
    (rawFrame S raw).eval (Sum.elim z y) = raw.eval z := by
  funext i
  rw [rawFrame,Frame.subst_eval]
  congr 1
  funext j
  simp

/-- The saved width bits and earlier rows introduce no gates. The real raw operand
emitter, sorting, two owner lookups and local record arithmetic are charged once. -/
theorem terminalHistory_size :
    (terminalHistory (Geo:=Geo) S code raw).size ≤ raw.size + 3000*(n+1)*(w+Nat.clog 2 n+1)^3 +
      2*lookupCost s n w w + (2*n*(1+w)+9*n*w)*(16*w+22) := by
  simp only [terminalHistory,complete_size,earlier,Frame.initial_size,zero_add]
  simpa only [rawFrame,Frame.subst_size,Frame.initial_size,zero_add] using
    tape_size code (rawFrame (Geo:=Geo) S raw) (oldAmount S)

variable {V : Type} (site : V ↪ Fin s) (prior : V → Site) (size : V → ℕ)
    (source : ∀ v, Fin (prior v).incoming → Option (Fin (size v)))
local notation "key" => (site.trans code).trans Fin.valEmbedding

/-- The shared terminal input computes the full post-sewing tape on the very same
native history used for the old geometry, work widths and extent words. -/
theorem terminalHistory_image (z : Z → Bool) (y : S.Output Geo s w w → Bool)
    (before : S.schema.Image (fun b => y (.inr b)) key prior)
    (owned : ∀ p ∈ Fragment.list (raw.eval z), ∃ v : V, p.site=(code (site v)).val)
    (cover : ∀ v, SewnField.Covers (Fragment.siteRuns (code (site v)).val (Fragment.list (raw.eval z))) (source v))
    (unique : ∀ v, Fragment.UniqueCover (prior v).incoming (Fragment.siteRuns (code (site v)).val (Fragment.list (raw.eval z))))
    (amounts : ∀ v b, value (fun j => y (.inl (.inr (site v,b,j)))) = if b then (prior v).size else (prior v).work)
    (fit : ∀ v, (prior v).size+size v < 2^w) (one : 1 < 2^w) :
    (S.schema.append (schema n w)).Image ((terminalHistory S code raw).eval (Sum.elim z y)) key
      (fun v => stage (prior v) (size v) (intervals (source v))) := by
  have e := raw_eval S raw z y
  have old : (earlier S).eval (Sum.elim z y) = (fun b => y (.inr b)) := by funext b; simp [earlier]
  exact complete_image code (rawFrame S raw) (oldAmount S) (Sum.elim z y) site prior size source
    (by rw [e]; exact owned) (by rw [e]; exact cover) (by rw [e]; exact unique)
    amounts fit one S.schema (earlier S) (old.symm ▸ before)

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
