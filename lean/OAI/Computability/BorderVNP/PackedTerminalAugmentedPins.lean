import OAI.Computability.BorderVNP.PackedTerminalRetainedReturn
import OAI.Computability.BorderVNP.PackedFrozenSelectedSchemas

/-! # Zero-gate terminal geometry, private extent and chronology on the actual augmented history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained.Terminal

open Packing.Inherited FrozenTape VPVNP.VerifierNetwork

variable {X G Geo : Type} [Fintype X] [Fintype G] [Fintype Geo] {a w d active reserve : ℕ}
variable (S : Format)

local notation "allInputs" => ((X ⊕ Fin reserve) ⊕ S.Output Geo a w d)

/-- Retain the full terminal state for post-sewing work and history adapters. -/
noncomputable def saved : Frame allInputs (S.Output Geo a w d) := Frame.initial Sum.inr

@[simp] theorem saved_size : (saved (X := X) (Geo := Geo) (a := a) (w := w) (d := d) (reserve := reserve) S).size=0 := rfl

/-- Select a terminal route or geometry bit from the saved full outer program. -/
noncomputable def route : Frame allInputs Geo := Frame.initial fun i => .inr (.inl (.inl i))

/-- The width used by the address/export stage. The false column is the true
private work width and the true column is the installed full site extent. -/
noncomputable def width (extent : Bool) : Frame allInputs (Fin a × Fin w) := Frame.initial fun z => .inr (.inl (.inr (z.1,extent,z.2)))

/-- Every frozen enable, owner and scalar field comes from the very same saved
terminal history. No additional evaluation of the chronological tree is needed. -/
noncomputable def history : Frame allInputs (Pins S.Rows S.Payload d) := Frame.initial fun z => .inr (.inr z)

@[simp] theorem route_size : (route (X := X) (a := a) (w := w) (d := d) (reserve := reserve) S (Geo := Geo)).size = 0 := rfl
@[simp] theorem width_size (b : Bool) : (width (X := X) (Geo := Geo) (d := d) (reserve := reserve) (a := a) (w := w) S b).size = 0 := rfl
@[simp] theorem history_size : (history (X := X) (Geo := Geo) (a := a) (w := w) (d := d) (reserve := reserve) S).size = 0 := rfl

variable (aug : Frame (X ⊕ G) ((S.Output Geo a w d) ⊕ Unit)) (ord : G ≃ Fin active) (fit : active≤reserve)
variable (x : X → Bool) (raw : Fin reserve → Bool)
local notation3 "out₀" => fun j : S.Output Geo a w d => aug.eval (Sum.elim x (readProfile ord fit raw)) (.inl j)
local notation3 "branch₀" => Retained.branch aug ord fit x raw

/-- The complete numerical and chronological saved state, at the actual native
profile literal, is exposed directly on these three input selections. -/
theorem read :
    (route S).eval branch₀ = (fun i => out₀ (.inl (.inl i))) ∧
    (∀ b, (width S b).eval branch₀ = fun z => out₀ (.inl (.inr (z.1,b,z.2)))) ∧
    (history S).eval branch₀ = fun j => out₀ (.inr j) := by
  refine ⟨funext fun j => ?_,fun b => funext fun j => ?_,funext fun j => ?_⟩
  · simp [route,Retained.branch]
  · simp [width,Retained.branch]
  · simp [history,Retained.branch]

/-- The input bank for post-sewing transformations and original tape projection
is exactly the augmented history output evaluated on the active broadcast. -/
theorem saved_read : (saved S).eval branch₀ = out₀ := by
  funext j; simp [saved,Retained.branch]

/-- Transport the selected schedule's actual semantic image onto the history
pins consumed by the joined terminal packet. -/
theorem image {A : Type} (siteID : A ↪ Fin a) (program : A → Site) (g : G → Bool)
    (code : readProfile ord fit raw=g)
    (selected : S.schema.Image (fun j => aug.eval (Sum.elim x g) (.inl (.inr j)))
      (siteID.trans Fin.valEmbedding) program) :
    S.schema.Image ((history S).eval branch₀) (siteID.trans Fin.valEmbedding) program := by
  rw [(read S aug ord fit x raw).2.2,code]
  exact selected

end PackedHistoryCircuit.Retained.Terminal

end BorderVNP
end Computability
end OAI
