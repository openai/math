import OAI.Computability.BorderVNP.PackedInheritedWorkCompiledTree
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProfile

/-! # Reading terminal program widths from the native profile broadcast

The terminal address exporter accepts the raw reserved broadcast and the
geometry columns. The work and extent projections read the same active
broadcast positions as the geometry guard. The projection introduces no gates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open PackedHistoryCircuit PackedHistoryCircuit.Normalized
open Packing.Inherited.WorkWords VPVNP.VerifierNetwork
open scoped Classical

variable {X G Geo : Type} [Fintype X] [Fintype G] [Fintype Geo] {V w active reserve : ℕ}
    (hist : Frame (X ⊕ G) (WithWidths Geo V w ⊕ Unit)) (ord : G ≃ Fin active) (fit : active ≤ reserve)
local notation "Γ" => (X ⊕ Fin reserve) ⊕ Geo

/-- Project the chosen terminal width column and attach the reserved native
broadcast wires of each active chronological profile slot. -/
noncomputable def broadcastColumn (extent : Bool) : Frame Γ (Fin V × Fin w) :=
  (hist.select (fun j => .inl (.inr (j.1,extent,j.2)))).subst
    (Frame.initial (fun z => .inl (z.elim Sum.inl fun g => .inr ((ord g).castLE fit))))

@[simp] theorem broadcastColumn_size (extent : Bool) : (broadcastColumn hist ord fit extent).size = hist.size := by
  simp [broadcastColumn]

/-- The auxiliary input's numerical words are exactly the selected true
history values, regardless of the separate route outputs. -/
theorem broadcastColumn_read (extent : Bool) (x : X → Bool) (word : Fin reserve → Bool) (route : Geo → Bool) :
    (broadcastColumn hist ord fit extent).eval (Sum.elim (Sum.elim x word) route) =
      (assignedColumn extent).eval (fun j => hist.eval (Sum.elim x (readProfile ord fit word)) (.inl j)) := by
  have plug : (Frame.initial (fun z : X ⊕ G => (Sum.inl (z.elim Sum.inl fun g => .inr ((ord g).castLE fit)) : Γ))).eval
      (Sum.elim (Sum.elim x word) route) = Sum.elim x (readProfile ord fit word) := by
    funext z; cases z <;> simp [readProfile]
  funext j
  simp only [broadcastColumn,Frame.subst_eval,plug,Frame.select_eval,assignedColumn,Frame.initial_eval]

/-- Both occupied rows and vacant slots are preserved on the actual decoded
chronological histogram. -/
theorem broadcastColumn_covers {U : Type*} (id : U ↪ Fin V) (size : U → ℕ) (extent : Bool)
    (x : X → Bool) (word : Fin reserve → Bool) (route : Geo → Bool) {g : G → Bool}
    (native : readProfile ord fit word = g)
    (read : Covers id size (assignedColumn extent) (fun j => hist.eval (Sum.elim x g) (.inl j))) :
    Covers id size (broadcastColumn hist ord fit extent) (Sum.elim (Sum.elim x word) route) := by
  constructor
  · intro u
    simpa only [broadcastColumn_read,native] using read.live u
  · intro i hi
    simpa only [broadcastColumn_read,native] using read.hole i hi

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
