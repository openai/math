import OAI.Hierarchy.TaggedWirePrefixCursor

namespace OAI
/-! # Branch reindexing preserves both the private tape and the actual final cursor -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar Tagged LinearAlgebra.SpectralBooks ChordGraph
open scoped BigOperators Classical
variable {X : Type} {slot : Event→Slot X} {events : List Event} {x₀ : X}
local notation "P" => Prefix slot events x₀

theorem replay_injective {tail x} (p : P tail x) : Function.Injective (replay p) := by
  intro i j eqn
  apply (encode slot tail x).injective
  funext b
  have same := congrArg (fun q : Path cursorSlot tail (atCursor p)=>
    encode cursorSlot tail (atCursor p) q (b.cast (bitCount (events:=events) (x₀:=x₀) tail).symm)) eqn
  exact (replay_word p i b).symm.trans (same.trans (replay_word p j b))

def histories {tail x} (p : P tail x) : Path slot tail x≃Path cursorSlot tail (atCursor p) :=
  Equiv.ofBijective (replay p) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨replay_injective p,(Fintype.card_congr (original p)).symm⟩)

theorem replay_end : ∀{tail x}(p : P tail x)(j : Path slot tail x),
    terminal cursorSlot tail (atCursor p) (replay p j)=atCursor (finish p j)
  | [],_,_,_=>rfl
  | _e::tail,_x,p,⟨c,rest⟩=>
    (replay_tail_apply p c rest (terminal cursorSlot tail)).trans (replay_end (advance p c) rest)

theorem terminal_history {tail x} (p : P tail x) (j : Path cursorSlot tail (atCursor p)) :
    terminal cursorSlot tail (atCursor p) j=atCursor (finish p ((histories p).symm j)) := by
  exact ((congrArg (terminal cursorSlot tail (atCursor p)) ((histories p).apply_symm_apply j)).symm).trans
    (replay_end p ((histories p).symm j))

theorem original_word {tail x} (p : P tail x) (j : Path cursorSlot tail (atCursor p)) (b : Fin (bits slot tail)) :
    encode cursorSlot tail (atCursor p) j (b.cast (bitCount (events:=events) (x₀:=x₀) tail).symm)=
      encode slot tail x ((histories p).symm j) b := by
  apply ((congrArg (fun c=>encode cursorSlot tail (atCursor p) c _) ((histories p).apply_symm_apply j)).symm).trans
  exact replay_word p _ b

end Hierarchy.WireTelescope.CalendarTape.Prefix

end
end OAI
