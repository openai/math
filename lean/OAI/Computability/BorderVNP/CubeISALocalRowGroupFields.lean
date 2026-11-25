import OAI.Computability.BorderVNP.CubeISALocalRowGroupLayout
import OAI.Computability.BorderVNP.CubeISALocalRowLabelArena
import OAI.Computability.BorderVNP.CubeScatterArenaAllocation

/-! # Reading all three group-scheduling frames after the actual declaration bootstrap -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally CubeHeaderInstall
open private label_arena_order from OAI.Computability.BorderVNP.CubeISALocalRowLabelArena

/-- The three real frame loads see the installed cube dimensions, selected coordinate and power,
physical address literals, initial team count and exterior-budget word. The cell count is the
value published by the geometry prefix, preserved through its label and declaration passes. -/
theorem groupFields_of_decoded {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    (bits : List Bool) (selected m : Memory w) (regs : Bank w)
    (decl : Broadcast a.n a.header.d a.header.cap) (r X : ℕ)
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits selected)
    (decoded : DecodedRows a (readings pub) f.dst decl (readings selected) (.ofWords regs m))
    (axis : readCode (a.n+1) decl.1 < a.n+1) (base : (pub 0).val+112 ≤ a.header.header)
    (extent : f.dst+bits.length ≤ a.header.header) (count : readings selected ((pub 0).val+11) = a.cells)
    (teams : f.teams = r+1) (budget : (old 0).val = X) (high : a.stop < 2^w) :
    let frame := (pub 0).val
    let l := weightLayout a frame (readCode (a.n+1) decl.1)
    let t := teamLayout a r
    l.Fields (readings m) ∧ t.Frame frame (readings m) ∧
      (⟨r+1,X,a.teamTotals⟩ : TeamBudget.Layout).Fields frame (readings m) := by
  intro frame l t
  obtain ⟨image,loaded,_,claimed,chosen,_,_⟩ := decoded
  change readings m = powerHeaderImage a f.dst (readings selected) at image
  have atBoot := pins.powerHeader a image base extent
  have order := label_arena_order a
  have source := a.source_order
  have apart := a.separated
  have group : a.groupWeights ≤ a.teamTotals ∧ a.teamTotals ≤ a.ownerBase := ⟨Nat.le_add_right ..,Nat.le_add_right ..⟩
  have numeric (k v : ℕ) (hk : a.operand k = some v) (hv : v ≤ a.stop) : readings m (frame+k) = v :=
    atBoot.arenaOperand a old fresh profile gates outputs width off ell hk (hv.trans_lt high)
  have pubBase := numeric 48 a.publicBase rfl (by omega)
  have demand := numeric 51 a.demands rfl (by omega)
  have alphabet := numeric 56 a.alphabet rfl (by omega)
  have weights := numeric 75 a.groupWeights rfl (by omega)
  have totals := numeric 76 a.teamTotals rfl (by omega)
  have owners := numeric 77 a.ownerBase rfl (by omega)
  have size : readings m (frame+11) = a.cells := by
    rw [image]
    unfold powerHeaderImage
    rw [headerImage_outside _ _ _ _ _ _ (.inl (show frame+11 < a.header.header by dsimp only [frame]; omega))]
    simp only [CubePowers.image,show ¬ a.powerBase ≤ frame+11 by dsimp only [frame]; omega,false_and,ite_false]
    exact count
  have num := numeric 74 a.header.d rfl (by have := source.2.2; omega)
  have rows : readings m (a.header.header+6) = a.header.volume a.n (selectorWidth a.n a.K a.h) := by
    rw [image,powerHeaderImage,headerImage_field _ _ _ _ _ _ (by decide) (by decide)]
    rfl
  have nr : readings m (frame+1) = r+1 := atBoot.teams.trans teams
  exact ⟨⟨loaded.d,loaded.axes,loaded.header,weights,size,pubBase,demand,loaded.power,alphabet,
    loaded.bc,chosen,claimed,rows,loaded.blocks,loaded.powers _ (Nat.le_of_lt_succ axis)⟩,
    ⟨nr,num,weights,totals,owners⟩,⟨nr,(atBoot.budgetWord a old fresh profile gates outputs width off ell).trans budget,totals⟩⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
