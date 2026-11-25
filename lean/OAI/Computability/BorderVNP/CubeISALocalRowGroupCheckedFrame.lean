import OAI.Computability.BorderVNP.CubeISALocalRowGroupFields
import OAI.Computability.BorderVNP.CubeISALocalRowGroupRoom

/-! # Constructing the actual frame for the seventh public scheduling instruction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally CubeHeaderInstall
open TeamContraction.JointHeader Finset

/-- The computed histogram, greedy team assignment and capacity guard all start
from the physical header and the fixed arena. The word bounds concern the real
aggregate histogram and exterior volume. -/
theorem checkedFrame_of_decoded {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    (bits : List Bool) (selected m : Memory w) (regs : Bank w)
    (decl : Broadcast a.n a.header.d a.header.cap) (r X : ℕ)
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits selected)
    (decoded : DecodedRows a (readings pub) f.dst decl (readings selected) (.ofWords regs m))
    (axis : readCode (a.n+1) decl.1 < a.n+1) (axes : a.header.a = a.n+1)
    (primary : (pub 0).val+112 ≤ a.header.header) (extent : f.dst+bits.length ≤ a.header.header)
    (count : readings selected ((pub 0).val+11) = a.cells)
    (teams : f.teams = r+1) (reserved : a.teams = r+1) (budget : (old 0).val = X)
    (alpha : 0 < a.header.d) (high : a.stop < 2^w) (million : 1000000 < 2^w)
    (scaled : 1000000*X*(r+1) < 2^w) :
    let frame := (pub 0).val
    let l := weightLayout a frame (readCode (a.n+1) decl.1)
    (∑ i ∈ range a.header.d, l.weight (readings m) i) < 2^w →
      GroupWeights.CheckedFrame l (teamLayout a r) (readings m) w X := by
  intro frame l mass
  obtain ⟨hist,assign,guard⟩ := groupFields_of_decoded pub f a old fresh profile gates outputs width off ell
    bits selected m regs decl r X pins decoded axis primary extent count teams budget high
  have fit := weightFits_of_arena a w frame _ (readings m) axes alpha axis high mass
  have room := weightSetup_of_arena a w frame _ (readings m) primary axis high million fit
  have cap := budgetFits_of_arena a w frame r X reserved primary high million scaled
  have frameBound : frame+77 < 2^w := by
    have header := header_le_publicBase a
    have before := a.separated
    dsimp only [frame] at *
    omega
  refine ⟨hist,room,fit,teamAllocated_of_arena a w r reserved high,frameBound,assign,rfl,rfl,?_,guard,cap,?_⟩
  · intro k hk i _
    simp at hk
    exact (groupFrame_ne a frame primary k (by omega)).1 i
  · intro k hk
    simp at hk
    obtain ⟨one,two,three⟩ := groupFrame_ne a frame primary k (by omega)
    exact ⟨fun i _ => one i,fun j => two j.val,fun i _ => three i⟩

/-- From the actual return of the label and interval passes, execute the fitted powers
and declaration programs and recover the checked scheduling frame on their exact image.
The declaration needs only its intrinsic binary range checks here. -/
theorem checkedFrame_of_pins {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh gates outputs width off ell : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (selected : Memory w)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap)
    (r X : ℕ) :
    let frame := (pub 0).val
    let l := weightLayout a frame (readCode (a.n+1) decl.1)
    let input := powerHeaderImage a f.dst (readings selected)
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    BootPins pub f (jointFields (a.extension old) fresh G.length gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw selected → a.header = physical →
    frame+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header → readings selected (frame+11) = a.cells →
    f.teams = r+1 → a.teams = r+1 → (old 0).val = X → 0 < a.header.d → 0 < a.header.blocks →
    0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w → 1000000 < 2^w → 1000000*X*(r+1) < 2^w →
    declarationInRange decl → (∑ i ∈ range a.header.d, l.weight input i) < 2^w →
    GroupWeights.CheckedFrame l (teamLayout a r) input w X := by
  intro frame l input raw physical pins eq primary extent count teams reserved budget alpha blocks stride high million scaled valid mass
  have check := publicBoot_pinned a old fresh gates outputs width off ell mac reg G claims pad decl
    pins eq primary extent alpha blocks stride high
  obtain ⟨_,out,m,_,_,decoded⟩ := check.complete valid
  have image : readings m = input := decoded.1
  rw [← image] at mass ⊢
  exact checkedFrame_of_decoded pub f a old fresh G.length gates outputs width off ell raw selected m out decl
    r X pins decoded valid.1 (congrArg Inputs.a eq) primary extent count teams reserved budget alpha high million scaled mass

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
