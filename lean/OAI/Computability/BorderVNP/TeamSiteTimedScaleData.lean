import OAI.Computability.BorderVNP.TeamSiteTimedGeometry
import OAI.Computability.BorderVNP.TeamSiteTimedDispatch

/-! # The manuscript's literal, exterior and native rows for the timed signed processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM UniversalMachine TeamContraction TeamContraction.ProcessorSlots TeamScales
open TeamSiteConsistency TeamSiteEvents
open FieldProcessor (Scale freeWidth)
open scoped BigOperators Classical

variable {pc reg args routines m g teams other n w e : ℕ} {Q Γ : Type} [Fintype Q] {α ξ : ℝ}
variable (P : TeamOpcode.Program pc reg args routines) (lib : Fin routines → Macro Q Γ m g) (mark : Fin routines → Γ)
variable (geo : Scale (machine P lib mark) pc reg args α ξ teams n other w e)

/-- The actual parser header pins the logical block, burst and team cutoff to their
paper values. Its free portion follows the real trusted-clock executable prefix. -/
noncomputable def scaleData (pub : Fin (other+1) → Fin args → Word w) (regs : Fin (other+1) → Fin reg → Word w)
    (advice : Fin (other+1) → Fin teams → Bool)
    (free : Fin (other+1) → Fin teams → Fin (freeWidth (machine P lib mark) α args reg teams w n) → Bool) :
    SiteData other teams reg args w (freeWidth (machine P lib mark) α args reg teams w n) :=
  ⟨pub,⟨block ξ n,geo.baseline.blockWord⟩,⟨ticks ξ teams n,geo.baseline.tickWord⟩,
    ⟨width n (1/2),geo.baseline.capWord⟩,regs,advice,free⟩

/-- Every processor reads two full literal fields and one directed exterior field for
each other team. The size bound is independent of their chosen bits. -/
theorem scaleInput (S : SiteData other teams reg args w (freeWidth (machine P lib mark) α args reg teams w n))
    {d : ℕ} (u : Fin (other+1)) (j : Fin teams) (pin : Fin d → Bool)
    (ext : Exterior other teams (link ξ (other+1) n) → Bool) (ib hb sb : ℕ) :
    let G := wiringWith (machine P lib mark) P S d (link ξ (other+1) n) n e geo.fits
    ((G.processorFields u pin ext ib hb sb).row j).length ≤ 3*block ξ n := by
  intro G
  apply ((G.processorFields u pin ext ib hb sb).row_length j).trans_le
  let lit := entryLiteral (machine P lib mark) (w+1) n (prefixCapacity teams args reg w n+1+freeWidth (machine P lib mark) α args reg teams w n)
  change lit + ((other+1)-1)*link ξ (other+1) n + lit ≤ 3*block ξ n
  have hl : lit = literal α n := geo.literalSize
  rw [Nat.add_sub_cancel,hl]
  exact (show literal α n+other*link ξ (other+1) n+literal α n = 2*literal α n+other*link ξ (other+1) n by omega) ▸ geo.localInput

/-- One native signed execution value per team uses the true initial row bits,
the original private instruction tables with the exact `n^25` cutoff, and its
actual finite-PC start. -/
noncomputable def scaleMachine (pub : Fin args → Word w) (regs : Fin reg → Word w) (rows : Fin teams → List Bool) :
    MachineInput w (TeamOpcode.State w pc reg) :=
  ⟨P.fetch pub (macros lib (n^25+1)),⟨P.base.entry,regs⟩,(List.ofFn rows).flatten.length,
    TeamTapeInputEmit.headerWord w (List.ofFn rows).flatten⟩

/-- Exact signed contraction on the real trusted processor at a fixed admissible scale,
for every external pin and all independent data literal choices. -/
def AtScale : Prop :=
  ∀ (pub : Fin (other+1) → Fin args → Word w) (regs : Fin (other+1) → Fin reg → Word w)
    (advice : Fin (other+1) → Fin teams → Bool)
    (free : Fin (other+1) → Fin teams → Fin (freeWidth (machine P lib mark) α args reg teams w n) → Bool)
    {d : ℕ} (pin : Fin d → Bool) (ib hb sb : Fin (other+1) → ℕ),
    let S := scaleData P lib mark geo pub regs advice free
    let G := wiringWith (machine P lib mark) P S d (link ξ (other+1) n) n e geo.fits
    Diagonal.signedContraction G.slot pin =
      ∑ ext, ∏ u, let rows := (G.processorFields u pin ext (ib u) (hb u) (sb u)).row
        nativeValue (scaleMachine (n := n) P lib (pub u) (regs u) rows) (ticks ξ teams n) (width n (1/2)) (n^25)

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
