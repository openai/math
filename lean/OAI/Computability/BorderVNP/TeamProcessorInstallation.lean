import OAI.Computability.BorderVNP.TeamProcessorLiteralScale
import OAI.Computability.BorderVNP.TransmissionSiteRowContext
import OAI.Computability.BorderVNP.TeamSiteProcessorRowClock

/-!
# The scaled RAM setup and measured physical processor contexts

The same exact literal, its optional pin copy and its exterior fields initialize
the native RAM and the physical row. The complete setup is valid for all choices
of their data. At every sufficiently large length the real processor context on
each such row fits the universal n³⁶ clock, including its private computations
and the concrete comparison sort.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP RAMTape BurstRAM TeamTapeHandoff TeamSite TeamSite.Processor TeamScales Filter

variable {pc reg k routines m g teams other n e w d : ℕ} {Q Γ : Type} [Fintype Q]
variable {P : TeamOpcode.Program pc reg k routines} {lib : Fin routines → Macro Q Γ m g}
variable {α ξ : ℝ}

/-- Supply arbitrary public registers and bits at the physical word width, while
fixing the three encoded clock parameters to the manuscript's actual integers. -/
noncomputable def SiteGeometry.data (geo : SiteGeometry P lib α ξ teams n other w e)
    (publicWords : Fin (other+1) → Fin k → Word w) (registers : Fin (other+1) → Fin reg → Word w)
    (advice : Fin (other+1) → Fin teams → Bool)
    (free : Fin (other+1) → Fin teams → Fin (siteFree P lib α teams w n) → Bool) :
    SiteData other teams reg k w (siteFree P lib α teams w n) :=
  ⟨publicWords,⟨block ξ n,geo.baseline.blockWord⟩,⟨ticks ξ teams n,geo.baseline.tickWord⟩,
    ⟨width n (1/2),geo.baseline.capWord⟩,registers,advice,free⟩

/-- At least half the reserved literal can carry the arbitrary original site
descriptions and the two striped public packets. -/
theorem SiteGeometry.free_half (geo : SiteGeometry P lib α ξ teams n other w e) :
    literal α n ≤ 2*siteFree P lib α teams w n := by
  have := geo.reserved
  unfold siteFree
  omega

/-- The actual parsed row length equals the charged stride for arbitrary exterior
bits and arbitrary optional pin assignments. -/
theorem SiteGeometry.input_length (geo : SiteGeometry P lib α ξ teams n other w e)
    (S : SiteData other teams reg k w (siteFree P lib α teams w n)) (u : Fin (other+1)) (j : Fin teams)
    (pin : Fin d → Bool) (ext : Exterior other teams (link ξ (other+1) n) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiring P lib S d (link ξ (other+1) n) n e geo.fits
    let F := G.processorFields u pin ext ibase hbase starbase
    (F.row j).length = 2*literal α n+other*link ξ (other+1) n := by
  intro G F
  apply (F.row_length j).trans
  let t := entryLiteral (Processor.machine P lib) (w+1) n
    (prefixCapacity teams k reg w n+1+siteFree P lib α teams w n)
  change t+(other+1-1)*link ξ (other+1) n+t = _
  have he : t = literal α n := geo.literalSize
  rw [he,Nat.add_sub_cancel]; ring

/-- The complete native Setup for the literal, exterior bits and optional pins of
this specific physical contraction. The checked initialization uses one bit per
RAM word, exactly as the physical parser does. -/
noncomputable def SiteGeometry.nativeSetup (geo : SiteGeometry P lib α ξ teams n other w e)
    (hr : 0 < teams) (S : SiteData other teams reg k w (siteFree P lib α teams w n))
    (u : Fin (other+1)) (pin : Fin d → Bool) (ext : Exterior other teams (link ξ (other+1) n) → Bool)
    (ibase hbase starbase fuel privateClock : ℕ) : TeamSiteConsistency.Setup teams w pc reg k routines e :=
  let G := wiring P lib S d (link ξ (other+1) n) n e geo.fits
  let F := G.processorFields u pin ext ibase hbase starbase
  geo.baseline.setup hr P (S.publicWords u) (TeamSiteEvents.macros lib fuel) ⟨P.base.entry,S.registers u⟩
    privateClock F.row (fun j => (geo.input_length S u j pin ext ibase hbase starbase).trans_le geo.localInput)

/-- When the site literals carry the prescribed caps, the physical validator and the
native Setup use identical words for the block, cumulative cutoff and private burst.
The canonical `SiteGeometry.data` constructor satisfies the three premises definitionally. -/
theorem SiteGeometry.nativeSetup_words (geo : SiteGeometry P lib α ξ teams n other w e)
    (hr : 0 < teams) (S : SiteData other teams reg k w (siteFree P lib α teams w n))
    (blockEq : S.block.val = block ξ n) (limitEq : S.limit.val = ticks ξ teams n)
    (capEq : S.burst.val = width n (1/2)) (u : Fin (other+1)) (pin : Fin d → Bool)
    (ext : Exterior other teams (link ξ (other+1) n) → Bool) (ibase hbase starbase fuel privateClock : ℕ) :
    let native := geo.nativeSetup hr S u pin ext ibase hbase starbase fuel privateClock
    native.block = S.block ∧ native.limit = S.limit ∧ native.cap = S.burst :=
  ⟨Fin.ext blockEq.symm,Fin.ext limitEq.symm,Fin.ext capEq.symm⟩

/-- At this geometry every incoming verified frame has a measured physical context
on the actual input tape, for arbitrary pins, comparator wires and successor guess. -/
def SiteGeometry.measured (geo : SiteGeometry P lib α ξ teams n other w e) : Prop :=
  ∀ (S : SiteData other teams reg k w (siteFree P lib α teams w n)), S.block.val = block ξ n →
    ∀ (fuel : ℕ), fuel ≤ n^25+1 → ∀ {d : ℕ} (u : Fin (other+1)) (j : Fin teams) (pin : Fin d → Bool)
    (ext : Exterior other teams (link ξ (other+1) n) → Bool) (int : Wires.Edge teams reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) (f : Frame w reg), f.bits = ingress (S.start P u) int j →
    let G := wiring P lib S d (link ξ (other+1) n) n e geo.fits
    let F := G.processorFields u pin ext ibase hbase starbase
    let stride := 2*literal α n+other*link ξ (other+1) n
    ∃ X : Row.Context P lib n (Nat.clog 2 teams) e w,
      RowInstalled S u j int f (List.ofFn (G.word pin ext int u j)) (F.row j) (j.val*stride) X ∧
      X.coversClock fuel (n^36) (fun es => X.cost (Row.nativeCost w m g fuel es) es)

/-- The universal clock covers every row at the validated numerical geometry. -/
theorem SiteGeometry.measured_of_clock (geo : SiteGeometry P lib α ξ teams n other w e)
    (clock : ∀ (X : Row.Context P lib n (Nat.clog 2 teams) e w) (fuel dataLength : ℕ),
      X.block.val ≤ n → 2+e+Nat.clog 2 teams ≤ n → dataLength ≤ n → fuel ≤ n^25+1 →
      X.preludeTicks ≤ Budget.inputCost n w (2^e) dataLength + Budget.prefixCost reg k w X.last →
      X.coversClock fuel (n^36) (fun es => X.cost (Row.nativeCost w m g fuel es) es)) : geo.measured := by
  intro S hBlock fuel hfuel d u j pin ext int ibase hbase starbase f incoming G F stride
  have len : (F.row j).length = stride := geo.input_length S u j pin ext ibase hbase starbase
  have localCap : stride ≤ 3*block ξ n := geo.localInput
  have atEnd : (j.val+1)*stride ≤ 2^w :=
    (Nat.mul_le_mul j.isLt localCap).trans geo.baseline.header
  have hwidth := geo.baseline.width
  have dim := geo.dimensions
  have prepare := siteRowContext P lib S d (link ξ (other+1) n) n e geo.fits (by omega)
    geo.baseline.localSort (by omega) geo.widened geo.comparators geo.baseline.sorter geo.baseline.pcs
    u j pin ext int ibase hbase starbase f incoming
  change (2*(j.val*(entryStride (Processor.machine P lib) (w+1) n
    (prefixCapacity teams k reg w n+1+siteFree P lib α teams w n) other (link ξ (other+1) n)) + (F.row j).length) ≤ 2^(w+1)) →
    2*(F.row j).length + 2*S.block.val ≤ 4*2^e → _ at prepare
  rw [geo.stride] at prepare
  obtain ⟨X,hX⟩ := prepare
    (by rw [len,pow_succ]; change 2*(j.val*stride+stride) ≤ 2^w*2; rw [← Nat.succ_mul]; exact (Nat.mul_le_mul_left 2 atEnd).trans_eq (Nat.mul_comm ..))
    (by rw [len,hBlock]; have := geo.baseline.rowCapacity; omega)
  have hn : block ξ n ≤ n := by have h₁ := geo.baseline.rowCapacity; have h₂ := geo.baseline.localSort; omega
  exact ⟨X,hX,clock X fuel _ (hX.blockEq ▸ hBlock ▸ hn) dim hX.dataWithin hfuel hX.prefix_le⟩

/-- Uniform instantiation of the quantitative team layout and the whole physical row clock.
The positive team exponent is fixed before the RAM program. Every permitted team size and
every setting of the optional pins, public data and exterior/interior bits is covered. -/
theorem eventually_measured_sites (D : ℕ) {α ξ : ℝ} (hα : α < 3) (hξ : 0 < ξ)
    (hsmall : ξ < 3/2) (horder : ξ ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
      (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g),
      ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
      ∀ other : ℕ, ∃ geo : SiteGeometry P lib α ξ teams n other (logWidth teams n^(D+1))
        (Wires.sortExponent (block ξ n)), geo.measured := by
  obtain ⟨ω,hω,hgeom⟩ := eventually_siteGeometry D hα hξ hsmall horder
  refine ⟨ω,hω,?_⟩
  intro pc reg k routines m g Q Γ inst P lib
  filter_upwards [hgeom P lib,Row.eventually_row_clock P lib] with n geometry clock
  intro teams hr bound other
  have geo := geometry teams hr bound other
  exact ⟨geo,geo.measured_of_clock (fun X => clock X)⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
