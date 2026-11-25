import OAI.Hierarchy.ProbeFixedWideCash
import OAI.Hierarchy.TaggedWireWideLanguage

namespace OAI
/-! # Checkout prices on every complete original, physically encoded choice path -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope Tagged Filter
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def EncodedCashBound (h width : ℕ) (late : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) : Prop :=
  let P:=v.widePlacement h width
  let stock:=v.fixedTerminalStock P h width
  let reader:=v.wideSelector h width late budget small
  let es:=events v.mesh
  ∀ size,(v.privateArena P h width).endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h)))
    (seed : Boot.Tape h (2^v.W)),
    let origin:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) seed
    ∀ j : CalendarTape.Path reader.format.slot es origin,
      let bits:=CalendarTape.encode reader.format.slot es origin j
      let raw:=reader.format.windows.header es bits seed
      v.checkoutCharge h width size π raw≤6*(2^h:ℕ)

theorem encoded_cash (h width : ℕ) (late : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (prices : v.AcceptedCashBound h width) :
    v.EncodedCashBound h width late budget small := by
  unfold EncodedCashBound
  dsimp only
  intro size extent π seed j
  let reader:=v.wideSelector h width late budget small
  let P:=v.widePlacement h width
  let stock:=v.fixedTerminalStock P h width
  let origin:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) seed
  let bits:=CalendarTape.encode reader.format.slot (events v.mesh) origin j
  let raw:=reader.format.windows.header (events v.mesh) bits seed
  have chosen:=v.wide_encoded_path h width size extent v.radius π seed late budget small j
  have accepts:=(v.wide_verdict h width size extent v.radius π raw late budget small).2 chosen
  exact prices size extent π raw accepts

/-- Cofinitely, every complete branch and permutation runs within the signed
checkout bound on its corresponding encoded original tape. -/
theorem wide_path_cash {κ A : ℝ} :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∃ (late : v.wideStockHeight≤x.h) (budget : v.keepLimit*x.w+1≤2^x.h) (small : x.w≤2^x.h),
        v.EncodedCashBound x.h x.w late budget small := by
  have tall : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [v.wide_cash,tall.eventually (eventually_ge_atTop v.wideStockHeight),
    WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit,WideParent.fixed_mul_width (κ:=κ) (A:=A) 1]
    with x cash late budget bound
  have room : x.w+1≤2^x.h := by simpa only [one_mul] using bound
  exact ⟨late,budget,(Nat.le_succ _).trans room,v.encoded_cash x.h x.w late budget _ cash⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
