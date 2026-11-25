import OAI.Hierarchy.ProbeFixedCheckedInventory
import OAI.Hierarchy.ProbeFixedCalendarReadbacks
import OAI.Hierarchy.ProbeFixedReadbackProducer
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Cash and the terminal commodity stock of the accepted, signed native program -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT Filter
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

abbrev wideBilledAccount (h width : ℕ) :=
  let P:=v.widePlacement h width
  let G:=v.privateArena P h width
  let stock:=v.fixedTerminalStock P h width
  let bits:=v.wideSignedPage h width stock
  let r:=Fintype.card (Slots h (2^v.W) k)
  let rows:=declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F G)
  let owners:=sinkBank (v.catalystStaticStart P h width) (rowOnlyCount v.mesh rows) r P.catalogue.rows
  v.billedAccount P h width r (TerminalLayout.settlement bits stock) (TerminalLayout.source bits)
    (TerminalLayout.table bits) (TerminalLayout.destination bits) owners

/-- Posted signed cash and retained physical stock priced directly in the
memory which already contains the terminal verdict word. -/
def checkoutCharge (h width size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) : ℝ :=
  let P:=v.widePlacement h width
  let stock:=v.fixedTerminalStock P h width
  let A:=v.wideBilledAccount h width
  let out:=v.wideSignedCheckoutAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
  let final:=A.read (.outer (v.mesh.inject+v.mesh.cool) 0) out
  A.bank.cash final+pairing (A.bank.units width final) A.box

theorem checkout_charge_eq (h width size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) :
    let P:=v.widePlacement h width
    let stock:=v.fixedTerminalStock P h width
    let C:=v.wideSignedChart h width stock
    let A:=v.wideBilledAccount h width
    let m:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
    let final:=A.read (.outer (v.mesh.inject+v.mesh.cool) 0) (run C (events C.mesh) m)
    v.checkoutCharge h width size π raw=A.bank.cash final+pairing (A.bank.units width final) A.box := by
  intro P stock C A m final
  let a:=Attempt.outer (v.mesh.inject+v.mesh.cool) 0
  let bits:=v.wideSignedPage h width stock
  let r:=Fintype.card (Slots h (2^v.W) k)
  let G:=v.privateArena P h width
  let rows:=declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F G)
  let owners:=sinkBank (v.catalystStaticStart P h width) (rowOnlyCount v.mesh rows) r P.catalogue.rows
  have same : A.read a (checkedOut C ((v.privateArena P h width).endAddress v.mesh) m)=
      A.read a (run C (events C.mesh) m) :=
    v.terminal_check_state P h width r (TerminalLayout.settlement bits stock) (TerminalLayout.source bits)
      (TerminalLayout.table bits) (TerminalLayout.destination bits) owners m
  unfold checkoutCharge
  change A.bank.cash (A.read a (checkedOut C _ m))+pairing (A.bank.units width (A.read a (checkedOut C _ m))) A.box=_
  rw [same]

/-- The input is the original finite startup image with its actual selector tape.
Both the verdict and the inventory ledger use the actual checkout on that tape. -/
def AcceptedCashBound (h width : ℕ) : Prop :=
  let P:=v.widePlacement h width
  let G:=v.privateArena P h width
  let stock:=v.fixedTerminalStock P h width
  ∀ size, G.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
    v.wideSignedCheckoutAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw (G.endAddress v.mesh)=0 →
    v.checkoutCharge h width size π raw≤6*(2^h:ℕ)

theorem accepted_cash :
    ∀ᶠ h : ℕ in atTop,∀ width, width≤2^h → v.widthFloor≤width → v.keepLimit*width+1≤2^h →
      v.AcceptedCashBound h width := by
  filter_upwards [v.readback_run,v.calendar_cash] with h original settled
  intro width small floor stride
  unfold AcceptedCashBound
  dsimp only
  intro size extent π raw vote
  obtain ⟨receipts⟩:=original width small floor stride size extent π raw vote
  rw [v.checkout_charge_eq h width size π raw]
  exact settled _ width _ _ _ _ _ _ π _ _ receipts

/-- The comparison applies to every allowed payload width once the height is
large. The width and finite-tape inequalities follow from the wide format. -/
theorem wide_cash {κ A : ℝ} :
    ∀ᶠ x : Tagged.WideParent κ A in Tagged.WideParent.large κ A,v.AcceptedCashBound x.h x.w := by
  have heights : Tendsto (Tagged.WideParent.h (κ:=κ) (A:=A)) (Tagged.WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [heights.eventually v.accepted_cash,heights.eventually (eventually_ge_atTop v.widthFloor),
      Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit,
      Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=A) 1] with x ready above stride cap
  have natural : x.h≤x.w := x.property.1.2.1
  have room : x.w+1≤2^x.h := by simpa only [one_mul] using cap
  exact ready x.w ((Nat.le_succ _).trans room) (above.trans natural) stride

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
