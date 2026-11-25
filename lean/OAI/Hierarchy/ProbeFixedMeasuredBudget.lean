import OAI.Hierarchy.ProbeFixedWideWidth
import OAI.Hierarchy.ProbeFixedWideBudget
import OAI.Hierarchy.ProbeFixedWidePaidCheckout

namespace OAI
/-! # Cofinal native budget on the original reported width words -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT ReportSockets PurchaseFrozen
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

set_option cleanup.letToHave false
set_option maxRecDepth 8192
attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

set_option maxHeartbeats 2000000 in
private abbrev MeasuredWidthStatement : Prop :=
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width (small : width ≤ 2^h) (_ : v.widthFloor ≤ width)
      (budget : v.keepLimit*width+1 ≤ 2^h),
      v.paidWordFactor v.maxBits*width≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (size : ℕ)
        (extent : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
        (state : Word (Native.wordBits h (2^v.W) Native.copies)),
      let P := v.widePlacement h width
      let G := v.privateArena P h width
      let stock := v.fixedTerminalStock P h width
      let r := Fintype.card (Slots h (2^v.W) k)
      let page := v.wideSignedPage h width stock
      let f := v.nativeBoards P h width
      let cnt := rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger f v.mesh P.catalogue P.routes F G))
      let owners := sinkBank (v.catalystStaticStart P h width) cnt r P.catalogue.rows
      let banks := TerminalLayout.settlement page stock
      let src := TerminalLayout.source page
      let tab := TerminalLayout.table page
      let dst := TerminalLayout.destination page
      let tape := v.wideFundedRaw h width v.maxBits raw
      let order := wideRouteOrder h (2^v.W) k
      let m := v.wideSignedMidAt h width size stock v.radius π order tape
      let checks := v.wideSignedCheckoutAt h width size stock v.radius π order tape
      let _out := run (v.wideSignedChart h width stock) (events v.mesh) m
      let marks := v.birthMarks P h width r banks src tab dst owners m
      let ord := P.catalogue.ordinal v.sampler π v.depth marks (v.wideOrder h width) rfl
      let _len := lenCode v.sampler π v.depth marks v.radius
      let paid := Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw v.maxBits size extent age budget small state)
      checks (G.endAddress v.mesh)=0 →
      ∀e, ((Whole.Reconciliation.originalWidth
        (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k)
        paid.1 (ord e) : ℕ):ℝ)/width =
        v.fundedProfile h width π m v.maxBits (Whole.Reconciliation.usedAt
          (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k)
          paid.1) e

set_option maxHeartbeats 4000000 in
theorem wide_funded_width : MeasuredWidthStatement v := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  refine (v.wide_funded_width_of_paid.and v.wide_paid_checkout_eq).mono ?_
  intro h window
  obtain ⟨measurement,framed⟩ := window
  intro width small floor budget cap π raw size extent age state P G stock r page f cnt owners banks src tab dst tape
    order m checks out marks ord len paid accepted
  have frame := framed width small floor budget size
    ((v.wide_funded_extent h width v.maxBits).trans extent) π tape
  have result := measurement width small floor budget cap π raw size extent age state accepted frame
  exact result

set_option maxHeartbeats 2000000 in
def MeasuredBudgetAt (h width : ℕ) : Prop :=
  ∃ (bounded : width ≤ 2^h) (stockRoom : v.keepLimit*width+1 ≤ 2^h) (time : v.wideFundedHeight ≤ h),
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (size : ℕ)
        (extent : v.wideFundedSize h width v.maxBits ≤ size)
        (state : Word (Native.wordBits h (2^v.W) Native.copies)),
      let P := v.widePlacement h width
      let G := v.privateArena P h width
      let stock := v.fixedTerminalStock P h width
      let r := Fintype.card (Slots h (2^v.W) k)
      let page := v.wideSignedPage h width stock
      let f := v.nativeBoards P h width
      let cnt := rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger f v.mesh P.catalogue P.routes F G))
      let owners := sinkBank (v.catalystStaticStart P h width) cnt r P.catalogue.rows
      let banks := TerminalLayout.settlement page stock
      let src := TerminalLayout.source page
      let tab := TerminalLayout.table page
      let dst := TerminalLayout.destination page
      let tape := v.wideFundedRaw h width v.maxBits raw
      let order := wideRouteOrder h (2^v.W) k
      let m := v.wideSignedMidAt h width size stock v.radius π order tape
      let checks := v.wideSignedCheckoutAt h width size stock v.radius π order tape
      let _out := run (v.wideSignedChart h width stock) (events v.mesh) m
      let marks := v.birthMarks P h width r banks src tab dst owners m
      let ord := P.catalogue.ordinal v.sampler π v.depth marks (v.wideOrder h width) rfl
      let len := lenCode v.sampler π v.depth marks v.radius
      let paid := Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw v.maxBits size extent time stockRoom bounded state)
      checks (G.endAddress v.mesh)=0 →
      TermBudget p q Q Λ (2^h) width v.radius (∑_j : Columns h (2^v.W)×Fin k,fuel v.mesh*width)
        (scaleOf v.sampler π v.depth marks) (fun e => (len e:ℝ))
        (fun e => ((Whole.Reconciliation.originalWidth
        (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k)
        paid.1 (ord e) : ℕ):ℝ)/width)

set_option maxHeartbeats 4000000 in
/-- Every normalized width in this conclusion is read at its original ordinal
after the actual reserve reconciliation and route settlement. -/
theorem cofinal_funded_budget {κ B : ℝ} :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,v.MeasuredBudgetAt x.h x.w := by
  have heights : Filter.Tendsto (Tagged.WideParent.h (κ:=κ) (A:=B)) (Tagged.WideParent.large κ B)
      Filter.atTop := Filter.tendsto_comap
  have law := (heights.eventually v.wide_funded_width).and (heights.eventually v.funded_budget)
  have limits := (heights.eventually (Filter.eventually_ge_atTop v.widthFloor)).and
    (heights.eventually (Filter.eventually_ge_atTop v.wideFundedHeight))
  have room := (Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) 1).and
    ((Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) v.keepLimit).and
      (Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) (v.paidWordFactor v.maxBits)))
  refine (law.and (limits.and room)).mono ?_
  intro x conditions
  obtain ⟨⟨measured,account⟩,⟨minWidth,age⟩,cap,stockRoom,capacity⟩ := conditions
  have small : x.w≤2^x.h := (Nat.le_succ _).trans (by simpa only [one_mul] using cap)
  have floor := minWidth.trans x.property.1.2.1
  refine ⟨small,stockRoom,age,?_⟩
  intro π raw size extent state P G stock r page f cnt owners banks src tab dst tape order m checks out marks ord len
    paid accepted
  have capacity' : v.paidWordFactor v.maxBits*x.w ≤ 2^x.h := (Nat.le_succ _).trans capacity
  have same := measured x.w small floor stockRoom capacity' π raw size extent age state accepted
  have costs := account x.w small floor stockRoom π raw size extent age state accepted
  exact (congrArg (TermBudget p q Q Λ (2^x.h) x.w v.radius
    (∑ _j : Columns x.h (2^v.W) × Fin k, fuel v.mesh*x.w)
    (scaleOf v.sampler π v.depth marks) (fun e => (len e : ℝ))) (funext same)).mpr costs

/-- The choice preceding the protocol fixes one finite native format for every
width filter and every permutation. Its emitted widths satisfy the original budget. -/
theorem spectral_measured_cofinal (F : Type) [Field F] (k : ℕ) (hk : 0<k)
    (missing : ¬HasSpectralFlat F (k+1)) :
    TaggedShorterBudget.Cofinal (fun p q Q σ Λ =>
      ∃v : FixedProtocolFormat F k p q Q σ Λ, ∀κ B : ℝ,
        ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,v.MeasuredBudgetAt x.h x.w) := by
  apply TaggedShorterBudget.Cofinal.of_all
  intro p q Q σ Λ hp hq hQ hσ hΛ
  obtain ⟨v⟩ := fixed_format F k hk missing hp hq hQ hσ hΛ
  exact ⟨v,fun _ _ => v.cofinal_funded_budget⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
