import OAI.Hierarchy.ProbeFixedWideReadbackRun
import OAI.Hierarchy.ProbeFixedWidePurchasedRows
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedCatalystEventRoom
import OAI.Hierarchy.ProtocolRAMCalendarDatedSeparation

namespace OAI
/-! # The actual accepted signed execution supplies all chronological price readbacks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W

/-- The single verdict field in this signed, booted execution recognizes the
admissible chronological choices at the very same memory. -/
theorem wide_verdict (h width size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size)
    (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
    (late : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    let P:=v.widePlacement h width
    let A:=v.privateArena P h width
    let stock:=v.fixedTerminalStock P h width
    let C:=v.wideSignedChart h width stock
    let order:=wideRouteOrder h D k
    v.wideSignedCheckoutAt h width size stock M π order raw (A.endAddress v.mesh)=0 ↔
      admissible C (events v.mesh) (v.wideSignedMidAt h width size stock M π order raw) := by
  intro P A stock C order
  let bits:=v.wideSignedPage h width stock
  let r:=Fintype.card (Slots h D k)
  let decl:=declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A)
  let owners:=sinkBank (v.catalystStaticStart P h width) (rowOnlyCount v.mesh decl) r P.catalogue.rows
  let banks:=TerminalLayout.settlement bits stock
  let src:=TerminalLayout.source bits
  let tab:=TerminalLayout.table bits
  let dst:=TerminalLayout.destination bits
  have whole:=(v.wide_stock_at h width size extent M π raw late budget small).mounted_all
  have sep : separated C (events v.mesh) := by
    apply separated_of_dated C A
    · exact fun e x hx=>(v.event_prefix P h width r banks src tab dst owners e x hx).1
    · exact fun a _=>v.catalyst_dated_verdict P h width r banks src tab dst owners a
  have wide : 0<Native.wordBits h D Native.copies := by rw [Native.wordBits_linear];omega
  exact checked_read C (A.endAddress v.mesh) _ whole sep wide

/-- Every original signed input accepted by the physical verdict word has a
price readback on that very execution, uniformly in the tape extension and
the data permutation. -/
theorem readback_run :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.widthFloor ≤ width → v.keepLimit*width+1 ≤ 2^h →
      let P := v.widePlacement h width
      let A := v.privateArena P h width
      let stock := v.fixedTerminalStock P h width
      let bits := v.wideSignedPage h width stock
      let r := Fintype.card (Slots h D k)
      let decl := declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A)
      let owners := sinkBank (v.catalystStaticStart P h width) (rowOnlyCount v.mesh decl) r P.catalogue.rows
      ∀ size, A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D),
        let order := wideRouteOrder h D k
        let m := v.wideSignedMidAt h width size stock v.radius π order raw
        v.wideSignedCheckoutAt h width size stock v.radius π order raw (A.endAddress v.mesh)=0 →
        Nonempty (v.ReadbackRun P h width r (TerminalLayout.settlement bits stock) (TerminalLayout.source bits)
          (TerminalLayout.table bits) (TerminalLayout.destination bits) owners π m m) := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [Filter.eventually_ge_atTop v.wideStockHeight, v.wide_face_room,
    v.wide_row_room, Filter.eventually_ge_atTop (2*v.keepLimit+2)] with h late faces rows dimension
  intro width small floor budget P A stock bits r decl owners size extent π raw order m accepted
  let banks := TerminalLayout.settlement bits stock
  let src := TerminalLayout.source bits
  let tab := TerminalLayout.table bits
  let dst := TerminalLayout.destination bits
  let C := v.wideSignedChart h width stock
  have lim := v.wide_stock_sizes h width late budget small
  have inventory := v.wide_stock_at h width size extent v.radius π raw late budget small
  have whole := inventory.mounted_all
  have valid:=(v.wide_verdict h width size extent v.radius π raw late budget small).mp accepted
  obtain ⟨_,_,seen,«public»,_,_,_,_,_⟩ :=
    v.wide_signed_boot_at h width size extent stock v.radius π order raw lim.words.addresses
  have picture := rows width
  refine ⟨v.wide_readback_of_rows h width size extent π raw lim.words.addresses small floor budget
    (dimension.trans (Nat.lt_two_pow_self (n:=h)).le) lim.roles lim.alphabet lim.copies lim.mass inventory valid
    (fun a live => (v.wide_stock_layout h width size extent v.radius π raw lim.words budget lim.width
      lim.alphabet lim.rowsMass lim.roles a live).1)
    (v.wide_payload_rows h width r banks src tab dst owners π m seen «public» whole lim.words.addresses
      picture.1 picture.2 faces.1)
    (v.wide_purchased_rows h width r banks src tab dst owners π m seen «public» whole lim.words.addresses
      picture.1 picture.2 faces.1 faces.2.1 faces.2.2 lim.strip)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
