import OAI.Computability.MultitapeWeakETH.HistoryRefreshKernelSpec
import OAI.Computability.MultitapeWeakETH.HistoryVisit
import OAI.Computability.VPVNP.PairSelectedPacketOrders

/-! # Typed operands of a chronological kernel call -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif CompressorRecords NetworkKernel
open Compression.DegreeRefresh Compression.Refresh PairSimulation LocalHistory NodeArguments TraversalRows
open PortRefresh RefreshMapOperands ShrinkBlockInputs ShrinkMap TreeDecode
open private next_number from OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages
open private ofFn_unique from OAI.Computability.VPVNP.PairRefreshTraversalOriginBits
open PortRefresh.TraversalPlan
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist : ℕ} (order : B.Entry ≃ Fin hist) (f : B.Entry → R) (hf : B.IsSolution f)

/-- The physical row, keyed old packets and parent packet all refer to the
same occurrence in the chronological term. The kernel's code and exponents
come directly from the reader of the selected origin. -/
def LevelKernelSpec (V : SelectedLevel B f hf) (w : ℕ) (point : ℕ → HistorySite) (run : Kernel) : Prop :=
  let t := V.pass.step.term V.term
  let r := originReader B f hf V.origin V.term
  ∀ (u : t.output.Site) (old : Placed t.place V.input.network.Half u) (new : t.output.Half u),
    let o := (siteOrder V.input).restrict (fun p => u = t.place p)
    let bank := NamedPackets.placedBank V.input _ u o old w
    let packet := pullBits (V.pass.output_eq V.term) (packed (V.pass.next V.term)) u new
    let row := ((outputOrder V).entries.symm u).val
    KernelSpec order (r.read u old new).encode (r.witness u old new).exponents
      (fun bits => run ((point row,bank,packet),bits))

variable {g : ℕ} (w : ℕ) (point : ℕ → HistorySite)
set_option allowUnsafeReducibility true in
attribute [local reducible] PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] ShrinkEnergy.chosenLayout

set_option maxHeartbeats 2000000 in
theorem shrink_level_spec (i : Fin S.steps) (X : State (a i) (packingLaneBits (a i) g))
    (sel : SelectedScore.Selection B X) (tape : List Bool) (run : Kernel)
    (checked : ∀ (z : SiteArguments B i g), shrinkLevel B f hf i X sel tape = shrinkLevel B f hf i z.state z.choice tape →
      let args := z.buffers () w
      KernelSpec order ((shrinkPassReaders B f hf i rfl z.state).kernel z.choice z.owner z.old z.parent).encode
        (B.shrinkPassWitnesses f hf i rfl z.state z.choice z.owner z.old z.parent).exponents
        (fun bits => run ((point (MapResidentRows.siteIndex z.state z.owner).val,args.1.1.2,args.1.2),bits))) :
    LevelKernelSpec order f hf (shrinkLevel B f hf i X sel tape) w point run := by
  intro u old new o bank packet row
  let z : SiteArguments B i g := ⟨X,sel,u,o,old,new,fun _ _ => 0⟩
  have num : row = (MapResidentRows.siteIndex X u).val :=
    next_number X B.shrink (S.shrink i) sel (packedSiteEquiv.symm u)
  rw [num]
  exact checked z rfl

local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)

set_option maxHeartbeats 1200000 in
theorem refresh_level_spec (X : State S.portExponent (S.portExponent+g))
    (c : DyadicRefreshChoice (a₀:=S.degreeExponent 0) X S.graph hE hC B.refresh)
    (tape : List Bool) (run : RefreshQuery → Option (List Tally))
    (checked : ∀ p old new, run (point (NewSlots.sites X.baseIndex (bitWordFinEquiv g) p).val,
        packed X (oldSite X p) old,
        packed (dyadicRefreshNext X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 c) (promotedSites p) new) =
        (TraversalPlan.emitted B order X c p old new).map (List.map (tally ∘ Fin.val))) :
    LevelKernelSpec order f hf (RefreshPlacement.selectedLevel B f hf X c tape) w point (refreshKernel run) := by
  intro u old new o bank packet row
  rcases u with ⟨⟨v,p⟩,lane⟩
  let port := ((v,lane),p)
  let one : {u // promotedSites port = place X u} := ⟨oldSite X port,old_place X port⟩
  have unique (j : {u // promotedSites port = place X u}) : j = one :=
    Subtype.ext ((place X).injective (j.property.symm.trans one.property))
  have packets : bank.2 = [packed X (oldSite X port) (old _ one.property)] :=
    ofFn_unique o one unique (fun j => packed X j.val (old j.val j.prop))
  let a := packed X (oldSite X port) (old _ one.property)
  let result := run (point row,a,packet)
  have hit := checked port (old _ one.property) new
  have spec := refresh_kernel_spec order f hf X c port old new result hit
  change KernelSpec _ _ _ (fun bits => (run (point row,bank.2.headD [],packet)).bind fun ls => some (ls,bits))
  rw [packets]
  exact spec

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
