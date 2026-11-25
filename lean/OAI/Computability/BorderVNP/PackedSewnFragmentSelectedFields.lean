import OAI.Computability.BorderVNP.PackedSewnFragmentFields
import OAI.Computability.BorderVNP.PackedSewnWirePrivatePorts
import OAI.Computability.BorderVNP.PackedTerminalSignedRows
import OAI.Computability.BorderVNP.DiagonalExternalSewGroupedBudget
import OAI.Computability.BorderVNP.PackedBankPublicHistory
import OAI.Computability.BorderVNP.PackedInheritedWorkSewnCapacity

/-! # Native fields of both terminal fragment directories

The grouped port directory determines the original block host on either initial grid.
Each canonical profile broadcast drives both endpoint scans and the public sparse
cable rows, with all numerical fit conditions derived from the original bank cap.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity Shortening.PreparedBins
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing TeamContraction ParseBatch
open Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts Diagonal.ExternalSew.RowTrace
open EnrichedOuter EnrichedOuter.Boundary TerminalCells Inherited.WorkWords Packing.Inherited Packing.SewnField FieldExport
open VPVNP VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM
open private localRecords_mono from OAI.Computability.BorderVNP.ShortenEpochRoundRecords
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r t pins link inner n copies w T start : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes d : ℕ) (order : Fin (tileCount axes d) ≃ (Fin axes → Deck (d+2)))
    (position : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    (C : Compiled (fun _ : Fin (tileCount axes d) => copies*inputBlockWidth r n axes d) deep budget cap w)

local notation "tiles" => tileCount axes d
local notation "block" => inputBlockWidth r n axes d
local notation "sh" => boundaryShape S start T
local notation "offs" => flatOffset (compiledOffset S start) T

variable (leaf : Admissible (Good (S := S) (start := start) (shape := boundaryShape S start) (w := w)
    (bits := fun _ : Fin (tileCount axes d) => copies*inputBlockWidth r n axes d) budget) 0)
    (leafRows : ∀ a : Fin (tileCount axes d), (leaf.val.rows.site (leaf.val.pack.layout.attach a)).val = a.val)
    {X : Type} [Fintype X] (base : VerifierNetwork.Frame X (Pins S start (boundaryShape S start) w 0)) (x : X → Bool)
    (initial : base.eval x = leaf.val.words) {b cells reserve : ℕ}
    (widths : ℕ → ℕ) (ord : ∀ j, Machine.Guess S start (fun _ _ => w) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation "Γ" => (X ⊕ Fin reserve) ⊕ Pins S start (boundaryShape S start) w T

variable {np : ℕ} (header : Inherited.WorkWords.Ports np) (port : Fin (tileCount axes d) ↪ Fin np)
    (ranges : WidthRanges S start T w)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (entry : e.Entry → ℕ) (B₀ : ℕ)
    (widthBase : VerifierNetwork.Frame X (OuterWidthPins S start (boundaryShape S start) w 0))
    (old : Inherited.Site.Programs leaf.val.pack.layout)
    (small : (PortTable.mk np port header).Widths (fun _ : Fin (tileCount axes d) => copies*inputBlockWidth r n axes d) w)
    (room : 15*(S.publicProgramFactor^T*B₀)<2^w) (basePorts : header.Reads leaf.val.pack.layout leaf.val.rows.site port)
    (baseCap : PhysicalEpochs.SiteCap leaf.val.route old.bankFields true B₀)
    (baseRead : WidthReads leaf.val old (widthBase.eval x))


include leafRows room baseCap seeds entry in
set_option maxHeartbeats 2200000 in
/-- Any saved terminal returning the actual route and old program extent computes
the complete signed sewing fields, including vacant rows and endpoint validity. -/
theorem compiled_terminalFieldReads (count : (fan S)^T*copies=R+1)
    (number : (Cube D → Deck (EnrichedOuter.depth S start T+1)) ≃ Fin cells)
    (vf : (sh).sites ≤ 2^w) (cf : cells ≤ 2^b) (blockPos : 0<block) (blockSmall : block≤link)
    (wordFit : copies*block < 2^w) (q : (packHistory leaf C.machine.epoch T).Index)
    {Words : Type} [Fintype Words]
    (route : VerifierNetwork.Frame Words (Pins S start (boundaryShape S start) w T))
    (aux : VerifierNetwork.Frame Words (Fin (boundaryShape S start T).sites × Fin w))
    (y : Words → Bool) :
    let s := ((packHistory leaf C.machine.epoch T).term q).val
    let L := flattenPack T s.pack
    let p : FieldExport.Params := ⟨R,r,G.program.length+t,link,block,tiles⟩
    let hp : p.Valid := ⟨blockPos,blockSmall,gridRoom G Fintype.card_pos⟩
    let F := TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := Fintype.card (Cube D))
      (d := EnrichedOuter.depth S start T) (E := (sh).edges) vf cf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*block)
    let src := boundFrame (factorEnum D) number cf route aux
    let lane := groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count
    let hosts := attachedHosts G Fintype.card_pos count L.layout
    let amount := fun u => ((C.machine.terminalPrivatePrograms (C.privateSiteRows port seeds) entry leaf old q) u).program.size
    route.eval y = s.words → WorkWords.Covers s.rows.site amount aux y →
    CellAddressPhysical.Represents (finalLayout p hosts)
      (fun v => number (reduceMove (EnrichedOuter.depth S start T) (s.route.origin v))) amount
      s.rows.site (mergedEdges p hp s.rows.edge) finProdFinEquiv.toEmbedding (FieldExport.fields F p (attachedName offs copies))
      ((withSewnFields src).eval y) ∧
    Fragment.FieldReads L.layout p hp lane hosts s.rows.site s.rows.edge finProdFinEquiv.toEmbedding
      F (attachedName offs copies) FinalTies.routePresent ((withSewnFields src).eval y)
      (fun u => ((C.machine.terminalPrivatePrograms (C.privateSiteRows port seeds) entry leaf old q) u).program.size) := by
  intro s L p hp F src lane hosts amount geo cover
  let rows := C.privateSiteRows port seeds
  let prior := C.machine.terminalPrivatePrograms rows entry leaf old q
  have names (z : Fin ((fan S)^T) × Fin tiles) : (s.rows.site (L.layout.attach z)).val = offs z.1+z.2.val :=
    compiledPack_gridRow C leaf leafRows T le_rfl q z
  have copiesPos : 0 < copies := Nat.pos_of_ne_zero (fun h => by rw [h,Nat.mul_zero] at count; omega)
  have oldFit (u : L.layout.Site) : incoming L.layout u < 2^w := by
    have covered := (cover.live u).symm.trans_lt (ParseBatchSort.value_lt _)
    exact (prior u).size.symm.le.trans_lt ((Nat.le_add_left _ _ : (prior u).program.incoming ≤ amount u).trans_lt covered)
  have owner (a : FreeBlock R tiles) : hosts.groupOwner a = L.layout.attach ((teamBlocks _ _ count a.1).1,a.2) := by
    simp only [hosts,attachedHosts,BlockHosts.groupOwner,dite_eq_left a.2.isLt]
    exact congrArg L.layout.attach (Prod.ext rfl (Fin.ext rfl))
  have stagedFit (u : L.layout.Site) : amount u + incoming (finalLayout p hosts) u < 2^w := by
    let data := prior.bankFields
    let tile := reduceMove (EnrichedOuter.depth S start T) (s.route.origin u)
    let test := fun z : L.layout.Site => reduceMove (EnrichedOuter.depth S start T) (s.route.origin z) = tile
    have grouped := grouped_records_of_owner G axes d ((fan S)^T) copies count L.layout hosts owner blockPos blockSmall true
      data.prior data.payload test
    have oldCap := C.machine.terminalPrivatePrograms_bankCap rows entry leaf old true B₀ baseCap q tile
    have single := CellAddresses.wireCapacity_le (finalLayout p hosts) id u data.prior data.payload
    have mono := localRecords_mono (finalLayout p hosts) true data.prior data.payload
      (fun a (ha : id a=u) => congrArg (fun z => reduceMove (EnrichedOuter.depth S start T) (s.route.origin z)) ha)
    have amountCap : amount u ≤ localRecords L.layout true data.prior data.payload test := by
      have h := InheritedBank.payload_incoming_le L.layout data.prior data.payload u test rfl
      exact (Nat.add_le_add (Nat.le_add_right _ _) (prior u).size.le).trans h
    have newBound := single.trans (mono.trans grouped)
    have budgetBound := (Nat.le_add_left _ 1).trans oldCap
    exact (Nat.add_le_add (amountCap.trans budgetBound) (newBound.trans (Nat.mul_le_mul_left 7 budgetBound))).trans_lt (by omega)
  have newFit (u : L.layout.Site) : incoming (finalLayout p hosts) u < 2^w :=
    (Nat.le_add_left _ _).trans_lt (stagedFit u)
  have ready : RouteRows.Ready (factorEnum D) L s.route.flatten s.rows.flatten s.dummy (route.eval y) :=
    geo.symm ▸ ((packHistory leaf C.machine.epoch T).term q).property.ready.flatten
  have checked := TerminalCells.route_represents (factorEnum D) number L s.route.flatten s.rows.flatten s.dummy
    finProdFinEquiv.toEmbedding vf cf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*block)
    (fun z => (groupRow_pair offs z).trans (names z).symm) (fun _ => rfl) (fun _ => wordFit)
    (fun i hi => (hi ⟨finProdFinEquiv.symm i,finProdFinEquiv.apply_symm_apply i⟩).elim)
    route aux y ready amount cover.live cover.hole
  have post := frame_represents p hp L.layout lane hosts _ amount s.rows.site s.rows.edge finProdFinEquiv.toEmbedding F src y
    checked (attachedName offs copies) (attached_name G Fintype.card_pos count L.layout s.rows.site offs names)
    ((Nat.le_mul_of_pos_left _ copiesPos).trans_lt wordFit)
  have previous : (withSewnFields src).eval y ∘ Sum.inl = src.eval y := by
    funext z
    simp only [withSewnFields,VerifierNetwork.Frame.subst_eval,constants_eval,Function.comp_apply,Sum.elim_inl]
  refine ⟨post,?_,?_,Views.EndpointData.of_rep _ _ _ _ _ post,oldFit,newFit,?_,stagedFit,?_⟩
  · simp only [withSewnFields,VerifierNetwork.Frame.subst_eval,constants_eval,Sum.elim_inr]
    rfl
  · rw [previous]
    exact Views.EndpointData.of_rep _ _ _ _ _ checked
  · intro u
    rw [previous]
    exact checked.stage u
  · intro i
    have eq := congrFun previous (FinalTies.routePresent i)
    change (withSewnFields src).eval y (.inl (FinalTies.routePresent i)) = src.eval y (FinalTies.routePresent i) at eq
    rw [eq]
    exact FinalTies.route_present (factorEnum D) number cf L s.route.flatten s.rows.flatten s.dummy route aux y ready i

include leafRows small room basePorts baseCap baseRead seeds entry in
set_option maxHeartbeats 2200000 in
/-- Both raw fragment circuits read the true old and sewn pointers on the selected
history broadcast. Their word bounds follow from the cumulative private program cap. -/
theorem compiled_fragmentFields (count : (fan S)^T*copies=R+1)
    (number : (Cube D → Deck (EnrichedOuter.depth S start T+1)) ≃ Fin cells)
    (vf : (sh).sites ≤ 2^w) (cf : cells ≤ 2^b) (blockPos : 0<block) (blockSmall : block≤link)
    (wordFit : copies*block < 2^w) (q : (packHistory leaf C.machine.epoch T).Index) :
    let s := ((packHistory leaf C.machine.epoch T).term q).val
    let L := flattenPack T s.pack
    let p : FieldExport.Params := ⟨R,r,G.program.length+t,link,block,tiles⟩
    let hp : p.Valid := ⟨blockPos,blockSmall,gridRoom G Fintype.card_pos⟩
    let word := (C.machine.nativeCode leaf base x initial widths ord fit q).val
    let hist := compile C.machine.steps T le_rfl (repeatLeaf (fan S) base T)
    let y := Sum.elim (Sum.elim x word) (fun j => hist.eval
      (Sum.elim x (readProfile (broadcastOrder (fan S) widths ord T) fit word)) (.inl j))
    let F := TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := Fintype.card (Cube D))
      (d := EnrichedOuter.depth S start T) (E := (sh).edges) vf cf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*block)
    let aux := C.nativeWidthColumn header ranges widthBase widths ord fit true
    let src := boundFrame (factorEnum D) number cf (VerifierNetwork.Frame.initial Sum.inr) aux
    let lane := groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count
    let hosts := attachedHosts G Fintype.card_pos count L.layout
    Fragment.FieldReads L.layout p hp lane hosts s.rows.site s.rows.edge finProdFinEquiv.toEmbedding
      F (attachedName offs copies) FinalTies.routePresent ((withSewnFields src).eval y)
      (fun u => ((C.machine.terminalPrivatePrograms (C.privateSiteRows port seeds) entry leaf old q) u).program.size) := by
  intro s L p hp word hist y F aux src lane hosts
  let rows := C.privateSiteRows port seeds
  let prior := C.machine.terminalPrivatePrograms rows entry leaf old q
  let amount := fun u => (prior u).program.size
  have bound : 2*(S.publicProgramFactor^T*B₀)<2^w := by omega
  have cover : WorkWords.Covers s.rows.site amount aux y := C.terminal_native_widths header ranges widthBase widths ord fit port seeds
    entry B₀ x leaf old base initial small bound basePorts baseCap baseRead q true _
  let route := VerifierNetwork.Frame.initial (Sum.inr : Pins S start (boundaryShape S start) w T → Γ)
  have geo : route.eval y = s.words := by
    have projected : route.eval y = output C.machine.steps T le_rfl (repeatLeaf (fan S) base T) x
        (readProfile (broadcastOrder (fan S) widths ord T) fit word) := by funext j; simp [route,y,hist,output]
    exact projected.trans (C.machine.nativeCode_state leaf base x initial widths ord fit q)
  exact (compiled_terminalFieldReads G axes d C leaf leafRows port seeds entry B₀ old room baseCap
    count number vf cf blockPos blockSmall wordFit q route aux y geo cover).2

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
