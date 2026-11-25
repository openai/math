import OAI.Computability.BorderVNP.PackedTerminalSelectedWidth
import OAI.Computability.BorderVNP.PackedTerminalSignedHosts
import OAI.Computability.BorderVNP.PackedTerminalCompiledExport

/-! # Canonical signed terminal rows on the selected native profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity Shortening.PreparedBins
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing TeamContraction ParseBatch
open Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts Diagonal.ExternalSew.RowTrace
open EnrichedOuter EnrichedOuter.Boundary TerminalCells Inherited.WorkWords
open VPVNP VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM
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
    (installed : leaf.val.pack.layout = (DeckGrid.wiredGrid G axes d order position).groupedRepeat
      (fun _ : Fin (tileCount axes d) => inputBlockWidth r n axes d) order copies)
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
    (room : 2*(S.publicProgramFactor^T*B₀)<2^w) (basePorts : header.Reads leaf.val.pack.layout leaf.val.rows.site port)
    (baseCap : PhysicalEpochs.SiteCap leaf.val.route old.bankFields true B₀)
    (baseRead : WidthReads leaf.val old (widthBase.eval x))

include leafRows small room basePorts baseCap baseRead in
set_option maxHeartbeats 1600000 in
/-- The signed terminal's true sewn endpoints, cell owners, cable widths,
and retained pre-sew program extents are read on the same
native profile word. The surviving site row numbers are those in the
physical original-grid directory. These extents are the work inputs to
the final incidence scan that prepares the sewn site programs. -/
theorem compiledSigned_retained_fields (count : (fan S)^T*copies = R+1)
    (number : (Cube D → Deck (EnrichedOuter.depth S start T+1)) ≃ Fin cells)
    (vf : (sh).sites ≤ 2^w) (cf : cells ≤ 2^b) (blockPos : 0 < block) (blockSmall : block ≤ link)
    (wordFit : copies*block < 2^w)
    (q : (packHistory leaf C.machine.epoch T).Index) :
    let s := ((packHistory leaf C.machine.epoch T).term q).val
    let p : FieldExport.Params := ⟨R,r,G.program.length+t,link,block,tiles⟩
    let hp : p.Valid := ⟨blockPos,blockSmall,gridRoom G Fintype.card_pos⟩
    let word := (C.machine.nativeCode leaf base x initial widths ord fit q).val
    let hist := compile C.machine.steps T le_rfl (repeatLeaf (fan S) base T)
    let y := Sum.elim (Sum.elim x word) (fun j => hist.eval
      (Sum.elim x (readProfile (broadcastOrder (fan S) widths ord T) fit word)) (.inl j))
    let F := TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := Fintype.card (Cube D))
      (d := EnrichedOuter.depth S start T) (E := (sh).edges) vf cf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*block)
    let aux := C.nativeWidthColumn header ranges widthBase widths ord fit true
    let size := fun v => (C.machine.terminalPrivatePrograms (C.privateSiteRows port seeds) entry leaf old q v).program.size
    let source := boundFrame (factorEnum D) number cf (VerifierNetwork.Frame.initial Sum.inr) aux
    CellAddressPhysical.Represents (enrichedSewnLayout G axes d order position count C.machine leaf installed q)
        (fun v => number (reduceMove (EnrichedOuter.depth S start T) (s.route.origin v))) size s.rows.site
        (FieldExport.mergedEdges p hp s.rows.edge) finProdFinEquiv.toEmbedding (FieldExport.fields F p (attachedName offs copies))
        ((FieldExport.withSewnFields source).eval y) := by
  intro s p hp word hist y F aux size source
  let N := flattenPack T s.pack
  have cover : Covers s.rows.site size aux y := C.terminal_native_widths header ranges widthBase widths ord fit port seeds
    entry B₀ x leaf old base initial small room basePorts baseCap baseRead q true _
  let routePins := VerifierNetwork.Frame.initial (Sum.inr : Pins S start (boundaryShape S start) w T → Γ)
  have read : routePins.eval y = s.words := by
    have projected : routePins.eval y = output C.machine.steps T le_rfl (repeatLeaf (fan S) base T) x
        (readProfile (broadcastOrder (fan S) widths ord T) fit word) := by funext j; simp [routePins,y,hist,output]
    exact projected.trans (C.machine.nativeCode_state leaf base x initial widths ord fit q)
  have names (z : Fin ((fan S)^T) × Fin tiles) : (s.rows.site (N.layout.attach z)).val = offs z.1+z.2.val :=
    compiledPack_gridRow C leaf leafRows T le_rfl q z
  have old := route_represents (factorEnum D) number N s.route.flatten s.rows.flatten s.dummy
    finProdFinEquiv.toEmbedding vf cf (groupRow offs) (fun _ => copies*block)
    (fun z => (groupRow_pair offs z).trans (names z).symm) (fun _ => rfl) (fun _ => wordFit)
    (fun i hi => (hi ⟨finProdFinEquiv.symm i,finProdFinEquiv.apply_symm_apply i⟩).elim)
    routePins aux y (read.symm ▸ ((packHistory leaf C.machine.epoch T).term q).property.ready.flatten)
    size cover.live cover.hole
  let hosts := enrichedBlockHosts G axes d order position count C.machine leaf installed q
  have named (u : Fin (R+1)) (i : ℕ) (hi : i < tiles) :
      attachedName offs copies u.val i = (F.sites (s.rows.site (hosts.host (u,i)))).val := by
    have h := attached_name G Fintype.card_pos count N.layout s.rows.site offs names u i hi
    rw [enrichedBlockHosts_attached G axes d order position count C.machine leaf installed q] at h
    exact h
  have copiesPos : 0 < copies := Nat.pos_of_ne_zero (fun h => by rw [h,Nat.mul_zero] at count; omega)
  exact FieldExport.frame_represents p hp N.layout (groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count)
    hosts _ size s.rows.site s.rows.edge finProdFinEquiv.toEmbedding F source y old (attachedName offs copies) named
    ((Nat.le_mul_of_pos_left _ copiesPos).trans_lt wordFit)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
