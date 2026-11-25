import OAI.Computability.BorderVNP.PackedTerminalNativeWidth
import OAI.Computability.BorderVNP.PackedInheritedWorkSelected

/-! # Auxiliary address widths of every selected native history

The exporter obtains work and full extents from one fixed width-augmented
selected schedule. Both are those of the recursively installed terminal
site programs of the history encoded in the input broadcast.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.PhysicalEpochs EnrichedOuter TerminalCells
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (C : Compiled bits deep budget cap w)
    (p : WorkWords.Ports np) (ranges : WidthRanges S start T w) {X : Type} [Fintype X] {reserve : ℕ}
    (widthBase : Frame X (Boundary.OuterWidthPins S start (boundaryShape S start) w 0))
    (widths : ℕ → ℕ) (ord : ∀ j, Machine.Guess S start (fun _ _ => w) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation "widthHist" => compile (WidthFrames.steps (widthFrames C p ranges)) T le_rfl (repeatLeaf (fan S) widthBase T)
local notation "sh" => boundaryShape S start T
local notation "geo" => Boundary.Pins S start (boundaryShape S start) w T

/-- The history-independent projection used as the route exporter's actual
auxiliary width source. -/
noncomputable def nativeWidthColumn (extent : Bool) :
    Frame ((X ⊕ Fin reserve) ⊕ geo) (Fin (sh).sites × Fin w) :=
  broadcastColumn widthHist (broadcastOrder (fan S) widths ord T) fit extent

/-- Connecting the augmented history to the native word costs only its
own gates, with no gate charge per copied input or output. -/
theorem nativeWidthColumn_size (extent : Bool) :
    (C.nativeWidthColumn p ranges widthBase widths ord fit extent).size = (widthHist).size := by
  exact broadcastColumn_size ..

variable (port : P ↪ Fin np)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ) (B : ℕ) (x : X → Bool)
    (leaf : Admissible (Boundary.Good (S:=S) (start:=start) (bits:=bits) (shape:=boundaryShape S start) (w:=w) budget) 0)
    (old : Site.Programs leaf.val.pack.layout)
    (base : Frame X (Boundary.Pins S start (boundaryShape S start) w 0)) (initial : base.eval x = leaf.val.words)

set_option maxHeartbeats 1500000 in
/-- For the same broadcast and any terminal route-word view, the actual fixed
auxiliary frame names exactly the work or total size of each surviving site
program. It emits zero in every unoccupied slot of the scheduled rectangle. -/
theorem terminal_native_widths (small : (PortTable.mk np port p).Widths bits w)
    (room : 2*(S.publicProgramFactor^T*B)<2^w) (basePorts : p.Reads leaf.val.pack.layout leaf.val.rows.site port)
    (baseCap : SiteCap leaf.val.route old.bankFields true B) (baseRead : Boundary.WidthReads leaf.val old (widthBase.eval x))
    (q : (packHistory leaf C.machine.epoch T).Index) (extent : Bool) (route : geo → Bool) :
    let word := (C.machine.nativeCode leaf base x initial widths ord fit q).val
    WorkWords.Covers ((packHistory leaf C.machine.epoch T).term q).val.rows.flatten.site
      (fun v => let prog := (C.machine.terminalPrivatePrograms (C.privateSiteRows port seeds) number leaf old q v).program
                if extent then prog.size else prog.work)
      (C.nativeWidthColumn p ranges widthBase widths ord fit extent) (Sum.elim (Sum.elim x word) route) := by
  intro word
  apply broadcastColumn_covers widthHist (broadcastOrder (fan S) widths ord T) fit _ _ extent x word route
    (C.machine.nativeCode_readProfile leaf base x initial widths ord fit q)
  exact (C.terminal_widths p port ranges seeds number B widthBase x leaf old small room basePorts baseCap baseRead q).2 extent

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
