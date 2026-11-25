import OAI.Computability.BorderVNP.DiagonalSignedSewnMarkedWords
import OAI.Computability.BorderVNP.PackedSeedCoreChoices
import OAI.Computability.BorderVNP.PackedBottomRetainedBudget

/-! # The original wired seed births retained by the selected sewn report program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.ExternalSew
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter Boundary GridHosts
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r t pins link inner n g d copies T w : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order pos copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) =>
      copies*inputBlockWidth r n (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Good budget 0 (seedState S G d order pos copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    {nc : ℕ} (ids : Fin (tileCount (Fintype.card (Cube D)) d) ↪ Fin nc)
    (number : e.Entry → ℕ)
    (real : Wiring R r t pins link inner n Edge)
    (count : (fan S)^T*copies = R+1)
    (hp : (fieldSewParams real (Fintype.card (Cube D)) d).Valid)
local notation "axes" => Fintype.card (Cube D)
local notation "adm" => Good (S := S) (start := d+1) (P := Fin (tileCount axes d))
  (bits := fun _ => copies*inputBlockWidth r n axes d) (shape := boundary S (d+1)) (w := w) budget
local notation "leaf" => (Subtype.mk (seedState S G d order pos copies table words) good : Admissible adm 0)
local notation "src" => wiredSeedStatePrograms S W pos tag sites edges ports copies table words
local notation "dir" => C.privateSiteRows ids seeds
local notation "lastPorts" => Flat.portRows T (privatePorts S ids T)

variable (placed : (seedState S G d order pos copies table words).pack.layout =
      (wiredGrid real (Fintype.card (Cube D)) d order pos).groupedRepeat
        (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => inputBlockWidth r n (Fintype.card (Cube D)) d) order copies)

open Packing.BottomReports Packing.CellAddresses Diagonal.ExternalSew.RowTrace

variable (q : (packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).Index)
local notation3 (prettyPrint := false) "net" => enrichedSewnLayout real axes d order pos count C.machine leaf placed q
local notation3 (prettyPrint := false) "st" => enrichedSewnPrograms real axes d order pos count C.machine leaf placed lastPorts hp q
  (C.machine.terminalPrivatePrograms dir number leaf src q)
local notation3 (prettyPrint := false) "chan" => (groupedGridRows G axes d order pos copies).edge
local notation3 (prettyPrint := false) "grp" => (Equiv.refl (Fin (tileCount axes d))).toEmbedding
local notation3 (prettyPrint := false) "original" => ((Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2))).symm.toEmbedding.trans
  (enrichedOuterHosts C.machine leaf q).site)
variable {J : Type} (index : J ↪ Fin ((fan S)^T) × (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (cell : ((packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).term q).val.pack.layout.Site → ℕ)
    {ns₁ : ℕ} (siteID : ((packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).term q).val.pack.layout.Site ↪ Fin ns₁)
    (slot base : J → ℕ)
local notation3 (prettyPrint := false) "roster" => index.trans original
local notation3 (prettyPrint := false) "bodies" => fun j =>
  W.seedCoreBundle pos tag sites edges ports (index j).2 (slot j) (base j) copies

/-- Each row in the source roster is the retained actual verifier birth at
its selected sewn host. The supplied offset is its public site-base read
from the very same program bank. -/
theorem signedSewn_retainedBirths
    (address : ∀ j, base j=siteBase net cell (cell (roster j)) siteID (fun v => (st v).program.size) ⟨roster j,rfl⟩) :
    RetainedBirths net cell (fun v => (st v).program) siteID roster bodies := by
  intro j
  let target := st (roster j)
  let tile := (index j).2
  have saved : target.birth = (src tile).birth :=
    C.machine.terminalPrivatePrograms_birth dir number leaf src q (index j).1 tile
  let born := W.seedBorn pos tag sites edges ports chan grp tile copies
  have start : (src tile).birth = born := rfl
  have trueBirth := DeckGrid.WiredWitness.seedCoreBundle_birth (R:=R) (r:=r) (t:=t) (pins:=pins) (link:=link) (inner:=inner)
    (n:=n) (g:=g) (Edge:=Edge) (G:=G) (d:=len) (D:=D) (q:=axes) (depth:=d) (order:=order) (state:=key)
    W pos tag sites edges ports chan grp tile (slot j) (base j) copies
  refine ⟨address j,born,trueBirth,?_⟩
  exact ⟨(saved.trans start) ▸ target.retention⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
