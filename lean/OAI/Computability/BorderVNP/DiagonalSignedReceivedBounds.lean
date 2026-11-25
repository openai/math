import OAI.Computability.BorderVNP.DiagonalSignedSewnSourceNumbers
import OAI.Computability.BorderVNP.DiagonalSignedSewnGuards
import OAI.Computability.BorderVNP.DiagonalSignedReceivedScale
import OAI.Computability.BorderVNP.DiagonalReceivedReportExtent

/-! # The true fixed signed compiler at each physically received report row -/

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

open InheritedBank

open BottomReports DiagonalTallyCellReports CellSparse BorderVNP.Cube.Physical.NativeAssignments

set_option maxHeartbeats 3200000 in
/-- On a genuine selected public history the complete private compiler supplies
all the local load, scalar, table, guard and range obligations of each physical
report. The inputs identify just its actual packet layout and original bundle
inventory. None depend on the report bits or on an acceptance assumption. -/
theorem signedSewn_receivedBounds (hm : 0 < m) (dB : ℕ)
    (q : (packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).Index)
    {cells teams : ℕ} (code : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)
    (short : inputBlockWidth r n axes d ≤ link) {M ext width gadgets limit : ℕ}
    (gp : 0 < gadgets) (fits : ∀ z, number z ≤ gadgets-1) {J : Type} [Fintype J]
    {lay : Fin teams → ReportLayout} (Rcv : ReceivedRows lay cells)
    (bundle : J → Bundle) (origins : Fin cells → List J) :
    let degree := Fintype.card (Direction axes)
    let K₀ := seedBoxCapacity n r axes d degree
    let mass := baseMass degree K₀ (seedChannelWidth n r axes d) copies dB
    let length := S.publicProgramFactor^T*mass
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    let Z := signedMarkedLimit copies K₀ coeff length
    let st := ((packHistory leaf C.machine.epoch T).term q).val
    let cell := fun v => code (reduceMove (depth S (d+1) T) (st.route.origin v))
    let N := enrichedSewnLayout real axes d order pos count C.machine leaf placed q
    let pr := enrichedSewnPrograms real axes d order pos count C.machine leaf placed lastPorts hp q
      (C.machine.terminalPrivatePrograms dir number leaf src q)
    SignedReceivedScale M ext width gadgets length (max (tableLimit e) (max 8 K₀)) Z limit →
    ∀ {slots : ℕ} (site : N.Site ↪ Fin slots) (owner : Fin slots → ℕ) (host : J ↪ N.Site),
    (∀ v, owner (site v)=(cell v).val) →
    (∀ t, (lay t).gadgets=gadgets ∧ (lay t).countWidth=width) →
    RetainedBirths N (fun v => (cell v).val) (fun v => (pr v).program) site host bundle →
    (∀ c,(origins c).Nodup) → (∀ c j,j ∈ origins c → (cell (host j)).val=c.val) →
    (∀ c j, j ∈ origins c → 0<(bundle j).header.copies ∧ 0<(bundle j).header.stride) →
    (∀ u i,(((Rcv.cells u).get i).bundles.map ReportBundle.useCount).sum=
      (((origins (Rcv.order ⟨u,i⟩)).map bundle).map Bundle.useBits).sum) →
      ReceivedBounds Rcv N cell site owner pr host bundle origins M ext Z (gadgets-1) (tableLimit e) (16*(e.count+1)) limit := by
  intro degree K₀ mass length coeff Z st cell N pr scale slots site owner host owned layout retained unique belongs copiesPos uses
  have numeric := signedSewn_sourceNumbers W pos tag sites edges ports table C words good seeds ids number real count hp placed
    hm dB q code short
  have structural := signedSewn_wellFormed W pos tag sites edges ports table C words good seeds ids number real count hp placed q
  have compiler := signedSewn_compilerFields W pos tag sites edges ports table C words good seeds ids number real count hp placed
    (gadgets-1) fits q
  have charge (c : Fin cells) (ex : Bool) :
      localRecords N ex pr.fullFields.prior pr.fullFields.payload (fun v => (cell v).val=c.val) ≤ M := by
    simpa only [Fin.val_inj] using (numeric.1 c ex).trans scale.program
  refine ⟨owned,fun v => (pr v).size,fun v => (structural v).2.1,
    fun v => (pr v).retention.locality (structural v).1,fun v => (structural v).2.2.1,fun v => (structural v).2.2.2,
    fun c => charge c false,fun c => charge c true,fun t => (layout t).1 ▸ scale.gadgetsFit,
    fun t => (layout t).2 ▸ scale.wordFit.trans (Nat.le_succ _),fun t => (layout t).2 ▸ scale.digits,
    fun t => (layout t).2 ▸ scale.digitFit,?_,numeric.2,fun v => (compiler v).1.2.1,
    fun v => (compiler v).1.2.2,?_,?_,retained,unique,belongs,copiesPos,uses⟩
  · intro t; rw [(layout t).1,(layout t).2]; exact scale.space
  · intro v fs hf f h
    obtain ⟨low,high⟩ := (compiler v).2 fs hf f h
    exact ⟨low.mono scale.relative,high⟩
  · intro t i v _ fs hf f h
    rw [(layout t).1]
    exact ((compiler v).2 fs hf f h).2.range gp

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
