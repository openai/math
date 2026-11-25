import OAI.Computability.BorderVNP.DiagonalCompiledGuardedReadback
import OAI.Computability.BorderVNP.DiagonalSignedPacketView

/-! # Physical subtotals of the original packet decoded by the signed private guard -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "C" => plan.compiled
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins := pins) p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "host" => ((Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2))).symm.toEmbedding.trans
  (enrichedOuterHosts M leaf q).site)
local notation3 (prettyPrint := false) "slabs" => fun j : Fin ((fan S)^T) × (Fin axes → Deck (d+2)) => W.seedSlab position code sites edges ports j.2
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges slabs (fun _ => rfl)

open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells) (gap : ℕ)

local notation3 (prettyPrint := false) "packed" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap q

local notation3 (prettyPrint := false) "atRowSeed(" f ")" => f
  (D:=D) (m:=m) (K:=K) (Gadget:=Gadget) (e:=e) (S:=S) (R:=R) (r:=r) (pins:=pins)
  (link:=link) (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s)
  (copies:=copies) (T:=T) (header:=header) (work:=work) (order:=order) (ns:=ns) (ne:=ne) (np:=np)
  (F:=F) (cells:=cells)

local notation3 (prettyPrint := false) "B" => atRowSeed(signedCoreDirectory) plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "terms" => EnrichedTape.tags p fit W position free count M leaf rfl y hy pos hp.block q

attribute [local instance] signedCoreBatchFinite
attribute [local irreducible] UniversalMachine.programPrefix Nat.clog

open BorderVNP.Cube BorderVNP.ParseTable

local notation3 (prettyPrint := false) "packets" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap
local notation3 (prettyPrint := false) "numbers" => SewnTape.teamNumber (fan S) T copies R count
local notation3 (prettyPrint := false) "widthAt" => atRowSeed(signedCore_widths) plan p fit W position code sites edges ports table
  words good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "recovered" => (B).recoveredRow (N := net) (s := cube.width)
  host slabs (fun _ => copies) widthAt hidden (fun z => terms z)


include y hy in
/-- Physical unary and scalar rows from the untouched bank and route. The
original polynomial's coefficient interpretation and numbering are explicit. -/
noncomputable def signedRawPacketRow {U : ℕ}
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (scalar : Gadget ≃ Fin U)
    (cubePos : TableEntry cube.pred cube.b cube.h cube.copies cube.width → Gadget)
    (bank : Ports (fun _ : FreeBlock R tiles => GridHosts.inputBlockWidth r (k+1) axes d))
    (v : (B).Route cube.width × (B).Bank) : Fin (R+1) → Fin (Branch.parameterCount (2*(k+1)) k s+U) → ℕ :=
  recovered bank cubePos (packed).label numbers (numberedLabelEquiv ord k s) scalar v

/-- The physical owner computes the source row of exactly the term selected by
the guarded interpreter. Both the hidden cable digits and the routed cube words
are read from this return, before summing over the processing teams. -/
theorem signedPinnedPaths_nativeRow {Pin : Type} {U : ℕ}
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (scalar : Gadget ≃ Fin U)
    (cubePos : TableEntry cube.pred cube.b cube.h cube.copies cube.width → Gadget)
    (pin : Pin → Ports (fun _ : FreeBlock R tiles => GridHosts.inputBlockWidth r (k+1) axes d))
    (i : Pin) (v : {u : (B).Route cube.width × (B).Bank // (B).Guard (pin i) u}) :
    let out := atRowSeed(signedPinnedPaths) plan p fit W position code sites edges ports table words good seeds free count y hy pos num
      hp q cube α ξ calibrated lit hd number gap cubePos (pin i) v
    recovered (pin i) cubePos (packed).label numbers (numberedLabelEquiv ord k s) scalar v.val =
      (packed).nativeRow (terms out.1) (pin i) cubePos out.2 numbers (numberedLabelEquiv ord k s) scalar := by
  intro out
  have info := atRowSeed(signedPinnedPaths_reads) plan p fit W position code sites edges ports table words good seeds free
    count y hy pos num hp q cube α ξ calibrated lit hd number gap cubePos (pin i) v
  have fibers := atRowSeed(signedCore_passing) plan p fit W position code sites edges ports table words good seeds free
    count y hy pos num hp q cube α ξ calibrated lit hd number gap out.1 cubePos (pin i)
  have place := atRowSeed(signedCore_packetView) plan p fit W position code sites edges ports table words good seeds free
    count pos num hp q cube α ξ calibrated lit hd number gap
  exact (B).recoveredRow_on_packet host slabs (fun _ => copies) widthAt hidden (fun z => terms z)
    (pin i) cubePos (packed).label numbers (numberedLabelEquiv ord k s) scalar v.val (packed) place
    out.1 out.2 fibers info

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
