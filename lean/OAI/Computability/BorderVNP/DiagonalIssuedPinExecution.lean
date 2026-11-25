import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback
import OAI.Computability.BorderVNP.DiagonalCompletedColumnFiber
import OAI.Computability.BorderVNP.DiagonalBootedPinExecution

/-! # The signed column from the booted machine, issued cells and protected finish -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ChosenReader

open Branch Crossing ResidueBox ResiduePins ResidueIndex TeamContraction ProcessorSlots JointHeader
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine RoutingISA.CellDispatch CellMacro.Generator
open VPVNP.BurstRAM BorderVNP.Cube Physical NativeAssignments Packing.BottomReports Packing.CellAddresses DiagonalTallyCellReports
open scoped Classical BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 4000

variable {F : Type} [Field F] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity F D m}
    {aux : ι → F} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField G aux q k s ord} {chart : AdvisedBranch C} [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult w pin exp : ℕ} (reader : ChosenReader chart (R+1) r mult w w pin)
    {t link inner : ℕ} {Edge : Type} {cn cd cb ch cK cs width reserve cap : ℕ}
    (id : TableEntry cn cb ch cK cs → ℕ)
    (wire : Wiring R r t ((pairedTableParameters (k+1) s+2)*pin) link inner (k+1) Edge)
    (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (limit burst : ℕ) (privateSize : TeamScales.width (k+1) (1/2) ≤ burst)

local notation "I" => Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool
local notation "dim" => pairedTableParameters (k+1) s + Fintype.card (G.Entry ⊕ ι)

variable {P Hist : Type} [Fintype P] [Fintype Hist] {bits : P → ℕ}
    {N : Hist → Network D P bits} {blocks : Hist → ℕ}
    (B : ∀ h,CoreDirectory (N h) cn cd (blocks h) cb ch cK R)
    (port : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Ports bits)
    (observed : ∀ h, Fin (B h).siteRows → ℕ) (original : ∀ h, Fin (B h).cells → List Bundle)
    (shape : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (h : Hist) → (B h).Route cs → Fin (R+1) → ReportLayout)
    (rows : ∀ i h v, ReceivedRows (shape i h v) (B h).cells)
    (owner : ∀ h, (B h).Route cs → Fin (B h).cells → Fin (R+1))
    (owned : ∀ i h v u (a : Fin ((rows i h v).cells u).length), owner h v ((rows i h v).order ⟨u,a⟩)=u)
    (siteOwner : ∀ h x, observed h ((B h).siteID x)=((B h).cell x).val)
    (legal : ∀ h x, ((B h).programs x).birth.Local ∧ ((B h).programs x).program.Schema ∧
      ((B h).programs x).program.RelativeBoxes ∧ ((B h).programs x).program.SignFree)
    {Term : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Hist → Type} [∀ i h, Fintype (Term i h)]
    (decode : ∀ i h, {v : (B h).Route cs × (B h).Bank // (B h).Guard (port i) v} ≃ Term i h)
    (assigned : ∀ i, (Σ h,Term i h) → Tally (Fin (R+1)) (Fin (pairedTableParameters (k+1) s)) (G.Entry ⊕ ι) exp)
    (fields : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (h : Hist) → (B h).Route cs × (B h).Bank →
      PositiveFields reserve cn cd cap (R+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) width)
    (j : Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin (pairedTableParameters (k+1) s)) (chart.pinRadius (R+1) r))

local notation3 (prettyPrint := false) "live" => (boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j
local notation3 (prettyPrint := false) "reported" => CoreDirectory.Proposals B shape rows
local notation3 (prettyPrint := false) "fType" => PreparedFields I Hist (Fin ((R+1)*dim*width) → Bool) (fun h => (B h).Route cs) reported
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock (k+1))

/-- Every value on the left is an execution of the original fixed program on
this live pin and exterior wiring. The inputs on the right of the construction
are the actual reached pre-call directories and protected canonical finishes.
The packet decoder need only invert the guarded source at a single public
history. Complete exterior bijectivity, all private signs and the live reader
image are supplied by the physical execution in this construction. -/
noncomputable def executionOfIssuedCells
    (boot : (x : {z // PositiveExterior wire args live w z}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver wire pub reg args live x.val u)
    (used : ∀ x u,(boot x u).used≤limit) :
    let active := PinStart.preCallSupport (fun z u => (boot z u).start) id
    ∀ next : (x : {ext // PositiveExterior wire args live w ext ∧ active ext}) → (u : Fin (R+1)) →
      let a := boot ⟨x.val,x.property.1⟩ u
      PositiveContinuation id SparseExterior.driver (k+1) (pub u) mac a.start.bank a.memory a.pins a.used limit,
    let S := BootedPinStart.supportedTeam id boot limit burst privateSize next
    ∀ (prep : JointBeforeCells S ≃ fType) (base : fType → Fin (R+1) → ℕ)
      (table : ∀ (f : fType) u, let p := prep.symm f
        OwnerTable (S p.1 u).pub ((S p.1 u).postMemory (p.2 u)) ⟨u.val,base f u,(B f.2.1).cells⟩
          (PositiveTeam.ownerWord (owner f.2.1 f.2.2.1)))
      (issued : ∀ f, CoreDirectory.Issued B port observed original shape rows S prep f),
    let actual := CoreDirectory.preparedRoutedRows B port observed original shape rows S prep owner owned base table issued
    (∀ i h v (ok : (B h).Guard (port i) v), let A := (actual i h v).candidate
      ∃ H : A.Completion (fields i h v), Nonempty (reader.CompletedPacket wire A H i live) ∧
        ∀ c, ∑ u,H.rows u c=∑ u,DiagonalTallyRAM.tallyRow ((assigned i ⟨h,decode i h ⟨v,ok⟩⟩).numberScalars
          (Fintype.equivFin (G.Entry ⊕ ι))) u c) →
    reader.WiredPinExecution id SparseExterior.driver wire args mac pub reg limit burst (fun i => Σ h,Term i h) assigned j := by
  intro active next S prep base table issued actual returned
  let sizes := fun h c => externalBase (N h) (B h).cell c (placedSize (N h) (B h).programs)
  let count := fun h => (B h).cells
  let room := CoreDirectory.issuedWidths B port observed original shape rows S prep owner owned base table issued
  let joined := PreparedOwned.join S prep count owner base table
  let banks := PreparedOwned.bank S prep count owner base table sizes room
  let guarded := fun i h => (B h).Guard (symbols:=cs) (port i)
  have sound := fun i h v => CoreDirectory.preparedRoutedSound B port observed original shape rows S prep
    owner owned base table issued i h v (siteOwner h) (legal h)
  choose H evidence using returned
  apply reader.executionOfBoots id SparseExterior.driver wire pub reg args limit burst privateSize _ assigned j boot next used joined
  exact NativeColumnFiber.ofCompletedPackets reader S joined prep banks actual fields guarded sound H decode assigned wire j
    (fun i h v ok => (evidence i h v ok).1.some) (fun i h v ok => (evidence i h v ok).2)

end Diagonal.ChosenReader

end BorderVNP
end Computability
end OAI
