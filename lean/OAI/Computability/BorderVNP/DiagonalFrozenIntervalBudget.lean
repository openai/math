import OAI.Computability.BorderVNP.DiagonalFrozenSuppliedRoom
import OAI.Computability.BorderVNP.DiagonalFrozenSignedScalarNumbers
import OAI.Computability.BorderVNP.DiagonalSignedReceivedScale
import OAI.Computability.BorderVNP.DiagonalCubePublicationRoom

/-! # Physical report interval bounds at the chosen frozen task -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover BorderVNP.Epoch Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs TeamScales
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open ExternalSew EnrichedOuter RoutingISA RoutingISA.SignedTaskArena TeamContraction.ProcessorSlots
open scoped Classical BigOperators BorderVNP.Epoch.Cube

set_option maxHeartbeats 1100000
set_option maxRecDepth 5500

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {e : PaidIdentity F D m}
    {S : SiteSchedule e} (cube : FixedCube K)
    {extra E dlog Q A B j : ℕ} {s : EpochScales S (cube.pred+1) extra}

/-- Quantities consumed by the original report-directory traversal. All
bounds apply to the same word width, exponent and physical cell stride. -/
structure FrozenIntervalBudget (S : SiteSchedule e) (n r d T copies header link w exponent : ℕ)
    (p : SignedTaskArena.Parameters) : Prop where
  batch : 1 ≤ r
  short : GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d ≤ link
  word : 60*logWidth r n ≤ w
  gap : p.privateGap = n^2
  gadgets : 0<p.report.gadgets
  scale :
    let axes := Fintype.card (Cube D)
    let cap := seedBoxCapacity n r axes d (Fintype.card (Direction axes))
    let mass := S.publicProgramFactor^T*initialMass (D:=D) n r d copies header
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    SignedReceivedScale (TeamScales.width n (1/5)) (TeamScales.width n (1/4)) p.report.countWidth
      p.report.gadgets mass (max (tableLimit e) (max 8 cap)) (signedMarkedLimit copies cap coeff mass)
      ((logWidth r n+1)^exponent)
  storage :
    let axes := Fintype.card (Cube D)
    let count := (epochCopies S)^T*GridHosts.tileCount axes d
    let size := seedDescriptionWidth n r axes d (header*logWidth r n)
      (BottomGridBank.bodyBudget (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))
    ∀ {cells : ℕ} (home : Fin count → Fin cells) (c : Fin cells) (g x : ℕ), g≤n^2 →
      x≤TeamScales.width n (1/5) → x+g+(∑ i, if home i=c then size else 0) ≤ 3*(r*n)^2+1

/-- One sufficiently large length pays for the receives of every returned
team and every source selected later. The published task uses the actual
cube-scalar numbering, reserved gap, gadget count and native word.
The sewn-record bound is available on the same threshold and supplies
the scalar premise of `storage` on every attained cell. -/
theorem JointSchedule.eventually_frozen_interval_budget (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (header : ℕ) (large : E+2 ≤ dlog) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let T := epochs s.τ n
      let copies := TeamScales.width n s.α
      let w := b.physical.word n
      let link := b.physical.link n
      (∀ work (plan : SeedPlan S n r d T copies header work)
        (count : (fan S)^T*copies=b.physical.teamsPred n+1), plan.SewnCellLoads count link) ∧
        ∀ l size (initial : StartupArena) (dir : Packing.Directory.Layout)
          (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories),
          let task := b.frozenSignedTask cube n l size header initial dir profile ceiling outputs field dirs
          FrozenIntervalBudget S n r d T copies header link w (E+2) task.p ∧
            (∀ z : e.Entry, cube.scalarNumber e (.inl z) ≤ task.p.report.gadgets-1) ∧
            (∀ z : BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width,
              cube.cubeID e z ≤ task.p.report.gadgets-1) := by
  let g := Fintype.card (e.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
  filter_upwards [b.eventually_signed_received_scale header g large,b.eventually_frozen_supplied_directory header,
    b.eventually_signed_grid,b.eventually_signedSewnCellLoads header,b.eventually_directory_word,eventually_ge_atTop (2^60)]
    with n scale bank grid loads wide hn
  intro r d T copies w link
  constructor
  · intro work plan count
    exact (loads work plan).choose_spec
  intro l size initial dir profile ceiling outputs field dirs task
  have numbers := b.frozenSignedTask_scalarNumbers e cube n l size header initial dir profile ceiling outputs field dirs
  have hr : 1≤r := stretch_one ..
  have logLo : 60 ≤ logWidth r n := by
    rw [Shortening.PublicCapacity.public_logWidth,← Nat.clog_pow 2 60 (by decide)]
    exact Nat.clog_mono_right _ (hn.trans ((show n ≤ 2*n by omega).trans (Nat.le_mul_of_pos_right _ hr)))
  have word : 60*logWidth r n ≤ w := by
    apply le_trans _ wide.2
    rw [pow_two]
    exact Nat.mul_le_mul_right _ logLo
  refine ⟨⟨hr,grid.2.2,word,rfl,numbers.2.1,scale,?_⟩,numbers.2.2.1,numbers.2.2.2.1⟩
  intro axes count bytes cells home c gap x hg hx
  have rows : (∑ i : Fin count, if home i=c then bytes else 0) ≤ count*bytes := by
    calc
      _ ≤ ∑ _ : Fin count, bytes := Finset.sum_le_sum fun i _ => by split <;> simp
      _ = _ := by simp
  exact (Nat.add_le_add_left rows _).trans (bank gap x hg hx)

end Diagonal

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Branch Crossing Cover Shortening Shortening.Adaptive Packing PhysicalEpochs Packing.DeckGrid
open Diagonal Diagonal.CellEntries Diagonal.ExternalSew GridHosts TeamContraction TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP BorderVNP.Epoch BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 6500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r k pins link a regs w ec width s copies T d header Q : ℕ} (plan : SeedPlan S (k+1) r d T copies header Q)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
local notation "budget" => boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)
local notation "word₀" => 60*logWidth r (k+1)
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies=R+1)
local notation "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S:=S) (start:=d+1) (P:=Fin tiles)
  (bits:=fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape:=boundaryShape S (d+1)) (w:=word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words)
  good : Admissible goodState 0)

variable {c : ℕ} (loads : plan.SewnCellLoads count link)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin c)
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins:=pins) p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "state" => ((packHistory (Pack:=Admissible goodState) (K:=fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((state).route.origin v))

include W code siteID edgeID portID loads in
/-- Each numbered cell of the attained signed network reads at most the
supplied-word allowance. The bound holds for every accepted public word
spelling of the seed before the report scanner reads private choices. -/
theorem supplied_width_on_source_words (v : Fin c) :
    Packing.CellAddresses.suppliedSize net cell v ≤ TeamScales.width (k+1) (1/5) := by
  let tile (z : (net).Site) := reduceMove (depth S (d+1) T) ((state).route.origin z)
  have test : (fun z : (net).Site => cell z=v) = (fun z => tile z=number.symm v) :=
    funext fun _ => propext number.eq_symm_apply.symm
  have measured := (loads G₀ order position W code siteID edgeID portID table words good q (number.symm v)).2
  have supplied (prior payload : (net).Site → ℕ) :
      Packing.CellAddresses.suppliedSize net cell v ≤ localRecords net true prior payload (fun z => tile z=number.symm v) := by
    rw [←test]
    exact (Nat.le_add_left ..).trans (Packing.CellAddresses.wireCapacity_le net cell v prior payload)
  exact (supplied _ _).trans measured

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
