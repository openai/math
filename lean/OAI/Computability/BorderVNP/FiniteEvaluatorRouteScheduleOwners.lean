import OAI.Computability.BorderVNP.CubeRouteAllDeclarations
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksNative
import OAI.Computability.BorderVNP.FiniteDiagonalCubeMeanOwner

/-! # Advertised group ownership on the finite field network

The native histogram uses the advertised crossing lengths and the actual sparse delivery
columns. At the public cell enumeration the label scan picks the same labels as the mean
packet plan. Consequently the greedy team for each group agrees before the shared payload
has been checked. Vacant rows and deliveries of width zero make no contribution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Crossing Physical MeanChoice LabelIndex

variable {l : Layout} {dir : LabelIndex.Layout} {before : ℕ → ℕ} {ep : Endpoints dir before}
variable {D n : ℕ} {P : Type*} {bits : P → ℕ} {C : Type} [Fintype C] [DecidableEq C]
variable {A : Type*} [Fintype A]

/-- Each native delivery contributes its exact width to the selected coordinate of
its original receiving cell. This includes zero-width rows with relocated dummy endpoints. -/
theorem directory_incoming_eq (N : Network D P bits) (cell : N.Site → C) (recv : A → C) (size : A → ℕ)
    (number : C ≃ Fin dir.cells) {edgeOrd : N.CrossingEdge cell ↪ Fin dir.cableCount}
    {dataOrd : A ↪ Fin dir.deliveryCount} (place : RowPlacement (networkRows N cell recv size)
      (fromTables dir before ep) number (edgeOrd.sumMap dataOrd)) (cells : l.cells=dir.cells)
    (positive : 0 < l.groups) (axis : Fin (n+1)) (s : Fin l.groups) :
    incomingWidth (directoryLabel cells positive ep n) (directoryRecv cells ep)
        (fun j => (deliveryAt dir before j.val).2) axis s =
      incomingWidth (meanPackedLabel N cell recv size ((List.finRange dir.cells).map number.symm) n l.groups positive)
        recv size axis s := by
  symm
  apply Fintype.sum_of_injective dataOrd dataOrd.injective
  · intro j miss
    have zero := place.unused (.inr j) (by
      rintro ⟨e|a,eq⟩
      · contradiction
      · exact miss ⟨a,Sum.inr.inj eq⟩)
    change (deliveryAt dir before j.val).2=0 at zero
    simp [zero]
  · intro a
    have row := place.live (.inr a)
    change rowEquivalent (.delivery ⟨(deliveryAt dir before (dataOrd a).val).1,_⟩ (deliveryAt dir before (dataOrd a).val).2)
      (.delivery (number (recv a)) (size a)) at row
    rcases row with eq | ⟨zs,zt⟩
    · obtain ⟨dst,sz⟩ := Traffic.delivery.inj eq
      have key : finCongr cells (directoryRecv cells ep (dataOrd a)) = number (recv a) :=
        Fin.ext (congrArg Fin.val dst)
      simp only [directoryLabel,key,sz,decoded_tableCodes N cell recv size dir before ep number place]
    · change (deliveryAt dir before (dataOrd a).val).2=0 at zs
      change size a=0 at zt
      simp [zs,zt]

end Cube.GroupWeights

namespace FiniteDiagonal.FieldRawLayout

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.GroupWeights Cube.LabelIndex Cube.Tally
open RoutingISA RoutingISA.LocalRow CubeHeaderInstall TeamContraction TeamContraction.JointHeader
open VPVNP.BurstRAM
open private loads_congr from OAI.Computability.BorderVNP.CubePhysicalGreedyTally

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R header profile cells cables maxRows stride : ℕ)
local notation "ar" => planArena L R header profile cells cables maxRows stride

/-- The native schedule on any in-range advertised declaration uses exactly the greedy
teams of the finite field plan. The placement refers to the original public RAM and the
label/interval run is the one returned by the public scheduling prefix. -/
theorem pinned_declared_team (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell : ℕ)
    (reg : Bank w) (mem : Memory w) (G : List Bool) (claims : List (List Bool)) (pad : ℕ)
    (rawDecl : L.Declaration) {log mid selected}
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg mem log mid selected) :
    let frame := (pub 0).val
    let raw := padded (spelling (G++DeclarationBits.spelling rawDecl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w L.alphabet L.dimension L.blocks L.bitWidth L.copies L.supply
    let ext := jointFields ((ar).extension old) fresh G.length gates outputs width off ell L.alphabet L.dimension L.blocks L.bitWidth L.copies L.supply
    let index := readCode (L.dimension+1) rawDecl.1
    let axis := Fin.ofNat (L.dimension+1) index
    let decl : LengthDeclaration L.dimension L.alphabet := (axis,fun p j => readCode ((ar).header.cap+1) (rawDecl.2 p j))
    let dir := LabelIndex.layout frame (readings mem)
    let input := powerHeaderImage ar f.dst (readings selected)
    BootPins pub f ext raw mem → (ar).header=physical → frame+112 ≤ header → f.dst+raw.length ≤ header →
      ∀ positive : 0 < L.alphabet, 0 < L.blocks → 0 < bankWidth L.dimension L.bitWidth L.copies L.alternatives L.supply →
      (ar).stop < 2^w → ∀ fit : LabelPrefixFits frame w (readings mem), readings mem (frame+11)=cells →
      declarationInRange rawDecl →
      ∀ (number : L.Cell ≃ Fin dir.cells) (edgeOrd : N.CrossingEdge L.cell ↪ Fin dir.cableCount)
        (dataOrd : V.Operand ↪ Fin dir.deliveryCount),
      RowPlacement (networkRows N L.cell V.recv V.dataWidth) (fromTables dir (readings mem) fit.endpoints)
        number (edgeOrd.sumMap dataOrd) →
      L.label = meanPackedLabel N L.cell V.recv V.dataWidth ((List.finRange dir.cells).map number.symm) L.dimension L.alphabet positive →
      (fun g : Fin L.alphabet => TeamNative.owner R ((weightLayout ar frame index).weight input) g.val) =
        declaredTeam ar decl L.label V.recv V.dataWidth R := by
  intro frame raw physical ext index axis decl dir input boot shape low copied positive blocks bank stop fit count
    valid number edgeOrd dataOrd placement labels
  obtain ⟨_,_,out,first,_,_,_,decoded⟩ := labelBoot_pinned pub f ar old fresh gates outputs width off ell
    mac reg mem G claims pad rawDecl boot shape low copied positive blocks bank stop fit
  have same := (first.unique_of_deterministic (by decide) run).2.2
  subst out
  obtain ⟨_,endRegs,endMem,_,_,read⟩ := decoded.complete valid
  have alphabetFit : (ar).alphabet < 2^w := by
    have bound : (ar).alphabet ≤ (ar).alphabet^2 := by
      rw [pow_two]; exact Nat.le_mul_of_pos_right _ (pow_pos positive _)
    obtain ⟨_,_,_,_,host,rec,pair,lim⟩ := (ar).writer_order
    omega
  let wl := weightLayout ar frame axis.val
  have image := groupImage_pinned pub mac f ar old fresh G.length gates outputs width off ell reg mem boot run
    fit stop alphabetFit count positive axis rawDecl (.ofWords endRegs endMem) read
  have weights (g : Fin L.alphabet) :
      wl.weight input g.val=declarationWeight L.blocks L.bitWidth L.alternatives L.copies decl L.label V.recv V.dataWidth g.val := by
    rw [image.weight_eq g]
    simp only [declarationWeight,dite_eq_left g.isLt,Fin.eta]
    apply congrArg (fun k => TeamNative.scaledWeight (incidentWidth L.blocks L.alternatives L.copies decl g) k
      (groupRaw (L.blocks*(L.copies*L.bitWidth)) axis g))
    exact (directory_incoming_eq N L.cell V.recv V.dataWidth number placement (l:=wl) count.symm positive axis g).trans
      (congrArg (fun lab => incomingWidth lab V.recv V.dataWidth axis g) labels.symm)
  have ordinal : axis.val=index := Nat.mod_eq_of_lt valid.1
  rw [← ordinal]
  funext g
  apply congrArg firstMinimum
  exact loads_congr R g.val _ _ (fun j hj => weights ⟨j,hj.trans g.isLt⟩)


open RoutingISA.Evaluator RoutingISA.Transmission

variable {dirLayout : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout}
variable {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin cells} {id : I ↪ ℕ} {sizes : I → ℕ}
local notation "rows" => Packing.Directory.Layout.directory dirLayout pp lp
local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base rows

/-- Run the complete native scheduling and descriptor-writing program at the declared
teams of the field network. Out-of-range candidates have no schedule return, even if
some decoded coordinate is represented by a wrapped machine index. -/
theorem field_schedule (placement : SlottedWriter ar dirLayout pp lp pins pub slotted base cell id sizes)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (G : List Bool) (claims : List (List Bool)) (pad X : ℕ)
    (rawDecl : L.Declaration) :
    let frame := (pub 0).val
    let raw := padded (spelling (G++DeclarationBits.spelling rawDecl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w L.alphabet L.dimension L.blocks L.bitWidth L.copies L.supply
    let ext := jointFields ((ar).extension old) fresh G.length gates outputs width off ell L.alphabet L.dimension L.blocks L.bitWidth L.copies L.supply
    let index := readCode (L.dimension+1) rawDecl.1
    let axis := Fin.ofNat (L.dimension+1) index
    let decl : LengthDeclaration L.dimension L.alphabet := (axis,fun p j => readCode ((ar).header.cap+1) (rawDecl.2 p j))
    let group := declaredTeam ar decl L.label V.recv V.dataWidth R
    let dir := LabelIndex.layout frame (readings initialRAM)
    let wl := weightLayout ar frame index
    let tl := teamLayout ar R
    let ticks := ((labelPrefixCost frame (readings initialRAM)+publicBootCost ar f.dst)+(minimumCost L.dimension+
      (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+
        (TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+directoryTicks ar frame
    BootPins pub f ext raw initialRAM → (ar).header=physical → frame+112 ≤ header → f.dst+raw.length ≤ header →
      ∀ alphabet : 2 ≤ L.alphabet, 0 < L.blocks → 0 < bankWidth L.dimension L.bitWidth L.copies L.alternatives L.supply →
      (ar).stop < 2^w → ∀ fit : LabelPrefixFits frame w (readings initialRAM), readings initialRAM (frame+11)=cells →
      f.teams=R+1 → (old 0).val=X → 1000000 < 2^w → 1000000*X*(R+1) < 2^w →
      controls+10 < header →
      readings initialRAM (frame+92)=controls ∧ readings initialRAM (controls+9)=(ar).cellBank ∧
        readings initialRAM (controls+10)=(ar).cellStride →
      0 < dirLayout.processors → 0 < dirLayout.block → dirLayout.fields ≤ 2 →
      1000000*((ar).stop+3*dirLayout.teams*(dirLayout.processors*dirLayout.literal))+2*(ar).stop < 2^w →
      (rows).length+L.alphabet.choose 2 ≤ maxRows →
      ∀ (number : L.Cell ≃ Fin dir.cells) (edgeOrd : N.CrossingEdge L.cell ↪ Fin dir.cableCount)
        (dataOrd : V.Operand ↪ Fin dir.deliveryCount),
      RowPlacement (networkRows N L.cell V.recv V.dataWidth) (fromTables dir (readings initialRAM) fit.endpoints)
        number (edgeOrd.sumMap dataOrd) →
      L.label = meanPackedLabel N L.cell V.recv V.dataWidth ((List.finRange dir.cells).map number.symm)
        L.dimension L.alphabet (by omega) →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg initialRAM tr mid selected ∧
        traceCost tr ≤ labelPrefixCost frame (readings initialRAM) ∧
        (∀ x < (ar).publicBase, readings selected x=readings initialRAM x) ∧
        let input := powerHeaderImage ar f.dst (readings selected)
        let owner := (ar).receivingOwner frame axis R input
        let pass := declarationInRange rawDecl ∧ declaredMinimum rawDecl ∧ capacities wl tl X input
        TestRun pub mac (.block (beforeWriters L.dimension (selectorWidth L.dimension L.alternatives L.copies))) reg initialRAM
          ticks pass (fun z => WriterSources ar frame controls f.team R decl group (readings pub) input (readings initialRAM) z.mem w) ∧
        PublicSchedule ar dirLayout pp lp owner decl group pins pub mac reg initialRAM
          (ticks+writerTicks (rows).length L.alphabet) pass := by
  intro frame raw physical ext index axis decl group dir wl tl ticks boot shape low copied two blocks bank stop
    fit count team budget million scaled control pointers processors block fields rawRoom rowRoom number edgeOrd dataOrd
    traffic labels
  obtain ⟨tr,mid,selected,run,clock,keep,before,full⟩ := placement.raw_schedule f old fresh gates outputs
    width off ell controls mac reg G claims pad rawDecl R X boot shape low copied two blocks bank stop fit count team rfl
    budget million scaled control pointers processors block fields rawRoom rowRoom
  refine ⟨tr,mid,selected,run,clock,keep,?_⟩
  intro input owner pass
  by_cases valid : declarationInRange rawDecl
  · have same := V.pinned_declared_team R header profile cells cables maxRows stride pub mac f old fresh gates outputs
      width off ell reg initialRAM G claims pad rawDecl run boot shape low copied (by omega) blocks bank stop fit count
      valid number edgeOrd dataOrd traffic labels
    change (fun g : Fin L.alphabet => TeamNative.owner R (wl.weight input) g.val)=group at same
    rw [← same]
    exact ⟨before,full⟩
  · exact ⟨⟨fun h => (valid h.1).elim, fun h => (valid (before.sound h).1.1).elim⟩,
      fun h => (valid h.1).elim, fun h => (valid (full.2 h).1.1).elim⟩

end FiniteDiagonal.FieldRawLayout

namespace FiniteDiagonal.FieldPacketPlan

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Diagonal

/-- The plan used by the actual ascending mean scan satisfies the label identity
in the advertised-team schedule at its original, possibly permuted cell numbers. -/
theorem meanPlan_directory_labels {D m d cells : ℕ} {P : Type} {bits : P → ℕ} {F : Type*} [Field F]
    {C A : Type} [Fintype C] [DecidableEq C] [Fintype A] (N : Network D P bits)
    (cell : N.Site → C) (recv : A → C) (size : A → ℕ) (edgeOrd : N.CrossingEdge cell ≃ Fin m)
    (cs : List C) (unique : cs.Nodup) (cover : cs.toFinset=Finset.univ) (cube : FixedCube F)
    (positive : 0<d) {W : ℝ} {M : ℕ} (budget : PackedLabelBudget N cell recv size W M (d^(cube.pred+1)))
    (number : C ≃ Fin cells) (ascending : (List.finRange cells).map number.symm=cs) :
    (meanPlan N cell recv size edgeOrd cs unique cover cube positive budget).label =
      meanPackedLabel N cell recv size ((List.finRange cells).map number.symm) cube.pred d positive := by
  rw [ascending]
  rfl

end FiniteDiagonal.FieldPacketPlan

end BorderVNP
end Computability
end OAI
