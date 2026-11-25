import OAI.Computability.BorderVNP.DiagonalObservedFrameBuilders

/-! # Signed report builders on the selected physical preparation frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyPacketEmit
open FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (task : SignedTaskArena.Layout)
    {decl : LengthDeclaration task.cube.n task.cube.header.d} (fixed : Block (R+1))
    {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    (F : PreparationFrame G L task.cube decl header pin pub mac reg mem)
    {Cell Data : Type*} [Fintype Data] (label : Cell → Label (task.cube.n+1) task.cube.header.d)
    (recv : Data → Cell) (amount : Data → ℕ) (template : Frame) (frame dataCount : ℕ)

local notation "ar" => task.cube
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv amount
local notation "total" => dataCount+task.cube.header.d.choose 2

/-- Physical controls and reports on every owned scan reached from the selected
frame. No return of the later cell evaluator appears among its inputs. -/
abbrev PreparationFrame.AfterOwned (S : SourceReports ar own) : Prop :=
  ∀ raw : SharedWords ar decl, let z := F.replay fixed raw
      ∀ (H : Fin (R+1) → TeamHistory w)
        (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        f.table=F.tab → f.row=F.row → SharedWriters f F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → f.receivedRows F.rows F.group=raw.val →
        ∀ (q : Matching ar own decl (f.receivedRows F.rows F.group)) (endRows : TeamRows.Returns (Fin (R+1)) ar w),
          OwnedHandoff f F.rows (F.source z.1) ar decl F.group template task.id total endRows →
          ObservedOwned ar decl F.group endRows own (f.receivedRows F.rows F.group) q.val →
          ∃ program : Fin (R+1) → OpenSuffix.Inputs,
            OpenSuffix.ControlFamily program endRows.pub endRows.macros endRows.finalRegs endRows.output (S.pins q.val) ∧
            (S.pins q.val → ∀ u, ∃ v : LocalReportData (endRows.pub u) (endRows.macros u) (endRows.finalRegs u)
              (endRows.output u), SameReportCells v.cells (S.cells q.val u))

set_option maxHeartbeats 1400000 in
/-- The returned writers on every physical exterior determine their own signed
dictionary, owner scans and row choices. Only the four reached controls, the
local report setup and its actual sparse argument continuation are needed
after observing the owned scans. -/
theorem PreparationFrame.signedReportBuilders (S : SourceReports ar own)
    (rows : F.rows=(ar).sharedRows frame decl.1.val dataCount)
    (table : F.tab=(ar).table frame total) (common : ∀ x u,readings (pub x u) 0=frame)
    (space : task.after.packed≤2^w) (values : CubeConstants.valueBound task.id<2^w)
    (room : (ar).ReplayRoom w frame)
    (words : ∀ x u, SharedCubeWords task decl F.group u.val (readings (pub x u)) (F.source x u) dataCount)
    (scheduled : F.group=declaredTeam ar decl label recv amount R)
    (least : decl.1=firstMinimum (fun j => ∑ pair,decl.2 pair j)) (copies : 1≤(ar).K)
    (afterOwned : F.AfterOwned task fixed label recv amount template dataCount S) :
    ∃ B : F.Builders fixed task.id own, F.SourceAgreement fixed S B ∧
      F.ObservedBuilders fixed task.id own template total B := by
  apply F.observedBuildersOnReturned fixed task.id own template total S
  intro raw z H f ht hr writer actual pins received
  have commonAt (u : Fin (R+1)) : readings (H u).pub 0=frame := (actual u).1 ▸ common z.1 u
  have wordsAt (u : Fin (R+1)) : SharedCubeWords task decl F.group u.val (readings (H u).pub) (F.source z.1 u) dataCount :=
    (actual u).1 ▸ words z.1 u
  have continuation := afterOwned raw H f ht hr writer actual pins received
  rw [rows] at writer continuation ⊢
  exact writer.signedReportBuilder task decl label recv amount F.group template frame dataCount S commonAt
    (ht.trans table) space values (fun u => (commonAt u).symm ▸ room) wordsAt scheduled least copies continuation

end TeamContraction

end BorderVNP
end Computability
end OAI
