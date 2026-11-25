import OAI.Computability.BorderVNP.DiagonalReplayPhysicalRows
import OAI.Computability.BorderVNP.RoutingISASignedPrepBuilder
import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # Using the physically returned cube and report builder on the same replay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Physical.NativeAssignments Scatter

variable {R w : ℕ} {ar : CubeArena.Layout}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {raw : Symbols ar.header.d → List Bool}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {pub : Fin (R+1) → Arg → Word w}
    {mac : Fin (R+1) → TeamOpcode.Macros w 8} {bank : Fin (R+1) → Bank w} {mem : Fin (R+1) → Memory w}

/-- The routed return's selected host pins and all of its original ordered
report cells, prior to any choices of their private digits. -/
def DeliveredBuilder.matchesSource (B : DeliveredBuilder ar owners decl raw id pub mac bank mem) (S : SourceReports ar owners) : Prop :=
  (∀ q, B.pins q ↔ S.pins q.val) ∧ ∀ (q : Subtype B.pins) u, SameReportCells
    (B.localRows q u).cells (S.cells q.val.val u)

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))

/-- Transfer a signed installed constant/owner/report scan from its original
native delivered words to the replay indices of the public packet. The true
delivery, substituted pins and final hardware banks are supplied here for
every physically admissible array, including the zero-valued ones. -/
noncomputable def PreparationFrame.buildersOnReturned
    (installAt : ∀ raw : SharedWords ar decl, let z := F.replay fixed raw
      ∀ (H : Fin (R+1) → TeamHistory w)
        (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        f.table=F.tab → f.row=F.row → SharedWriters f F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → f.receivedRows F.rows F.group=raw.val →
        Nonempty (DeliveredBuilder ar owners decl (f.receivedRows F.rows F.group) id (fun u => (H u).pub)
          (fun u => (H u).macros) (fun u => (H u).history.val.2.1) (fun u => (H u).history.val.2.2))) :
    F.Builders fixed id owners := by
  intro raw
  apply Classical.choice
  obtain ⟨H,f,ft,fr,writer,actual,pinned,read⟩ := F.replayDelivery fixed raw
  let z := F.replay fixed raw
  obtain ⟨B⟩ := installAt raw H f ft fr writer actual pinned read
  have p : (fun u => (H u).pub)=pub z.1 := funext fun u => (actual u).1
  have op : (fun u => (H u).macros)=mac z.1 := funext fun u => (actual u).2.1
  have reg : (fun u => (H u).history.val.2.1)=fun u => (z.2 u).val.2.1 :=
    funext fun u => congrArg Prod.fst (actual u).2.2
  have word : (fun u => (H u).history.val.2.2)=fun u => (z.2 u).val.2.2 :=
    funext fun u => congrArg Prod.snd (actual u).2.2
  rw [read,p,op,reg,word] at B
  exact ⟨B⟩

/-- Choose the native builders and their agreement simultaneously. This
ensures the canonical host guard and source report inventory used in the
prefix equivalence are exactly those of the very same installed builder. -/
theorem PreparationFrame.sourceBuildersOnReturned (S : SourceReports ar owners)
    (installAt : ∀ raw : SharedWords ar decl, let z := F.replay fixed raw
      ∀ (H : Fin (R+1) → TeamHistory w)
        (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        f.table=F.tab → f.row=F.row → SharedWriters f F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → f.receivedRows F.rows F.group=raw.val →
        ∃ B : DeliveredBuilder ar owners decl (f.receivedRows F.rows F.group) id (fun u => (H u).pub)
          (fun u => (H u).macros) (fun u => (H u).history.val.2.1) (fun u => (H u).history.val.2.2), B.matchesSource S) :
    ∃ B : F.Builders fixed id owners, F.SourceAgreement fixed S B := by
  classical
  have which (raw : SharedWords ar decl) : ∃ B : DeliveredBuilder ar owners decl raw.val id
      (pub (F.replay fixed raw).1) (mac (F.replay fixed raw).1)
      (fun u => ((F.replay fixed raw).2 u).val.2.1) (fun u => ((F.replay fixed raw).2 u).val.2.2),
      B.matchesSource S := by
    obtain ⟨H,f,ft,fr,writer,actual,pinned,read⟩ := F.replayDelivery fixed raw
    let z := F.replay fixed raw
    have packet := installAt raw H f ft fr writer actual pinned read
    have p : (fun u => (H u).pub)=pub z.1 := funext fun u => (actual u).1
    have op : (fun u => (H u).macros)=mac z.1 := funext fun u => (actual u).2.1
    have reg : (fun u => (H u).history.val.2.1)=fun u => (z.2 u).val.2.1 :=
      funext fun u => congrArg Prod.fst (actual u).2.2
    have word : (fun u => (H u).history.val.2.2)=fun u => (z.2 u).val.2.2 :=
      funext fun u => congrArg Prod.snd (actual u).2.2
    rw [read,p,op,reg,word] at packet
    exact packet
  choose B actual using which
  exact ⟨B,fun raw => (actual raw).1,fun raw => (actual raw).2⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
