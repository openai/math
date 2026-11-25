import OAI.Computability.BorderVNP.DiagonalSignedWriterOwnership

/-! # Retaining the actual scanner observation of each selected builder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Physical.NativeAssignments TeamContraction

variable {R w : ℕ} {ar : CubeArena.Layout}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {raw : Symbols ar.header.d → List Bool}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {pub : Fin (R+1) → Arg → Word w}
    {mac : Fin (R+1) → TeamOpcode.Macros w 8} {b : Fin (R+1) → Bank w} {m : Fin (R+1) → Memory w}

/-- The actual all-team scanner runs in the builder's inverse on this routed
assignment, starting at its own installed dictionary. -/
noncomputable def DeliveredBuilder.ownedAt (B : DeliveredBuilder ar owners decl raw id pub mac b m)
    (q : Matching ar owners decl raw) : TeamRows.Returns (Fin (R+1)) ar w :=
  ownedHistory ar pub mac (fun u => (B.constants u).val.2.1) (fun u => (B.constants u).val.2.2) (B.owned.symm q)

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (template : Frame) (count : ℕ)

/-- The selected scanner inverse has the returned delivery, pin substitutions
and observations on the very same hardware banks as the external route replay. -/
def PreparationFrame.ObservedBuilders (B : F.Builders fixed id owners) : Prop :=
  ∀ raw : SharedWords ar decl, let z := F.replay fixed raw
    ∃ (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
        F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
      f.table=F.tab ∧ f.row=F.row ∧ SharedWriters f F.rows (F.source z.1) ∧
      (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) ∧
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
        (F.guess u) (H u).initial) ∧ f.receivedRows F.rows F.group=raw.val ∧
      ∀ q : Matching ar owners decl raw.val, let endRows := (B raw).ownedAt q
        OwnedHandoff f F.rows (F.source z.1) ar decl F.group template id count endRows ∧
          ObservedOwned ar decl F.group endRows owners raw.val q.val

private theorem transport_builder {raw raw' : Symbols ar.header.d → List Bool}
    {p p' : Fin (R+1) → Arg → Word w} {mac₀ mac₁ : Fin (R+1) → TeamOpcode.Macros w 8}
    {b b' : Fin (R+1) → Bank w} {m m' : Fin (R+1) → Memory w} (S : SourceReports ar owners)
    (handoff : TeamRows.Returns (Fin (R+1)) ar w → Prop) (group : Fin ar.header.d → Fin (R+1))
    (words : raw=raw') (pubs : p=p') (macros : mac₀=mac₁) (regs : b=b') (outputs : m=m')
    (B : DeliveredBuilder ar owners decl raw id p mac₀ b m) (agree : B.matchesSource S)
    (attained : ∀ q : Matching ar owners decl raw, handoff (B.ownedAt q) ∧
      ObservedOwned ar decl group (B.ownedAt q) owners raw q.val) :
    ∃ B' : DeliveredBuilder ar owners decl raw' id p' mac₁ b' m', B'.matchesSource S ∧
      ∀ q : Matching ar owners decl raw', handoff (B'.ownedAt q) ∧
        ObservedOwned ar decl group (B'.ownedAt q) owners raw' q.val := by
  subst raw'; subst p'; subst mac₁; subst b'; subst m'
  exact ⟨B,agree,attained⟩

set_option maxHeartbeats 1100000 in
/-- Choose the builder, mathematical row agreement and full observed owned
receipt together at each raw exterior. Reindexing the genuine return to
the replay preserves all three. -/
theorem PreparationFrame.observedBuildersOnReturned (S : SourceReports ar owners)
    (installAt : ∀ raw : SharedWords ar decl, let z := F.replay fixed raw
      ∀ (H : Fin (R+1) → TeamHistory w)
        (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        f.table=F.tab → f.row=F.row → SharedWriters f F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → f.receivedRows F.rows F.group=raw.val →
        ∃ B : DeliveredBuilder ar owners decl (f.receivedRows F.rows F.group) id (fun u => (H u).pub)
          (fun u => (H u).macros) (fun u => (H u).history.val.2.1) (fun u => (H u).history.val.2.2),
          B.matchesSource S ∧ ∀ q : Matching ar owners decl (f.receivedRows F.rows F.group),
            OwnedHandoff f F.rows (F.source z.1) ar decl F.group template id count (B.ownedAt q) ∧
            ObservedOwned ar decl F.group (B.ownedAt q) owners (f.receivedRows F.rows F.group) q.val) :
    ∃ B : F.Builders fixed id owners, F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template count B := by
  classical
  let Candidate (raw : SharedWords ar decl) := DeliveredBuilder ar owners decl raw.val id
    (pub (F.replay fixed raw).1) (mac (F.replay fixed raw).1)
    (fun u => ((F.replay fixed raw).2 u).val.2.1) (fun u => ((F.replay fixed raw).2 u).val.2.2)
  have which (raw : SharedWords ar decl) : ∃ B : Candidate raw, B.matchesSource S ∧
      let z := F.replay fixed raw
      ∃ (H : Fin (R+1) → TeamHistory w)
        (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        f.table=F.tab ∧ f.row=F.row ∧ SharedWriters f F.rows (F.source z.1) ∧
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) ∧
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) ∧ f.receivedRows F.rows F.group=raw.val ∧
        ∀ q : Matching ar owners decl raw.val, OwnedHandoff f F.rows (F.source z.1) ar decl F.group template id count
          (B.ownedAt q) ∧ ObservedOwned ar decl F.group (B.ownedAt q) owners raw.val q.val := by
    obtain ⟨H,f,ft,fr,writer,actual,pinned,read⟩ := F.replayDelivery fixed raw
    let z := F.replay fixed raw
    obtain ⟨B,source,seen⟩ := installAt raw H f ft fr writer actual pinned read
    obtain ⟨B',src,records⟩ := transport_builder id owners S
      (OwnedHandoff f F.rows (F.source z.1) ar decl F.group template id count) F.group read
      (funext fun u => (actual u).1) (funext fun u => (actual u).2.1)
      (funext fun u => congrArg Prod.fst (actual u).2.2) (funext fun u => congrArg Prod.snd (actual u).2.2) B source seen
    exact ⟨B',src,H,f,ft,fr,writer,actual,pinned,read,records⟩
  choose B source records using which
  exact ⟨B,⟨fun raw => (source raw).1,fun raw => (source raw).2⟩,records⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
