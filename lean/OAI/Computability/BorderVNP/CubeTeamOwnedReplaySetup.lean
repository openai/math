import OAI.Computability.BorderVNP.CubeTeamOwnedArenaSetup
import OAI.Computability.BorderVNP.CubeScatterTransmissionRoutedDispatch
import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalRun
import OAI.Computability.BorderVNP.CubeISAOwnedStrictSideInverse
import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay

/-! # Instantiating the owned bytecode from its decoded common inputs

The private fiber can vary freely. The scalar layout and every shared word
read by the traversal depend only on the recovered declaration, the true
scheduler, and the two actual directed receiver buffers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows
open TeamRowSources Scatter Assignment Padding.Banks Tally

/-- Literal received lists, before splitting them into selector and crossing parts. -/
def Layout.RawViews (ar : Layout) {w : ℕ} (frame team axis : ℕ) (owner : Fin ar.header.d → ℕ)
    (raw : Symbols ar.header.d → List Bool) (m : Memory w) : Prop :=
  let l := ar.scanner frame team axis ar.rowSelectorBits
  ∀ (p : Symbols ar.header.d) (high : Bool), owner (oriented p high).1 = team →
    Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m (l.view (key (oriented p high))) (raw p)

/-- Numeric resource bounds of the concrete post-geometry arena. -/
structure Layout.ReplayRoom (ar : Layout) (w frame : ℕ) : Prop where
  axes : ar.header.a = ar.n+1
  alphabet : 0 < ar.header.d
  payload : 0 < ar.header.blocks*(ar.h*ar.b)
  positive : 0 < bankWidth ar.n ar.b ar.h ar.K ar.s
  primary : frame+112 ≤ ar.header.header
  stopFit : ar.stop < 2^w
  fixedFit : LocalRow.templateLimit ar.n ar.b ar.h ar.K ar.s < 2^w
  capFit : declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s < 2^w

variable {Team : Type*}
variable (ar : Layout)
variable (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Team)

/-- The actual shared emission of a routed assignment is the selector prefix and
the physical crossing words of its native packet and singleton data. -/
theorem shared_bankData (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) (p : Symbols ar.header.d) :
    let A := bankData q.2 ar.header.packetBase ar.singleBank
    sharedWords (Routed.trueDeclaration ar.b ar.s q.1) (Routed.physicalShared owners q) p =
      commonSelectors A.select A.axis p ++ commonCrossings ar.b A.axis p A.select A.supply (fun z => A.value z.1.val z.2) := by
  intro A
  have singles : (fun z : SingleSlot ar.n ar.header.d ar.header.blocks (ar.h*ar.b) => A.value z.1.val z.2) =
      (fun z => lookup q.2 (.inl z)) := by
    funext z
    exact SingleRowData.extendSlots_apply (fun v => lookup q.2 (.inl v)) z
  rw [singles,commonCrossings_eq_keys]
  rfl

/-- The receiver's original raw buffers, not a presumed private execution, suffice
to initialize the real roles for any assignment with that common emission. -/
theorem Layout.replaySetup {w : ℕ} (code : Team ↪ ℕ) (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners)
    (u : Team) (pub : Arg → Word w) (m : Memory w) (decl : LengthDeclaration ar.n ar.header.d)
    (raw : Symbols ar.header.d → List Bool)
    (shape : Routed.trueDeclaration ar.b ar.s q.1 = decl)
    (emits : sharedWords (Routed.trueDeclaration ar.b ar.s q.1) (Routed.physicalShared owners q) = raw)
    (room : ar.ReplayRoom w (readings pub 0))
    (words : ar.ScannerWords (readings pub 0) (code u) decl.1.val (code ∘ owners q.1) (readings pub) (readings m) decl.2)
    (received : ar.RawViews (readings pub 0) (code u) decl.1.val (code ∘ owners q.1) raw m) :
    let l := ar.scanner (readings pub 0) (code u) decl.1.val ar.rowSelectorBits
    let A := bankData q.2 ar.header.packetBase ar.singleBank
    PhysicalSetup (l := l) A (code ∘ owners q.1) ar.powerBase ar.vertexBase ar.publicBase
      (ar.header.header+13) (ar.header.header+13+ar.header.entries) decl.2 pub m := by
  subst decl
  intro l A
  apply ar.physicalSetup_of_words (readings pub 0) (code u) A (code ∘ owners q.1) pub m
    rfl rfl rfl room.axes room.alphabet room.payload room.positive room.primary room.stopFit room.fixedFit room.capFit words
  intro p high own
  let addr := l.view (key (oriented p high))
  let sel := commonSelectors A.select A.axis p
  let cut := commonCrossings ar.b A.axis p A.select A.supply (fun z => A.value z.1.val z.2)
  have read : Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m addr (sel++cut) := by
    have spell : raw p = sel++cut := (congrFun emits p).symm.trans (shared_bankData ar owners q p)
    exact spell ▸ received p high own
  change Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m addr sel ∧
    Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m (addr+sel.length) cut
  exact ⟨by simpa only [List.length_nil,Nat.add_zero] using Resident.slice [] sel cut (by simpa only [List.nil_append] using read),
    Resident.slice sel cut [] (by simpa only [List.append_nil] using read)⟩

end RoutingISA.CubeArena

namespace Cube.TeamRows

open RoutingISA

/-- Every fetched instruction of a complete owned-group stage is native, including
the positive binary choices. Thus a common extension of two finite tapes forces
identical full runs from the same entry state. -/
theorem ownedGroups_native (n b h K s : ℕ) : ∀ pc, (ownedGroups n b h K s).program.tag pc = .native := by
  apply Code.program_tag_native
  have st := (LocalRow.strictChecked n b h K s).nativeOnly_of_unsigned (LocalRow.strictChecked_unsigned ..)
  have dt := (LocalRow.diagonalChecked n b h K s).nativeOnly_of_unsigned (LocalRow.diagonalChecked_unsigned ..)
  simp only [ownedGroups,scan,body,select,strictRole,diagonalRole,OwnedStages.diagonalSide,Code.block,Code.nativeOnly,
    OwnedStages.strictSide_nativeOnly,OwnedStages.singleStage_nativeOnly,st,dt,Bool.and_self]
  rfl

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
