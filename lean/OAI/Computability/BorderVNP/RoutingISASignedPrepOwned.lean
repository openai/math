import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedDirectory
import OAI.Computability.BorderVNP.RoutingISASignedPrepJoint

/-! # The owned-group fiber on its actual common row words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment
open TeamContraction TeamRows Padding.Banks
open private owned_native from OAI.Computability.BorderVNP.DiagonalNativeSignedTags

variable {w R : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (decl : LengthDeclaration ar.n ar.header.d) (raw : Symbols ar.header.d → List Bool)
    (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
    (bank : Fin (R+1) → Bank w) (mem : Fin (R+1) → Memory w)

set_option quotPrecheck false in
local notation "Layout" => fun u : Fin (R+1) => ar.scanner (readings (pub u) 0) u.val decl.1.val ar.rowSelectorBits

/-- Actual owned-group histories starting after the cube constants have been installed. -/
abbrev OwnedRuns := ∀ u : Fin (R+1), Evaluator.Returns (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s)
  (pub u) (mac u) (bank u) (mem u)

/-- The joint scan, its physical bank outputs, and each team's original chronological trace. -/
def ownedHistory (z : OwnedRuns ar pub mac bank mem) : TeamRows.Returns (Fin (R+1)) ar w :=
  ⟨pub,mac,bank,mem,fun u => (z u).val.1,fun u => (z u).val.2.1,fun u => (z u).val.2.2,fun u => (z u).property⟩

/-- The two public parts of the encoding of an owned routed cube assignment. -/
abbrev Matching := {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners //
  (Routed.encode owners q).declaration=decl ∧ (Routed.encode owners q).shared=raw}

/-- True operand and arena conditions at the local scan entry, evaluated on
the specific complete assignment whose owned execution is being replayed. -/
def ownedFit (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) : Prop :=
  ∀ u : Fin (R+1), PhysicalSetup (l := Layout u)
    (bankData q.2 ar.header.packetBase ar.singleBank) (Fin.valEmbedding ∘ owners q.1) ar.powerBase ar.vertexBase
    ar.publicBase (ar.header.header+13) (ar.header.header+13+ar.header.entries) decl.2 (pub u) (mem u)

/-- On real physical input words, replay an assignment by its exact dispatcher tape.
The verified native computation constructs all the per-cell and vertex views. -/
theorem replay_owned (q : Matching ar owners decl raw) (ready : ownedFit ar owners decl pub mem q.val) :
    ∃ z : OwnedRuns ar pub mac bank mem, (ownedHistory ar pub mac bank mem z).observed ar decl raw = Routed.encode owners q.val := by
  have run (u : Fin (R+1)) := ownedGroups_physical_run (ready u) (mac u) (bank u)
  choose ev st m path tr _cost _image using run
  let z : OwnedRuns ar pub mac bank mem := fun u => ⟨(ev u,st u,m u),path u⟩
  refine ⟨z,Routed.Words.ext q.property.1.symm q.property.2.symm ?_⟩
  rw [Routed.encode_tapes owners Fin.valEmbedding Layout (fun _ => ar.header.packetBase)
    (fun _ => ar.singleBank) (fun _ => rfl) (fun _ => rfl)]
  funext u
  exact (tr u).2.1

/-- Every genuine owned-family return reads the private callback tapes of its
unique routed assignment. Conversely the installed physical operands run the
actual scanner once for every compatible assignment. -/
noncomputable def ownedEquiv
    (recover : ∀ z : OwnedRuns ar pub mac bank mem, ∃ q, ObservedOwned ar decl (owners q.1)
      (ownedHistory ar pub mac bank mem z) owners raw q)
    (ready : ∀ q : Matching ar owners decl raw, ownedFit ar owners decl pub mem q.val) :
    OwnedRuns ar pub mac bank mem ≃ Matching ar owners decl raw := by
  let F := ownedHistory ar pub mac bank mem
  let chosen (z : OwnedRuns ar pub mac bank mem) := (recover z).choose
  have encoded (z : OwnedRuns ar pub mac bank mem) : Routed.encode owners (chosen z) = (F z).observed ar decl raw :=
    (Routed.realizes_iff owners Fin.valEmbedding ((F z).layout ar Fin.valEmbedding decl)
      (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) (fun _ => rfl) (fun _ => rfl) _ _).mp
      (recover z).choose_spec.observed
  let assign (z : OwnedRuns ar pub mac bank mem) : Matching ar owners decl raw :=
    ⟨chosen z,congrArg Routed.Words.declaration (encoded z),congrArg Routed.Words.shared (encoded z)⟩
  refine Equiv.ofBijective assign ⟨?_,?_⟩
  · intro x y eq
    have e : chosen x = chosen y := congrArg Subtype.val eq
    have obs := (encoded x).symm.trans ((congrArg (Routed.encode owners) e).trans (encoded y))
    funext u
    have tape := congrArg (fun z => z.tapes u) obs
    obtain ⟨he,hr,hm⟩ := DiagonalResidueRAM.unique_returns ((TeamRows.ownedGroups ..).program_tag_native (owned_native ..))
      (x u).property (y u).property (tail := []) (tail' := []) (congrArg (· ++ []) tape)
    exact Subtype.ext (Prod.ext he (Prod.ext hr hm))
  · intro q
    obtain ⟨z,obs⟩ := replay_owned ar owners decl raw pub mac bank mem q (ready q)
    have eq := (encoded z).trans obs
    have inj : Function.Injective (Routed.encode (b := ar.b) (s := ar.s) owners) := by
      intro x y he
      exact (Routed.wordsEquiv owners ar.b ar.s).injective (Subtype.ext he)
    exact ⟨z,Subtype.ext (inj eq)⟩

/-- The native tape, routed row words, physical end banks, real word-level
completion and cost bounds of the assignment selected by the bijection. -/
theorem ownedEquiv_receipt
    (recover : ∀ z : OwnedRuns ar pub mac bank mem, ∃ q, ObservedOwned ar decl (owners q.1)
      (ownedHistory ar pub mac bank mem z) owners raw q)
    (ready : ∀ q : Matching ar owners decl raw, ownedFit ar owners decl pub mem q.val)
    (z : OwnedRuns ar pub mac bank mem) :
    let q := (ownedEquiv ar owners decl raw pub mac bank mem recover ready z).val
    ObservedOwned ar decl (owners q.1) (ownedHistory ar pub mac bank mem z) owners raw q :=
  (recover z).choose_spec

/-- The decoded assignment reproduces the original common rows and each team's
actual private callback tape, including the declared axis and all row totals. -/
theorem ownedEquiv_observed
    (recover : ∀ z : OwnedRuns ar pub mac bank mem, ∃ q, ObservedOwned ar decl (owners q.1)
      (ownedHistory ar pub mac bank mem z) owners raw q)
    (ready : ∀ q : Matching ar owners decl raw, ownedFit ar owners decl pub mem q.val)
    (z : OwnedRuns ar pub mac bank mem) :
    Routed.encode owners (ownedEquiv ar owners decl raw pub mac bank mem recover ready z).val =
      (ownedHistory ar pub mac bank mem z).observed ar decl raw := by
  let F := ownedHistory ar pub mac bank mem z
  change Routed.encode owners (recover z).choose=F.observed ar decl raw
  exact (Routed.realizes_iff owners Fin.valEmbedding (F.layout ar Fin.valEmbedding decl)
    (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) (fun _ => rfl) (fun _ => rfl) _ _).mp
      (recover z).choose_spec.observed

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
