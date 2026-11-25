import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoveredIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceTag
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementEncoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecodedChoices
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoicePartition

/-! # Decoding a forward replacement recovers the chosen old summand

The forward occurrence and exterior-wire bijections identify the re-expanded
old record assembly with the one extracted from the original map. Each
recovered record carries the same term index as its original occurrence.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementChoices.System

open ReplacementTemplate

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) {M : MapRep N}
  (Term : Checked N K ε → Type) (choice : (C.family Term).Label M)
  (T : (Σ R, Term R) → ReplacementTemplate.{0,0,0})
  [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]
  (stub : ∀ j, (T j).Stub ≃ j.1.val.shape.Stub) (slot : ReplacementTemplate.Numbering T)

local notation "tag" => C.choiceTag Term choice
local notation "newPair" => C.choicePairing Term choice T stub
local notation "roles" => Forward.label (T := T) tag
local notation "copies" => Copies (T := T) roles

variable (orient : ∀ (e : (C.choicePairing Term choice T stub).Wire) (b : Bool),
  (T (C.choiceTag Term choice ((C.choicePairing Term choice T stub).ends (e,b)).1)).direction ((C.choicePairing Term choice T stub).ends (e,b)).2 = b)
  (old : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop)
  (old_pass : ∀ e : (C.choicePairing Term choice T stub).Wire,
    old (Forward.liftTag (C.choiceTag Term choice) _ ((C.choicePairing Term choice T stub).ends (e,false))) (Forward.liftTag (C.choiceTag Term choice) _ ((C.choicePairing Term choice T stub).ends (e,true))))

private theorem distinct_choiceTag :
    Function.Injective ((fun j : Σ R, Term R => j.1.patchId) ∘ tag) := by
  intro j k h
  exact Subtype.ext (((C.checked_patchId j).symm.trans h).trans (C.checked_patchId k))

local notation "validV" => Forward.vertexTests tag newPair slot orient
local notation "validE" => Forward.edgeTests tag newPair slot orient (Checked.patchId ∘ Sigma.fst) old
  (distinct_choiceTag C Term choice) old_pass
private abbrev forwardDecodedPair := recordPairing validV validE (fun j => Subtype.val (Sigma.fst j)) stub

local notation "decodedPair" => forwardDecodedPair C Term choice T stub slot orient old old_pass

/-- The actual boundary pairing of the old expansion agrees with that of the
original certified map, including the two conversions through the template stubs. -/
def forwardOldReindex :
    PatchRecord.Reindexing (C.record M) (fun c : copies => c.1.1.val) (C.pairing M) decodedPair where
  occ := Forward.occurrences tag
  saved _ := rfl
  wire := Forward.exterior tag newPair slot orient
  ends e b := by
    let convertEnds := Equiv.sigmaCongrRight (fun c : copies => stub c.1)
    have h := Forward.ends_roundTrip tag newPair slot orient (Checked.patchId ∘ Sigma.fst) old
      (distinct_choiceTag C Term choice) old_pass e b
    refine Eq.trans ?_ (congrArg convertEnds h).symm
    let s := (C.pairing M).ends (e,b)
    change (⟨Forward.occurrences tag s.1,s.2⟩ : Σ c : copies, c.1.1.val.shape.Stub) =
      ⟨Forward.occurrences tag s.1,stub (tag s.1) ((stub (tag s.1)).symm s.2)⟩
    exact congrArg (Sigma.mk (Forward.occurrences (T := T) tag s.1)) ((stub (tag s.1)).apply_symm_apply s.2).symm

variable [Fintype (Copies (T := T) (Forward.label (T := T) (C.choiceTag Term choice)))]

/-- Decoding the forward role assignment gives the original decorated old
map up to rooted numbered isomorphism, with the same term at every occurrence. -/
theorem forward_left_roundTrip
    (d : DecodedChoices C (fun c : copies => c.1.1) decodedPair) :
    (C.family Term).IsIso (d.decorated Term (fun c => c.1.2)) ⟨M,choice⟩ := by
  let : DecidableEq (C.Occ M) := Classical.decEq _
  let : DecidableEq copies := Classical.decEq _
  let a := C.forwardOldReindex Term choice T stub slot orient old old_pass
  let p := C.partition M
  let glue := p.oldIso M.map (C.label M) (C.name M)
  let r := p.root M.map (C.label M) (C.name M)
  let conn := p.connected M.map (C.label M) (C.name M)
  have types (v : PatchRecord.vertices (C.record M)) :
      (PatchRecord.asMap (C.record M) (C.pairing M) r conn).typeAt v = (C.record M v.1).shape.typeAt v.2 :=
    UniformDecorations.typeAt_iso glue v
  let root := a.root_of_types r d.root conn d.connected types d.types
  let assembled := a.iso r d.root conn d.connected root
  let expMap := PatchRecord.asMap (fun c : copies => c.1.1.val) decodedPair d.root d.connected
  let hm := C.member expMap _ d.pass
  let f := ((expMap.toRepIso hm.1 hm.2).symm.trans assembled.symm).trans glue
  apply d.recovered.isIso_of_terms Term (fun c => c.1.2) f choice
    (Forward.occurrences (T := T) tag).symm
  intro c
  obtain ⟨j,rfl⟩ := (Forward.occurrences (T := T) tag).surjective c
  rfl

include orient old_pass in
/-- The same round trip for any presentation of the forward slot numbering
and any witnesses of its local checks. -/
theorem forward_left_roundTrip_of_slots
    (num : (Forward.graph tag newPair).FourPortNumbering)
    (hnum : num = Forward.numbering tag newPair slot)
    (hv : ∀ v, VertexTest T num slot roles v)
    (he : ∀ e, PairTest (Checked.patchId ∘ Sigma.fst) old (readEnd hv e false) (readEnd hv e true))
    (d : DecodedChoices C (fun c : copies => c.1.1)
      (recordPairing hv he (fun j => Subtype.val (Sigma.fst j)) stub)) :
    (C.family Term).IsIso (d.decorated Term (fun c => c.1.2)) ⟨M,choice⟩ := by
  subst num
  exact C.forward_left_roundTrip Term choice T stub slot orient old old_pass d

end PortGraph.ReplacementChoices.System

end

end SpectralBooks
end LinearAlgebra
end OAI
