import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceTag
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementSmallIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoveredPairing
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecodedChoices

/-! # The recovered list positions and their forward boundary pairing -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph

namespace ReplacementTemplate.DecodedChoices

open ReplacementChoices
variable {N K : ℕ} {ε : ℝ} {C : System N K ε} (Term : Checked N K ε → Type)
section Expanded
variable {O : Type} [Fintype O] {R : O → Checked N K ε}
  {P : StubPairing (fun j => (R j).val.shape.Stub)} (d : DecodedChoices C R P)

private abbrev originalIso :=
  let M := PatchRecord.asMap (Subtype.val ∘ R) P d.root d.connected
  let hm := C.member M _ d.pass
  M.toRepIso hm.1 hm.2

def cutWires : P.Wire ≃ (C.pairing d.toRep).Wire :=
  d.recovered.exterior P d.root d.connected d.originalIso

theorem cutEnds (e : P.Wire) (b : Bool) :
    Equiv.sigmaCongr d.recovered.occ (fun j => PatchRecord.castStub (congrArg Subtype.val (d.recovered.checked j).symm))
        (P.ends (e,b)) = (C.pairing d.toRep).ends (d.cutWires e,b) :=
  d.recovered.pairing P d.root d.connected d.originalIso e b

end Expanded

abbrev TermTag := Σ Q, Term Q
variable {T : TermTag Term → ReplacementTemplate.{0,0,0}}
  {V E I : Type} [Fintype V] [Fintype E] [DecidableEq V] {H : RootedMap V E}
  {slot : Numbering T} {z : V → RoleLabel T} {patchId : TermTag Term → I}
  {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
  (hv : ∀ v, VertexTest T (actualSlots H) slot z v)
  (he : ∀ e, PairTest patchId oldEdge (readEnd hv e false) (readEnd hv e true))
  [Fintype (Copies (T := T) z)]
  (stub : ∀ j, (T j).Stub ≃ j.1.val.shape.Stub)

private abbrev checkedRecords (c : Copies (T := T) z) := c.1.1
private abbrev rawRecord (a : TermTag Term) := a.1.val
private abbrev oldPair := recordPairing hv he (rawRecord Term) stub

variable (d : DecodedChoices C (checkedRecords (T := T) (z := z)) (oldPair Term hv he stub))

/-- The term decoration recovered at the representative. -/
abbrev savedChoice := (d.decorated Term (fun c => c.1.2)).2

/-- The complete checked record and actual term index at each recovered
occurrence equal the smaller graph's original tag. -/
theorem savedTag (c : Copies (T := T) z) :
    c.1 = (C.choiceTag Term (savedChoice Term hv he stub d)) (d.recovered.occ c) :=
  (d.decorated_sigma Term (fun i => i.1.2) c).symm

/-- Re-index surviving cuts by the actual old representative's wires. -/
def savedExterior : OutsideEdge hv ≃
    (C.choicePairing Term (savedChoice Term hv he stub d) T stub).Wire :=
  d.cutWires

private theorem cast_end {a b : TermTag Term} (h : a = b) (hR : a.1.val = b.1.val)
    (s : (T a).Stub) :
    atTag (fun j => (T j).Stub) h s = (stub b).symm (PatchRecord.castStub hR (stub a s)) := by
  subst b
  exact ((stub a).symm_apply_apply s).symm

/-- The concrete forward pairing on the re-extracted old representative
satisfies the boundary agreement needed for the smaller-map round trip. -/
theorem savedPaired : Paired hv he (C.choiceTag Term (savedChoice Term hv he stub d))
    (C.choicePairing Term (savedChoice Term hv he stub d) T stub) d.recovered.occ
    (savedTag Term hv he stub d) (savedExterior Term hv he stub d) := by
  intro e b
  let a := endsEquiv hv he (e,b)
  let tag := C.choiceTag Term (savedChoice Term hv he stub d)
  let convertEnds := Equiv.sigmaCongrRight (fun j => (stub (tag j)).symm)
  have h := d.cutEnds e b
  refine Eq.trans ?_ (congrArg convertEnds h)
  change (⟨d.recovered.occ a.1,_⟩ : Σ i, (T (tag i)).Stub) = ⟨d.recovered.occ a.1,_⟩
  exact congrArg (Sigma.mk _) (cast_end Term stub (savedTag Term hv he stub d a.1) _ a.2)

end ReplacementTemplate.DecodedChoices
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
