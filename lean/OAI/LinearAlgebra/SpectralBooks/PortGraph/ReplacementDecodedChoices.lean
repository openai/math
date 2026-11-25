import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoverChoices
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldRoot

/-! # Recovering the chosen old terms from the smaller map

The local root, port, and edge checks on the decorated replacement recover
a passing old map. Its occurrence coordinates assign each advertised term
to the corresponding canonical patch of the old representative.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementTemplate

open ReplacementChoices MapLabels

universe u

variable {N K : ℕ} {ε : ℝ} (C : System N K ε)
  {I : Type} (R : I → Checked N K ε) [Fintype I]
  (P : StubPairing (fun i => (R i).val.shape.Stub))

local notation "records" => (Subtype.val ∘ R)

/-- Data recovered on the old expansion, in the original occurrence coordinates. -/
structure DecodedChoices where
  root : PatchRecord.vertices records
  connected : (PatchRecord.graph records P).ConnectedFrom root
  types : ∀ v, (PatchRecord.asMap records P root connected).typeAt v = (R v.1).val.shape.typeAt v.2
  pass : (tests N K ε).Pass (PatchRecord.asMap records P root connected) (PatchRecord.labels records)
  recovered :
    let M := PatchRecord.asMap records P root connected
    let hm := C.member M _ pass
    C.Recovered R (M.toRep hm.1 hm.2) (M.toRepIso hm.1 hm.2).vertex

namespace DecodedChoices

variable {C R P} (d : DecodedChoices C R P)

/-- The finite representative of the decoded old map. -/
def toRep : MapRep N :=
  let M := PatchRecord.asMap records P d.root d.connected
  let hm := C.member M _ d.pass
  M.toRep hm.1 hm.2

/-- The old representative with the particular term chosen in each smaller tree. -/
def decorated (Term : Checked N K ε → Type u) (t : ∀ i, Term (R i)) : (C.family Term).Rep :=
  ⟨d.toRep, d.recovered.choices Term t⟩

/-- Reading a term on the representative recovers its advertised catalogue entry. -/
theorem decorated_sigma (Term : Checked N K ε → Type u) (t : ∀ i, Term (R i)) (i : I) :
    (⟨C.checked d.toRep (d.recovered.occ i), (d.decorated Term t).2 (d.recovered.occ i)⟩ :
      Σ Q, Term Q) = ⟨R i,t i⟩ :=
  d.recovered.choices_sigma Term t i

end DecodedChoices

section Decoder

variable {V E J : Type} {T : J → ReplacementTemplate.{0,0,0}} {H : PortGraph V E}
  {num : H.FourPortNumbering} {slot : Numbering T} {z : V → Σ j, (T j).Role}
  (tagRecord : J → Checked N K ε) {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
  (hv : ∀ v, VertexTest T num slot z v)
  (he : ∀ e, PairTest (fun j => (tagRecord j).patchId) oldEdge (readEnd hv e false) (readEnd hv e true))
  [Fintype E] [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire] [Fintype (Copies (T := T) z)]
  (chosen : ∀ j, (T j).Role) (r : V)
  (rootCheck : ∀ v, recordMark (fun j => (tagRecord j).val) chosen (z v) ↔ v = r)
  (stub : ∀ j, (T j).Stub ≃ (tagRecord j).val.shape.Stub)
  (directed : ∀ j s, (stub j s).val.side = (T j).direction s)
  (oldCheck : ∀ a b, oldEdge a b → PatchRecord.stubTest (fun j => (tagRecord j).val) (tests N K ε)
    (recordedStub _ stub a) (recordedStub _ stub b))

include rootCheck directed oldCheck in
/-- The accepted smaller map determines an old map and the correspondence
between its canonical records and the advertised records on decoded tree copies. -/
def decodedChoices (conn : H.ConnectedFrom r) :
    DecodedChoices C (fun c : Copies (T := T) z => tagRecord c.1)
      (recordPairing hv he (fun j => (tagRecord j).val) stub) := by
  apply Classical.choice
  let Q := fun c : Copies (T := T) z => tagRecord c.1
  let P := recordPairing hv he (fun j => (tagRecord j).val) stub
  obtain ⟨old,hconn,pass,types⟩ := exists_passing_old_map hv he (fun j => (tagRecord j).val)
    chosen r rootCheck stub conn (tests N K ε) (fun c => (tagRecord c.1).property) directed oldCheck
  have orient (e : P.Wire) (b : Bool) : (P.ends (e,b)).2.val.side = b :=
    (directed _ _).trans (stub_direction hv he e b)
  have boundary (e : P.Wire) : (Q (P.ends (e,false)).1).patchId ≠ (Q (P.ends (e,true)).1).patchId :=
    (stub_tests hv he e).1
  exact ⟨⟨old,hconn,types,pass,C.recoverToRep Q P old hconn orient types pass boundary⟩⟩

end Decoder

end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
