import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecodedChoices
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoveredIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementEncoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementUniform

/-! # Transporting the decoder along an isomorphism of passing smaller maps

A role and its port number determine the named end at every dart. Hence an
isomorphism of the smaller decorated maps identifies the exterior edges.
The old verifier makes the saved record on each copy unique. Consequently
the named paired stubs match, and gluing the recovered records gives
isomorphic old maps with the same term choices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementTemplate

open ReplacementChoices
universe u
variable {J V E W D : Type} {T : J → ReplacementTemplate.{0,0,0}}
  {G : PortGraph V E} {G' : PortGraph W D} {num : G.FourPortNumbering} {num' : G'.FourPortNumbering}
  {z : V → RoleLabel T} {z' : W → RoleLabel T}

/-- Coordinate change of the numbered smaller graphs carrying their role labels. -/
structure DecoderIso (num : G.FourPortNumbering) (num' : G'.FourPortNumbering)
    (z : V → RoleLabel T) (z' : W → RoleLabel T) where
  vertex : V ≃ W
  edge : E ≃ D
  incidence : ∀ e b, vertex (G.vertex e b) = G'.vertex (edge e) b
  slot : ∀ e b, num _ ⟨(e,b),rfl⟩ = num' _ ⟨(edge e,b),rfl⟩
  role : ∀ v, z v = z' (vertex v)

namespace DecoderIso

def ofIso [Fintype V] [Fintype E] [DecidableEq V] [Fintype W] [Fintype D] [DecidableEq W]
    {H : RootedMap V E} {H' : RootedMap W D} (f : H.Iso H') (same : ∀ v, z v = z' (f.vertex v)) :
    DecoderIso (actualSlots H) (actualSlots H') z z' :=
  ⟨f.vertex,f.edge,f.incidence,fun e b => Fin.ext (f.number e b),same⟩

variable (F : DecoderIso num num' z z') {slots : Numbering T}
  (hv : ∀ v, VertexTest T num slots z v) (hv' : ∀ v, VertexTest T num' slots z' v)

private theorem namedEnd_ext {a b : End T} (h : owner T a = owner T b)
    (hn : endNumber slots a = endNumber slots b) : a = b := by
  have eqnum {w : RoleLabel T} (p : End T) (hp : owner T p = w) :
      slots w ⟨p,hp⟩ = endNumber slots p := by subst w; rfl
  exact congrArg Subtype.val ((slots _).injective ((eqnum a h).trans hn))

theorem readEnd_eq (e : E) (b : Bool) : readEnd hv e b = readEnd hv' (F.edge e) b := by
  apply namedEnd_ext
    ((owner_readEnd hv e b).trans (((F.role _).trans (congrArg z' (F.incidence e b))).trans
      (owner_readEnd hv' _ b).symm))
  exact (number_readEnd hv e b).trans ((F.slot e b).trans (number_readEnd hv' _ b).symm)

def exterior : OutsideEdge hv ≃ OutsideEdge hv' :=
  F.edge.subtypeEquiv (fun e => by simp only [← F.readEnd_eq hv hv' e false])

/-- Root-role vertices give the occurrence equivalence independently of the
particular proofs that the tests pass. -/
def copies : Copies z ≃ Copies z' :=
  Equiv.sigmaCongrRight fun j => F.vertex.subtypeEquiv (fun v => by rw [F.role v])

variable {N K : ℕ} {ε : ℝ} {C : System N K ε} {R : J → Checked N K ε}
  {old : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
  (he : ∀ e, PairTest (fun j => (R j).patchId) old (readEnd hv e false) (readEnd hv e true))
  (he' : ∀ e, PairTest (fun j => (R j).patchId) old (readEnd hv' e false) (readEnd hv' e true))
  [Fintype E] [Fintype D] [Fintype (Copies z)] [Fintype (Copies z')]
  (stub : ∀ j, (T j).Stub ≃ (R j).val.shape.Stub)


/-- On a decoded old map, two occurrences cannot advertise the same tag. -/
private def copyTag (d : DecodedChoices C (fun c : Copies z' => R c.1) (recordPairing hv' he' (Subtype.val ∘ R) stub)) : Copies z' ↪ J :=
  ⟨Sigma.fst, fun {a b} h => d.recovered.occ.injective (C.checked_injective
    (((d.recovered.checked a).trans (congrArg R h)).trans (d.recovered.checked b).symm))⟩

variable (d' : DecodedChoices C (fun c : Copies z' => R c.1) (recordPairing hv' he' (Subtype.val ∘ R) stub))

/-- The boundary matching of the two actual old expansions is carried to the
same paired recorded stubs by the bijection of exterior edges. -/
def reindex : PatchRecord.Reindexing (fun c : Copies z => (R c.1).val)
    (fun c : Copies z' => (R c.1).val) (recordPairing hv he (Subtype.val ∘ R) stub) (recordPairing hv' he' (Subtype.val ∘ R) stub) where
  occ := F.copies
  saved _ := rfl
  wire := F.exterior hv hv'
  ends e b := by
    let tag := copyTag hv' he' stub d'
    apply (Forward.liftTag tag (fun j => (R j).val.shape.Stub)).injective
    let fam (s : Σ j, (T j).Stub) : Σ j, (R j).val.shape.Stub := ⟨s.1,stub s.1 s.2⟩
    have h := (readEnd_stub hv he e b).symm.trans ((F.readEnd_eq hv hv' e.val b).trans
      (readEnd_stub hv' he' (F.exterior hv hv' e) b))
    exact congrArg fam (Sum.inr.inj h)

variable (d : DecodedChoices C (fun c : Copies z => R c.1) (recordPairing hv he (Subtype.val ∘ R) stub))

private local instance (priority := high) {X : Type} {y : X → RoleLabel T} : DecidableEq (Copies y) := Classical.decEq _

def oldIso : d.toRep.map.Iso d'.toRep.map :=
  let q := F.reindex hv hv' he he' stub d'
  let m := PatchRecord.asMap _ _ d.root d.connected
  let m' := PatchRecord.asMap _ _ d'.root d'.connected
  let mem := C.member m _ d.pass
  let mem' := C.member m' _ d'.pass
  ((m.toRepIso mem.1 mem.2).symm.trans (q.iso _ _ _ _ (q.root_of_types _ _ _ _ d.types d'.types))).trans
    (m'.toRepIso mem'.1 mem'.2)

include F in
/-- The reverse construction respects isomorphism of smaller decorated maps,
including changes of presentation to finite integer names. -/
theorem decorated_iso (Term : Checked N K ε → Type u) (t : ∀ j, Term (R j)) :
    (C.family Term).IsIso (d.decorated Term (fun c => t c.1)) (d'.decorated Term (fun c => t c.1)) :=
  d.recovered.isIso_of_terms Term _ (F.oldIso hv hv' he he' stub d' d) _
    (fun c => d'.recovered.occ (F.copies c)) (fun c => d'.decorated_sigma Term (fun k => t k.1) (F.copies c))

end DecoderIso
end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
