import OAI.Computability.NearSquareRoot.InterchangeAtlasVerifier
import OAI.Computability.NearSquareRoot.InterchangeMinorVerifier
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasMask

/-! # Numbering the labels and rectangle keys of a finite template

Relabeling replaces each endpoint and chart by the same geometric incidence
in finite ordinal coordinates. It preserves chart words, incidence counts,
rectangle-matrix coefficients, and the factorization supplied by a minor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.TemplateGeometry

open StageLedger RectangleAtlas

variable {L B : Type} {l t : ℕ} (e : L ≃ Fin l) (k : B ≃ Fin t) (r : B → Rectangle L)

def rect [DecidableEq L] (i : Fin t) : Rectangle (Fin l) where
  sources := Finset.univ.filter fun v => e.symm v ∈ (r (k.symm i)).sources
  destinations := Finset.univ.filter fun v => e.symm v ∈ (r (k.symm i)).destinations

variable [DecidableEq L]

theorem mem_side (s : Bool) (v : Fin l) (i : Fin t) :
    v ∈ (if s then (rect e k r i).destinations else (rect e k r i).sources) ↔
      e.symm v ∈ (if s then (r (k.symm i)).destinations else (r (k.symm i)).sources) := by
  cases s <;> simp [rect]

def incidentEquiv (s : Bool) (v : Fin l) :
    Incident (rect e k r) s v ≃ Incident r s (e.symm v) where
  toFun i := ⟨k.symm i.1, (mem_side e k r s v i.1).mp i.2⟩
  invFun i := ⟨k i.1, (mem_side e k r s v _).mpr (by simpa using i.2)⟩
  left_inv i := Subtype.ext (k.apply_symm_apply _)
  right_inv i := Subtype.ext (k.symm_apply_apply _)

theorem card_incident [Fintype B] (s : Bool) (v : Fin l) :
    Fintype.card (Incident (rect e k r) s v) = Fintype.card (Incident r s (e.symm v)) :=
  Fintype.card_congr (incidentEquiv e k r s v)

theorem card_hamming_incident {p d : ℕ} [Fact p.Prime]
    (e : HammingLabels p d ≃ Fin l) (k : HammingRectangleKey p d (Fact.out : p.Prime).pos ≃ Fin t)
    (s : Bool) (v : Fin l) :
    Fintype.card (Incident (rect e k (nodeRectangles p d)) s v) ≤
      labelIncidence p d (Fact.out : p.Prime).pos := by
  rw [card_incident]
  exact hamming_incident_le p d _ _ _

def endpoint {s : Bool} (u : Endpoint (rect e k r) s) : Endpoint r s :=
  ⟨e.symm u.1, incidentEquiv e k r s u.1 u.2⟩

def chart {m : ℕ} : Chart (rect e k r) m → Chart r m
  | .inl (s,j,v) => Chart.label s j (e.symm v)
  | .inr (.inl (j,i)) => Chart.common j (k.symm i)
  | .inr (.inr (.inl ⟨_,u⟩)) => Chart.prepare (endpoint e k r u)
  | .inr (.inr (.inr (j,⟨_,u⟩))) => Chart.localMap j (endpoint e k r u)

def catalog {a m b : ℕ} (w : AddressROM.Catalog r a m b) : AddressROM.Catalog (rect e k r) a m b :=
  fun c => w (chart e k r c)

private theorem valid_tests [Fintype L] [Fintype B] {a m b : ℕ} (w : AddressROM.Catalog r a m b) :
    AddressROM.valid w = true ↔
    (∀ c, AddressROM.shapeOK w c = true) ∧
      (∀ s j u, AddressROM.edgeOK w s j u = true) ∧ ∀ j v, AddressROM.pivotOK w j v = true :=
  decide_eq_true_iff

theorem valid_catalog [Fintype L] [Fintype B] {a m b : ℕ} (w : AddressROM.Catalog r a m b)
    (hw : AddressROM.valid w = true) : AddressROM.valid (catalog e k r w) = true := by
  obtain ⟨hs,he,hp⟩ := (valid_tests r w).mp hw
  apply (valid_tests (rect e k r) _).mpr
  refine ⟨?_,fun s j u => he s j (endpoint e k r u),fun j v => hp j (e.symm v)⟩
  intro c
  rcases c with ⟨s,j,v⟩ | ⟨j,i⟩ | ⟨s,u⟩ | ⟨j,s,u⟩
  all_goals exact hs (chart e k r _)

theorem rectangleMatrix_apply [Fintype B] {K : Type} [Field K] (v u : Fin l) :
    rectangleMatrix (K:=K) (rect e k r) v u = rectangleMatrix (K:=K) r (e.symm v) (e.symm u) := by
  classical
  simp only [rectangleMatrix, Matrix.of_apply, e.symm.injective.eq_iff]
  congr 1
  apply Fintype.sum_equiv k.symm
  intro i
  simp [rect]

private def ordinal (l t : ℕ) : ((Bool × Fin t) × Fin l) ≃ Fin (2*t*l) :=
  (Equiv.prodCongr ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans finProdFinEquiv)
    (Equiv.refl _)).trans finProdFinEquiv

private theorem ordinal_val (s : Bool) (j : Fin t) (v : Fin l) :
    (ordinal l t ((s,j),v)).val = FlatAtlas.maskIdx l t s j v := by
  change v.val + l * (j.val + t * (finTwoEquiv.symm s).val) = (s.toNat * t + j.val) * l + v.val
  cases s <;> simp [finTwoEquiv] <;> ring

/-- Both orientations of an ordinal rectangle family in the flat mask's
physical order, including an empty label or key space. -/
def maskBits (r : Fin t → Rectangle (Fin l)) : List Bool :=
  List.ofFn fun i : Fin (2*t*l) =>
    let p := (ordinal l t).symm i
    decide (p.2 ∈ if p.1.1 then (r p.1.2).destinations else (r p.1.2).sources)

@[simp] theorem length_maskBits (r : Fin t → Rectangle (Fin l)) :
    (maskBits r).length = 2*t*l := List.length_ofFn

theorem represents_maskBits (r : Fin t → Rectangle (Fin l)) :
    FlatAtlas.Represents (maskBits r) r := by
  intro s j v
  unfold FlatAtlas.mask
  rw [← ordinal_val s j v]
  simp [maskBits, List.getD]

section Minor
variable {K : Type} [Field K] [DecidableEq K] {h : ℕ}

def minor (c : MinorROM.Code L K h) : MinorROM.Code (Fin l) K h :=
  ⟨e ∘ c.row, e ∘ c.col, c.middle⟩

theorem valid_minor [Fintype L] (A : Matrix L L K) (c : MinorROM.Code L K h)
    (hc : MinorROM.valid A c = true) :
    MinorROM.valid (A.submatrix e.symm e.symm) (minor e c) = true := by
  obtain ⟨hi,hj,inv,fac⟩ := (MinorROM.valid_iff _ _).mp hc
  refine (MinorROM.valid_iff _ _).mpr ⟨e.injective.comp hi,e.injective.comp hj,?_,?_⟩
  · simpa [minor, Matrix.submatrix_submatrix, Function.comp_def] using inv
  · ext i j
    simpa [minor, Matrix.mul_apply, Matrix.submatrix_apply] using
      congrFun (congrFun fac (e.symm i)) (e.symm j)

theorem valid_rect_minor [Fintype B] [Fintype L] (c : MinorROM.Code L K h)
    (hc : MinorROM.valid (rectangleMatrix r) c = true) :
    MinorROM.valid (rectangleMatrix (rect e k r)) (minor e c) = true := by
  have eq : rectangleMatrix (K:=K) (rect e k r) =
      (rectangleMatrix r).submatrix e.symm e.symm := by
    ext v u
    exact rectangleMatrix_apply e k r v u
  rw [eq]
  exact valid_minor e _ c hc

end Minor
end Interchange.TemplateGeometry

end NearSquareRoot
end Computability
end OAI
