import OAI.Computability.NearSquareRoot.InterchangeROMStageTableCorrect
import OAI.Computability.NearSquareRoot.InterchangeROMStageTableMatrix
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyIndex

/-! # Source-row coverage of the five rectangle tables

Every emitted coefficient has an input register in the typed bank of its gate.
The lane also lies in the ground field's fixed lane range. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable

open Interchange StageLedger

/-- All source terms have preimages among the encoded rows and lanes. -/
def Covers {A : Type} (src : A → Role) (lanes : ℕ) (ts : List Term) : Prop :=
  ∀ t ∈ ts, ∃ a : A × Fin lanes, (src a.1, a.2.val) = t.1

namespace Covers

variable {A : Type} {src : A → Role} {n : ℕ}

theorem nil : Covers src n [] := by simp [Covers]

theorem single (a : A) (d : Fin n) (c : ℕ) : Covers src n [term (src a) d c] := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  exact ⟨(a,d),rfl⟩

theorem cons (a : A) (d : Fin n) (c : ℕ) {ts : List Term} (h : Covers src n ts) :
    Covers src n (term (src a) d c :: ts) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨(a,d),rfl⟩
  · exact h t ht

theorem append {ts us} (h : Covers src n ts) (k : Covers src n us) : Covers src n (ts ++ us) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (h t) (k t)

theorem across {v : ℕ} {f : ℕ → List Term} (h : ∀ i : Fin v, Covers src n (f i)) :
    Covers src n (InterchangeROMStageTable.across v f) := by
  intro t ht
  obtain ⟨i,hi,ht⟩ := List.mem_flatMap.mp ht
  exact h ⟨i,List.mem_range.mp hi⟩ t ht

end Covers

variable {g : Data} {r : B g → Rectangle (L g)} {I J : H g → L g}

/-- The partial sum reads each occupied source of its rectangle. -/
theorem partial_covered (ok : FrameOK g r I J) (o : L g ⊕ (Q g × B g)) (d : D g) :
    Covers (Sum.elim (native (g:=g)) (qeRole (r:=r) (side:=false))) g.lanes
      (partials g (Sum.elim native rRole o) d) := by
  let src := (Sum.elim (native (g:=g)) (qeRole (r:=r) (side:=false)))
  change Covers src _ _
  rcases o with v | ⟨j,b⟩
  · exact Covers.single (src:=src) (.inl v) d 1
  · apply Covers.across
    intro v
    change Covers src _ (if g.src b v then _ else [])
    simp only [ok.src,decide_eq_true_eq]
    split
    next h => exact Covers.single (src:=src) (.inr (j,⟨v,b,h⟩)) d 1
    next => exact Covers.nil

/-- The inverse minor reads the singleton and each occupied destination rank term. -/
theorem mix_covered (ok : FrameOK g r I J)
    (o : (L g ⊕ (Q g × B g)) ⊕ (Q g × H g)) (d : D g) :
    Covers (Sum.elim (Sum.elim (native (g:=g)) (rRole (g:=g))) (tRole (r:=r) (s:=I) (side:=true))) g.lanes
      (mix g (Sum.elim (Sum.elim native rRole) mRole o) d) := by
  let src := (Sum.elim (Sum.elim (native (g:=g)) (rRole (g:=g))) (tRole (r:=r) (s:=I) (side:=true)))
  change Covers src _ _
  rcases o with (v | ⟨j,b⟩) | ⟨j,i⟩
  · exact Covers.single (src:=src) (.inl (.inl v)) d 1
  · exact Covers.single (src:=src) (.inl (.inr (j,b))) d 1
  · apply Covers.across
    intro k
    apply Covers.cons (src:=src) (.inr (j,⟨k,none⟩)) d
    apply Covers.across
    intro b
    simp only [ok.row,ok.dst,decide_eq_true_eq]
    split
    next h => exact Covers.single (src:=src) (.inr (j,⟨k,some ⟨b,h⟩⟩)) d _
    next => exact Covers.nil

/-- Scatter reads one retained rectangle and a source-incident rank term. -/
theorem scatter_covered (ok : FrameOK g r I J)
    (o : (L g ⊕ (Q g × L g)) ⊕ (Q g × B g)) (d : D g) :
    Covers (Sum.elim (Sum.elim (native (g:=g)) (rRole (g:=g))) (tRole (r:=r) (s:=J) (side:=false))) g.lanes
      (scatter g (Sum.elim (Sum.elim native lRole) rRole o) d) := by
  let src := (Sum.elim (Sum.elim (native (g:=g)) (rRole (g:=g))) (tRole (r:=r) (s:=J) (side:=false)))
  change Covers src _ _
  rcases o with (v | ⟨j,v⟩) | ⟨j,b⟩
  · exact Covers.single (src:=src) (.inl (.inl v)) d 1
  · apply Covers.across
    intro k
    split
    next => exact Covers.single (src:=src) (.inr (j,⟨k,none⟩)) d 1
    next => exact Covers.nil
  · apply Covers.cons (src:=src) (.inl (.inr (j,b))) d
    apply Covers.across
    intro k
    change Covers src _ (if g.src b (g.col k) then _ else [])
    simp only [ok.col,ok.src,decide_eq_true_eq]
    split
    next h => exact Covers.single (src:=src) (.inr (j,⟨k,some ⟨b,h⟩⟩)) d 1
    next => exact Covers.nil

/-- Each packed lane of each restored query is present in the collection bank. -/
theorem collect_covered (o : L g ⊕ Endpoint r true) (d : D g) :
    Covers (Sum.elim (Sum.elim (native (g:=g)) (lRole (g:=g))) (qeRole (r:=r) (side:=true))) g.lanes
      (collect g (Sum.elim native eRole o) d) := by
  let src := (Sum.elim (Sum.elim (native (g:=g)) (lRole (g:=g))) (qeRole (r:=r) (side:=true)))
  change Covers src _ _
  rcases o with v | ⟨v,b⟩
  · change Covers src _ (_ ++ _)
    apply Covers.append
    · apply Covers.across
      intro k
      exact Covers.single (src:=src) (.inl (.inl v)) k _
    · apply Covers.across
      intro j
      apply Covers.across
      intro k
      exact Covers.single (src:=src) (.inl (.inr (j,v))) k _
  · apply Covers.across
    intro j
    apply Covers.across
    intro k
    exact Covers.single (src:=src) (.inr (j,⟨v,b⟩)) k _

/-- The final gate adds only destination-incident restored rows. -/
theorem finish_covered (ok : FrameOK g r I J) (v : L g) (d : D g) :
    Covers (Sum.elim (native (g:=g)) (eRole (r:=r) (side:=true))) g.lanes
      (finish g (native v) d) := by
  let src := (Sum.elim (native (g:=g)) (eRole (r:=r) (side:=true)))
  change Covers src _ _
  apply Covers.cons (src:=src) (.inl v) d
  apply Covers.across
  intro b
  change Covers src _ (if g.dst b v then _ else [])
  simp only [ok.dst,decide_eq_true_eq]
  split
  next h => exact Covers.single (src:=src) (.inr ⟨v,b,h⟩) d 1
  next => exact Covers.nil

open InterchangeROMStage (Frame)
open InterchangeROMStage.Frame (Realization)

/-- Stage table parameters with the serialized frame's row fields and masks. -/
def fromFrame (f : Frame) (rank p lanes : ℕ) (minor base : ℕ → ℕ → ℕ)
    (query : ℕ → ℕ → ℕ → ℕ) : Data where
  p := p
  labels := f.labels
  rectangles := f.boxes
  queries := f.queries
  ranks := rank
  lanes := lanes
  src b v := f.incident false v b
  dst b v := f.incident true v b
  row i := ((f.minor true)[i]?).getD 0
  col i := ((f.minor false)[i]?).getD 0
  minor := minor
  base := base
  query := query

theorem frame_ok {f : Frame} (r : Realization f) (p lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) :
    FrameOK (fromFrame f r.rank p lanes minor base query) r.rect (r.sel true) (r.sel false) where
  src b v := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact r.incident_iff false v b
  dst b v := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact r.incident_iff true v b
  row i := congrArg (·.getD 0) (r.minor_get true i)
  col i := congrArg (·.getD 0) (r.minor_get false i)

/-- The five table gates occur at the even input boundaries 2 through 10. -/
def inputBoundary (tag : Fin 5) := 2*(tag.val+1)

/-- Scalar input numbering in the destination-major, lane-minor bank. -/
def slot {f : Frame} (r : Realization f) (n lanes : ℕ) (a : r.Boundary n × Fin lanes) : Ground :=
  (r.code n a.1,a.2.val)

theorem slot_injective {f : Frame} (r : Realization f) (n lanes : ℕ) :
    Function.Injective (slot r n lanes) := by
  rintro ⟨u,d⟩ ⟨v,k⟩ h
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
  exact Prod.ext (r.code_injective n h₁) (Fin.ext h₂)

/-- Every term in each of the five literal gates lies in its actual input bank. -/
theorem frame_covered {f : Frame} (r : Realization f) (p lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) (tag : Fin 5)
    (o : r.Boundary (inputBoundary tag + 1) × Fin lanes) :
    let g := fromFrame f (f.minor true).length p lanes minor base query
    Covers (r.code (inputBoundary tag)) lanes (terms g tag (slot r (inputBoundary tag+1) lanes o)) := by
  dsimp only
  rw [r.minor_length true]
  have ok := frame_ok r p lanes minor base query
  fin_cases tag
  · exact partial_covered ok o.1 o.2
  · exact mix_covered ok o.1 o.2
  · exact scatter_covered ok o.1 o.2
  · exact collect_covered (g:=fromFrame f r.rank p lanes minor base query) o.1 o.2
  · exact finish_covered ok o.1 o.2

/-- Summing a generated numeric matrix row over the finite physical input slots
gives the value of that gate's native terms. -/
theorem frame_mulVec {f : Frame} (r : Realization f) (p lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) (tag : Fin 5)
    [Fintype (r.Boundary (inputBoundary tag))] (o : r.Boundary (inputBoundary tag+1) × Fin lanes)
    (x : Ground → ZMod p) :
    let g := fromFrame f (f.minor true).length p lanes minor base query
    let ts := terms g tag (slot r (inputBoundary tag+1) lanes o)
    (∑ a, (coefficient ts (slot r (inputBoundary tag) lanes a) : ZMod p) *
      x (slot r (inputBoundary tag) lanes a)) = value x ts :=
  coefficient_mulVec p _ (slot_injective r _ _) _ (frame_covered r _ _ _ _ _ _ _) x

/-- Native pointwise operation at the five table positions of the grouped script. -/
def gateNative {f : Frame} (r : Realization f) (p : ℕ) [Fact p.Prime] (lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) :
    (tag : Fin 5) → (r.Boundary (inputBoundary tag) → Fin lanes → ZMod p) →
    r.Boundary (inputBoundary tag+1) → Fin lanes → ZMod p
  | ⟨0,_⟩, x,o,d => StageRoute.partialTable r.rect (fun a => x a d) o
  | ⟨1,_⟩, x,o,d => StageRoute.mixTable r.rect (r.sel true)
      (fun i k : Fin r.rank => (minor i k : ZMod p)) (fun a => x a d) o
  | ⟨2,_⟩, x,o,d => StageRoute.scatterTable r.rect (r.sel false) (fun a => x a d) o
  | ⟨3,_⟩, x,o,d => StageRoute.sumQueries r.rect
      (InterchangeROMRepair.mixerMap (fun i k : Fin lanes => (base i k : ZMod p)))
      (fun j : Fin f.queries => InterchangeROMRepair.mixerMap (fun i k : Fin lanes => (query j i k : ZMod p)))
      x o d
  | ⟨4,_⟩, x,o,d => StageRoute.finishTable r.rect (fun a => x a d) o

theorem frame_gate_value {f : Frame} (r : Realization f) (p : ℕ) [Fact p.Prime] (lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) (tag : Fin 5)
    (o : r.Boundary (inputBoundary tag+1) × Fin lanes) (x : Ground → ZMod p) :
    let g := fromFrame f (f.minor true).length p lanes minor base query
    value x (terms g tag (slot r (inputBoundary tag+1) lanes o)) =
      gateNative r p lanes minor base query tag (fun a d => x (slot r (inputBoundary tag) lanes (a,d))) o.1 o.2 := by
  dsimp only
  rw [r.minor_length true]
  let g := fromFrame f r.rank p lanes minor base query
  have ok := frame_ok r p lanes minor base query
  fin_cases tag
  · exact partial_correct ok x o.1 o.2
  · exact mix_correct ok x o.1 o.2
  · exact scatter_correct (p:=p) (g:=g) rfl ok x o.1 o.2
  · exact collect_correct (g:=g) (r:=r.rect) x o.1 o.2
  · exact finish_correct ok x o.1 o.2

/-- The ordinal matrix emitted by any of the five gates acts on arbitrary
typed input rows by the corresponding native rectangle operator. -/
theorem frame_gate_mulVec {f : Frame} (r : Realization f) (p : ℕ) [Fact p.Prime] (lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) (tag : Fin 5)
    [Fintype (r.Boundary (inputBoundary tag))] (o : r.Boundary (inputBoundary tag+1) × Fin lanes)
    (x : r.Boundary (inputBoundary tag) → Fin lanes → ZMod p) :
    let g := fromFrame f (f.minor true).length p lanes minor base query
    let ts := terms g tag (slot r (inputBoundary tag+1) lanes o)
    (∑ a, (coefficient ts (slot r (inputBoundary tag) lanes a) : ZMod p) * x a.1 a.2) =
      gateNative r p lanes minor base query tag x o.1 o.2 := by
  let z : Ground → ZMod p := Function.extend (slot r (inputBoundary tag) lanes) (fun a => x a.1 a.2) (fun _ => 0)
  have hz (a : r.Boundary (inputBoundary tag) × Fin lanes) :
      z (slot r (inputBoundary tag) lanes a) = x a.1 a.2 := (slot_injective r _ _).extend_apply _ _ a
  have h := (frame_mulVec r p lanes minor base query tag o z).trans (frame_gate_value r p lanes minor base query tag o z)
  simpa only [hz] using h

/-- Literal source membership, without choosing an inverse code or an index. -/
theorem frame_source_mem {f : Frame} (r : Realization f) (p lanes : ℕ)
    (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ) (tag : Fin 5)
    (o : r.Boundary (inputBoundary tag+1) × Fin lanes) (t : Term)
    (ht : t ∈ terms (fromFrame f (f.minor true).length p lanes minor base query) tag
      (slot r (inputBoundary tag+1) lanes o)) :
    t.1.1 ∈ f.bank (inputBoundary tag) ∧ t.1.2 < lanes := by
  obtain ⟨⟨a,k⟩,ha⟩ := frame_covered r _ _ _ _ _ _ o t ht
  rw [← ha]
  exact ⟨r.code_mem _ a,k.isLt⟩

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROMTable

private def laneOrder (lanes : ℕ) : Series (Fin lanes) :=
  ⟨List.finRange lanes,List.nodup_finRange _,List.mem_finRange⟩

/-- Serialization order of the ground components of a stage bank. -/
noncomputable def scalarOrder {f : Frame} (r : Realization f) (n lanes : ℕ) :
    Series (r.Boundary n × Fin lanes) := (r.order n).cart (laneOrder lanes)

theorem scalarOrder_tab {f : Frame} (r : Realization f) (n lanes : ℕ) :
    (scalarOrder r n lanes).tab (slot r n lanes) = expandRoles (f.bank n) lanes := by
  have axis (a : r.Boundary n) : (laneOrder lanes).tab (fun k => slot r n lanes (a,k)) =
      (List.range lanes).map (fun k => (r.code n a,k)) := by
    apply List.ext_getElem (by simp [Series.tab,laneOrder])
    intro i hi hi'
    simp [Series.tab,laneOrder,slot]
  rw [scalarOrder,Series.grouped,← r.order_tab n]
  rw [show (fun a => (laneOrder lanes).tab (fun k => slot r n lanes (a,k))) =
    (fun a => (List.range lanes).map fun k => (r.code n a,k)) from funext axis]
  simp only [expandRoles,Series.tab,List.flatMap_def,List.map_map,Function.comp_def]

/-- Reading the physical lookup table at a ground-letter tuple produces the
tuple specified by the native grouped stage at that address. -/
theorem frame_gate_lookup (c : Parameters) (r : Realization c.1) [Fact c.2.1.Prime] (tag : Fin 5)
    [Fintype (r.Boundary (inputBoundary tag))] (x : r.Boundary (inputBoundary tag) → D (decode c) → ZMod c.2.1) :
    let n := inputBoundary tag
    let inp := scalarOrder r n c.2.2.1
    let out := scalarOrder r (n+1) c.2.2.1
    let g := decode c
    let table := matrixTable c.2.1 inp.count (gateMatrix c (c.1.gate tag n))
    let src := stripe inp (fun a => numeral (x a.1 a.2).val)
    let dst := stripe out (fun b => numeral
      (gateNative r c.2.1 c.2.2.1 g.minor g.base g.query tag x b.1 b.2).val)
    RegisterLookup.read table src = dst ∧ (src,dst) ∈ table := by
  let n := inputBoundary tag
  let lanes := c.2.2.1
  let g := decode c
  let y : Ground → ZMod c.2.1 := Function.extend (slot r n lanes) (fun a => x a.1 a.2) (fun _ => 0)
  have hy (a : r.Boundary n × Fin lanes) : y (slot r n lanes a) = x a.1 a.2 :=
    (slot_injective r n lanes).extend_apply _ _ _
  have h := gate_lookup c (c.1.gate tag n) (scalarOrder r n lanes) (scalarOrder r (n+1) lanes)
    (slot r n lanes) (slot r (n+1) lanes) (scalarOrder_tab r n lanes).symm
    (scalarOrder_tab r (n+1) lanes).symm (slot_injective r n lanes)
    (fun b => frame_covered r c.2.1 lanes g.minor g.base g.query tag b) y
  have hv (b : r.Boundary (n+1) × Fin lanes) :
      value y (terms (decode c) (c.1.gate tag n).1 (slot r (n+1) lanes b)) =
        gateNative r c.2.1 lanes g.minor g.base g.query tag x b.1 b.2 := by
    have he := frame_gate_value r c.2.1 lanes g.minor g.base g.query tag b y
    have hy' : (fun a d => y (slot r (inputBoundary tag) lanes (a,d))) = x := by
      funext a d
      exact hy (a,d)
    rw [hy'] at he
    exact he
  dsimp only at h ⊢
  simpa only [hy,hv] using h

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
