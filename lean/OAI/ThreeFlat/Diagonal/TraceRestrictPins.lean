import OAI.ThreeFlat.Diagonal.TraceBitHeader
import OAI.ThreeFlat.Diagonal.TraceArrayLayout

namespace OAI
/-! # Restricting the open inputs of a row network -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open LaneCursor
variable {F : Type*} {n P Q k low slots offset : ℕ}

theorem restricted_source (N : BitNetwork F P) (wire : Fin P → Option (Fin Q))
    (i : Fin N.cells) (j : Fin 3) :
    (N.restrictPins wire).source i j = relabel wire (N.source i j) := by
  cases N with
  | mk n c src tables =>
    dsimp only [BitNetwork.restrictPins]
    cases src i j <;> rfl

private theorem wired_before (wire : Fin P → Option (Fin Q)) (s : BitSource n P)
    (hs : wired (relabel wire s)) : wired s := by
  cases s with
  | pin | hidden => trivial
  | constant => exact hs

private def originalOccurrence (N : BitNetwork F P) (wire : Fin P → Option (Fin Q))
    (e : Occurrence (N.restrictPins wire)) : Occurrence N :=
  ⟨e.val,wired_before wire _ ((congrArg wired (restricted_source N wire e.val.1 e.val.2)).mp e.property)⟩

private theorem relabel_owner (wire : Fin P → Option (Fin Q)) (old : Fin P → Row k low)
    (pins : Fin Q → Row k low) (hh : Fin n → Row k low) (fallback : Row k low)
    (h : ∀ i j, wire i = some j → pins j = old i) (s : BitSource n P) (hs : wired (relabel wire s)) :
    sourceRow hh pins fallback (relabel wire s) = sourceRow hh old fallback s := by
  cases s with
  | hidden => rfl
  | constant => exact False.elim hs
  | pin i =>
    cases hi : wire i with
    | none => simp [relabel,hi,wired] at hs
    | some j => simpa only [relabel,hi,sourceRow] using h i j hi

def restrictLayout {N : BitNetwork F P} (L : RowLayout N k low offset slots)
    (wire : Fin P → Option (Fin Q)) (pins : Fin Q → Row k low)
    (owner : ∀ i j, wire i = some j → pins j = L.pinRow i) : RowLayout (N.restrictPins wire) k low offset slots where
  cellAddress := L.cellAddress
  hiddenRow := L.hiddenRow
  pinRow := pins
  offset := L.offset
  code e := L.code (originalOccurrence N wire e)
  reaches e := by
    let old := originalOccurrence N wire e
    let fallback := (L.cellAddress e.val.1).1
    have hs := restricted_source N wire e.val.1 e.val.2
    have good := (congrArg wired hs).mp e.property
    have place := (congrArg (sourceRow L.hiddenRow pins fallback) hs).trans
      (relabel_owner wire L.pinRow pins L.hiddenRow fallback owner _ good)
    exact (L.reaches old).trans (congrArg (fun v => partner v (L.offset (L.code old))) place.symm)

private theorem relabel_rowAddress {b t n q : ℕ} (wire : Fin P → Option (Fin Q))
    (v : Fin t) (input : Fin t → Fin q → BitSource b P) (s : BitSource n q) :
    relabel wire (TraceCircuit.rowAddress v input s) =
      TraceCircuit.rowAddress v (fun u i => relabel wire (input u i)) s := by
  cases s with
  | constant | hidden => rfl
  | pin j =>
    cases he : input v j with
    | hidden | constant => simp [TraceCircuit.rowAddress,relabel,he]
    | pin i => cases hi : wire i <;> simp [TraceCircuit.rowAddress,relabel,he,hi]

theorem restrict_assemble {b t c n q : ℕ} (wire : Fin P → Option (Fin Q))
    (rows : Fin t → Fin c → TraceCircuit.Cell F n q) (input : Fin t → Fin q → BitSource b P) :
    (TraceCircuit.assemble rows input).restrictPins wire =
      TraceCircuit.assemble rows (fun v i => relabel wire (input v i)) := by
  let N := TraceCircuit.assemble rows input
  have he : (N.restrictPins wire).source =
      (TraceCircuit.assemble rows (fun v i => relabel wire (input v i))).source := by
    funext c j
    exact (restricted_source N wire c j).trans (relabel_rowAddress wire _ input _)
  exact congrArg (fun src => BitNetwork.mk (b+t*n) (t*c) src (TraceCircuit.assemble rows input).table) he

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
