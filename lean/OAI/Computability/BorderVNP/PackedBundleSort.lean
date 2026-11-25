import OAI.Computability.BorderVNP.PackedBottomBundleHeader
import OAI.Computability.BorderVNP.CellPacketGeometrySchema
import OAI.Computability.BorderVNP.CellPacketGeometryPhysical

/-! # Stable sorting of the six public fields of each bottom-bundle header

Start and stop markers bracket each cell's section. Within the section all six words
of each original bundle appear together, in the same order as the original site rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open VPVNP.VerifierNetwork CellPacketGeometry PackedHistogram ParseBatchSort ParseBatchCounts
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private keyPin valuePin keyPin_value valuePin_value from OAI.Computability.BorderVNP.CellPacketGeometrySchema

/-- Site-major, field-minor word ordinals before grouping by final cell. -/
def coords (N : ℕ) : List (Fin N × Fin 6) :=
  (List.finRange N).flatMap fun i => [(i,0),(i,1),(i,2),(i,3),(i,4),(i,5)]

/-- The source contributes six scalar lanes per bundle. -/
theorem coords_length (N : ℕ) : (coords N).length = 6*N := by
  unfold coords
  have h (xs : List (Fin N)) :
      (xs.flatMap fun i => ([(i,0),(i,1),(i,2),(i,3),(i,4),(i,5)] : List (Fin N × Fin 6))).length =
        6*xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]; omega
  simpa using h (List.finRange N)

/-- Coordinates of one live scalar lane in the padded rectangle. -/
def coord {N : ℕ} (i : Fin (6*N)) : Fin N × Fin 6 :=
  (coords N)[i.val]'(by rw [coords_length]; exact i.isLt)

/-- Numerical field in the exact order consumed by the native writer. -/
def scalar (h : BundleHeader) (f : Fin 6) : ℕ := h.words[f.val]'(by simp [BundleHeader.words])

/-- The compact cell section, in original site order. -/
def selected {C N : ℕ} (owner : Fin N → Fin C) (header : Fin N → BundleHeader) (c : Fin C) : List ℕ :=
  ((List.finRange N).filter (fun i => decide (owner i=c))).flatMap (fun i => (header i).words)

/-- The number of scalar words in a cell is six times its number of assigned bundles. -/
theorem selected_length {C N : ℕ} (owner : Fin N → Fin C) (header : Fin N → BundleHeader) (c : Fin C) :
    (selected owner header c).length = 6*((List.finRange N).filter (fun i => decide (owner i=c))).length := by
  unfold selected
  generalize (List.finRange N).filter _ = xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [BundleHeader.words]; omega

private theorem coords_words {N C : ℕ} (owner : Fin N → Fin C) (header : Fin N → BundleHeader) (c : Fin C) :
    ((coords N).filter (fun r => decide (owner r.1=c))).map (fun r => scalar (header r.1) r.2) =
      selected owner header c := by
  unfold coords selected
  generalize List.finRange N = xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : owner a = c <;> simp [h,scalar,BundleHeader.words] <;> exact ih

private theorem filter_get {α β : Type*} (xs : List α) (n : ℕ) (hlen : xs.length = n)
    (keep : α → Bool) (v : α → β) :
    (((List.finRange n).filter (fun i => keep (xs[i.val]'(hlen.symm ▸ i.isLt)))).map
      (fun i => v (xs[i.val]'(hlen.symm ▸ i.isLt)))) = (xs.filter keep).map v := by
  subst n
  have h := congrArg (fun ys => (ys.filter keep).map v) (List.map_get_finRange xs)
  simpa only [List.filter_map,List.map_map,Function.comp_def,List.get_eq_getElem] using h

/-- The marker theorem for scalar rows produces whole headers for the indicated cell. -/
theorem inside_words {C N b : ℕ} (fit : C+6*N+C ≤ 2^b) (owner : Fin N → Fin C)
    (header : Fin N → BundleHeader) (c : Fin C) :
    let owners := fun i : Fin (6*N) => owner (coord i).1
    let words := fun i : Fin (6*N) => scalar (header (coord i).1) (coord i).2
    (inside (fun i => Markers.key owners (Markers.row C (6*N) i.val)) (Markers.start fit c) (Markers.stop fit c)).map
      (fun i => Markers.word words (Markers.row C (6*N) i.val)) = selected owner header c := by
  intro owners words
  rw [Markers.inside_words]
  exact (filter_get (coords N) (6*N) (coords_length N) (fun r => decide (owner r.1=c))
    (fun r => scalar (header r.1) r.2)).trans (coords_words owner header c)

/-- Dynamic key bits, six words at each original site row, and the geometry validity bit. -/
abbrev Pins (N k w : ℕ) := (Fin N × (Fin k ⊕ Fin 6 × Fin w)) ⊕ Unit

variable {σ : Type*} [Fintype σ] {C N b k w : ℕ}

private noncomputable def field (C N b k w : ℕ) : Stable.Input b k w ⊕ Unit → Expr (Pins N k w)
  | .inl (i,.inl j) => keyPin (fun (a : Fin (6*N)) q => .inl ((coord a).1,.inl q))
      (Markers.row C (6*N) i.val) j
  | .inl (i,.inr j) => valuePin (fun (a : Fin (6*N)) q => .inl ((coord a).1,.inr ((coord a).2,q)))
      (Markers.row C (6*N) i.val) j
  | .inr _ => .input (.inr ())

/-- Insert the markers and padding before executing the public stable sort. -/
noncomputable def source (C b : ℕ) (up : Frame σ (Pins N k w)) : Frame σ (Stable.Input b k w ⊕ Unit) :=
  up.step (field C N b k w)

/-- Emitting the raw sort input uses at most one gate per bit. -/
theorem source_size (C b : ℕ) (up : Frame σ (Pins N k w)) :
    (source C b up).size ≤ up.size + 2^b*(k+w) + 1 := by
  have h (i : Stable.Input b k w ⊕ Unit) : (field C N b k w i).size ≤ 1 := by
    rcases i with ⟨i,j|j⟩ | u
    · cases hr : Markers.row C (6*N) i.val <;> simp [field,keyPin,hr,StatementCircuit.Expr.size]
    · cases hr : Markers.row C (6*N) i.val <;> simp [field,valuePin,hr,StatementCircuit.Expr.size]
    · rfl
  simpa only [source,Stable.Input,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,mul_one,
    Nat.add_assoc] using Frame.step_size_le up (field C N b k w) 1 h

/-- Semantics of the concrete physical pins for every padded input lane. -/
theorem source_values (up : Frame σ (Pins N k w)) (x : σ → Bool) (owner : Fin N → Fin C)
    (header : Fin N → BundleHeader) (fit : C < 2^k)
    (keys : ∀ i, value (fun j => up.eval x (.inl (i,.inl j))) = (owner i).val)
    (values : ∀ i f, value (fun j => up.eval x (.inl (i,.inr (f,j)))) = scalar (header i) f) :
    let raw := fun i => (source C b up).eval x (.inl i)
    Stable.key raw = (fun i => Markers.key (fun z => owner (coord z).1) (Markers.row C (6*N) i.val)) ∧
    Stable.weight raw = (fun i => Markers.word (fun z => scalar (header (coord z).1) (coord z).2)
        (Markers.row C (6*N) i.val)) ∧ (source C b up).eval x (.inr ()) = up.eval x (.inr ()) := by
  intro raw
  refine ⟨funext fun i => ?_, funext fun i => ?_,?_⟩
  · simpa only [Stable.key,raw,source,Frame.step_eval,field,wordValue] using
      keyPin_value (fun (a : Fin (6*N)) q => .inl ((coord a).1,.inl q)) (up.eval x)
        (fun z => owner (coord z).1) (fun z => keys _) (Markers.row C (6*N) i.val) fit
  · let wire := fun (a : Fin (6*N)) (q : Fin w) => (Sum.inl ((coord a).1,Sum.inr ((coord a).2,q)) : Pins N k w)
    have h (a) : value (up.eval x ∘ wire a) = scalar (header (coord a).1) (coord a).2 := values _ _
    simpa only [Stable.weight,raw,source,Frame.step_eval,field,wordValue,funext h,wire] using
      valuePin_value wire (up.eval x) (Markers.row C (6*N) i.val)
  · simp [source,field,StatementCircuit.Expr.eval]

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
