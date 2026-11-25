import OAI.Computability.BorderVNP.CellPacketGeometryDescriptors
import OAI.Computability.BorderVNP.PackedLookup

/-! # Physical row numbering and wiring of both geometry sort inputs

The shared source frame supplies per-word cell and payload pins, a current cell key
for each chunk and the ordinary geometry operand pins. The fixed pin map inserts
all public markers and padding, fans each chunk key to its three adjacent raw rows,
and preserves the numerical geometry operands used by private-slot descriptors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open VPVNP.VerifierNetwork PackedHistogram ParseBatchSort ParseBatchCounts Packing.Word

/-- Live source fields before inserting sort markers and power-of-two padding. -/
abbrev Pins (N M k w : ℕ) (E : Type*) :=
  (Fin N × (Fin k ⊕ Fin w)) ⊕ ((Fin M × Fin k) ⊕ ((E × Fin w) ⊕ Unit))

/-- Fixed raw ordering of the three fields of all source descriptors. -/
def coords (M : ℕ) : List (Fin M × Fin 3) :=
  (List.finRange M).flatMap fun i => [(i,0),(i,1),(i,2)]

/-- Exactly three sortable scalar words per chunk. -/
theorem coords_length (M : ℕ) : (coords M).length = 3*M := by
  have h (xs : List (Fin M)) :
      (xs.flatMap fun i => ([(i,0),(i,1),(i,2)] : List (Fin M × Fin 3))).length = 3*xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons,ih]; omega
  simpa [coords] using h (List.finRange M)

variable {C N M p d k w : ℕ} {E σ : Type*} [Fintype σ] [Fintype E]

private noncomputable def natBit (n : ℕ) (j : Fin k) := (numberWords k).symm (Fin.ofNat (2^k) n) j

private noncomputable def keyPin {T : Type*} {n : ℕ}
    (wire : Fin n → Fin k → T) (r : Markers.Row C n) (j : Fin k) : Expr T :=
  match r with
  | .start c | .stop c => .const (natBit c.val j)
  | .data i => .input (wire i j)
  | .pad => .const (natBit C j)

private def valuePin {T : Type*} {n : ℕ}
    (wire : Fin n → Fin w → T) (r : Markers.Row C n) (j : Fin w) : Expr T :=
  match r with
  | .data i => .input (wire i j)
  | _ => .const false

private noncomputable def field (C N M p d k w : ℕ) (E : Type*) :
    Columns p d k w E → Expr (Pins N M k w E)
  | .inl (i,.inl j) => keyPin (fun a b => .inl (a,.inl b)) (Markers.row C N i.val) j
  | .inl (i,.inr j) => valuePin (fun a b => .inl (a,.inr b)) (Markers.row C N i.val) j
  | .inr (.inl (i,j)) => keyPin (fun z b => .inr (.inl (((coords M)[z.val]).1,b)))
      (Markers.row C (coords M).length i.val) j
  | .inr (.inr x) => .input (.inr (.inr x))

/-- Every source pin is selected wire the actual upstream frame or hardwired to a
single constant bit. Dynamic ownership never changes the circuit or its row count. -/
noncomputable def source (C p d : ℕ) (upstream : Frame σ (Pins N M k w E)) : Frame σ (Columns p d k w E) :=
  upstream.step (field C N M p d k w E)

/-- The descriptor expression in a physical raw lane. The empty cells still have
markers and holes, which carry zero payload. -/
def expression (C d : ℕ) (fit : C+N+C ≤ 2^p) (dest H : ℕ) (ref : Fin M → Reference N E)
    (r : Fin (2^d)) : WidthExpr (E ⊕ Fin (2^p)) :=
  match Markers.row C (coords M).length r.val with
  | .data i => let z := (coords M)[i.val]; (ref z.1).fields fit dest H z.2
  | _ => .const 0

private theorem keyPin_value {T : Type*} {n : ℕ} (wire : Fin n → Fin k → T) (x : T → Bool)
    (owner : Fin n → Fin C) (correct : ∀ i, value (x ∘ wire i) = (owner i).val)
    (r : Markers.Row C n) (fit : C < 2^k) :
    wordValue x (keyPin wire r) = Markers.key owner r := by
  cases r with
  | start c | stop c => simp [wordValue,keyPin,Markers.key,natBit,
      BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
      Nat.mod_eq_of_lt (c.isLt.trans fit)]
  | data i => exact correct i
  | pad => simp [wordValue,keyPin,Markers.key,natBit,
      BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,Nat.mod_eq_of_lt fit]

private theorem valuePin_value {T : Type*} {n : ℕ} (wire : Fin n → Fin w → T) (x : T → Bool)
    (r : Markers.Row C n) : wordValue x (valuePin wire r) = Markers.word (fun i => value (x ∘ wire i)) r := by
  have zero (b : ℕ) : value (fun _ : Fin b => false) = 0 := by induction b <;> simp_all [value]
  cases r <;> simp [valuePin,wordValue,Markers.word,Function.comp_def,
    BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,zero]

/-- Values of the raw words, dynamic keys and retained physical slot operands in
the two geometry sorts. The only semantic inputs concern the actual upstream
pins of the original site and chunk keys. -/
theorem source_values (upstream : Frame σ (Pins N M k w E)) (x : σ → Bool)
    (wordOwner : Fin N → Fin C) (partOwner : Fin M → Fin C) (fit : C < 2^k)
    (pw : ∀ i, value (fun j => upstream.eval x (.inl (i,.inl j))) = (wordOwner i).val)
    (pr : ∀ i, value (fun j => upstream.eval x (.inr (.inl (i,j)))) = (partOwner i).val) :
    let z := (source C p d upstream).eval x
    let raw := fun i => z (.inl i)
    let word := fun i => value fun j => upstream.eval x (.inl (i,.inr j))
    (∀ i, Stable.key raw i = Markers.key wordOwner (Markers.row C N i.val)) ∧
    (∀ i, Stable.weight raw i = Markers.word word (Markers.row C N i.val)) ∧
    (∀ i : Fin (2^d), value (fun j => z (.inr (.inl (i,j)))) =
      Markers.key (fun q => partOwner ((coords M)[q.val]).1) (Markers.row C (coords M).length i.val)) ∧
    ∀ y, z (.inr (.inr y)) = upstream.eval x (.inr (.inr y)) := by
  intro z raw word
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_,fun y => ?_⟩
  · simpa only [Stable.key,raw,z,source,Frame.step_eval,field,wordValue] using
      keyPin_value (fun a b => .inl (a,.inl b)) (upstream.eval x) wordOwner pw (Markers.row C N i.val) fit
  · simpa only [Stable.weight,raw,z,source,Frame.step_eval,field,wordValue,word,Function.comp_def] using
      valuePin_value (fun a b => .inl (a,.inr b)) (upstream.eval x) (Markers.row C N i.val)
  · simpa only [z,source,Frame.step_eval,field,wordValue] using
      keyPin_value (fun q b => .inr (.inl (((coords M)[q.val]).1,b))) (upstream.eval x)
        (fun q => partOwner ((coords M)[q.val]).1) (fun q => pr _) (Markers.row C (coords M).length i.val) fit
  · simp [z,source,field,BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]

omit [Fintype E] in
/-- Every raw row expression fits before knowing the first sorting permutation. -/
theorem expression_fits (fit : C+N+C ≤ 2^p) (dest H : ℕ) (ref : Fin M → Reference N E)
    (up : Columns p d k w E → Bool) (π : Equiv.Perm (Fin (2^p))) (r : Fin (2^d))
    (space : dest+2^p < 2^w) (header : H < 2^w) (one : 1 < 2^w) :
    (expression C d fit dest H ref r).Fits w (operands up π) := by
  unfold expression
  cases Markers.row C (coords M).length r.val with
  | data i => exact (ref _).fits fit dest H up π _ space header one
  | _ => exact Nat.two_pow_pos _

end CellPacketGeometry.Schema

end BorderVNP
end Computability
end OAI
