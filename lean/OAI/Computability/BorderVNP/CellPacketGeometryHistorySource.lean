import OAI.Computability.BorderVNP.CellPacketGeometryHistoryLookup

/-! # Physical upstream inputs to the sorted sparse packet geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Packing.Inherited FrozenTape ParseBatchSort ParseBatchLookup ParseBatchCounts PackedHistogram
open VPVNP.VerifierNetwork LiveWords
open private readScalar from OAI.Computability.BorderVNP.CellPacketGeometryHistoryFields
open private zero_value from OAI.Computability.BorderVNP.PackedInheritedWordCircuit

variable {σ : Type}

private def extend {z s : ℕ} (h : s≤z) (zero : σ) (f : Fin s → σ) (j : Fin z) : σ :=
  prepend (fun _ : Fin (z-s) => zero) f (j.cast (by omega))

private theorem extend_value {z s : ℕ} (h : s≤z) (zero : σ) (f : Fin s → σ) (x : σ → Bool)
    (hz : x zero = false) : value (fun j => x (extend h zero f j)) = value (x ∘ f) := by
  have cast_value {n m : ℕ} (he : n=m) (v : Fin m → Bool) : value (v ∘ Fin.cast he)=value v := by
    cases he; rfl
  have e := prepend_map x (fun _ : Fin (z-s) => zero) f
  have hc := cast_value (show z=s+(z-s) by omega) (x ∘ prepend (fun _ : Fin (z-s) => zero) f)
  exact hc.trans ((congrArg value e).trans (by simp [value_prepend,Function.comp_def,hz,zero_value]))

variable {a C cap k w d t q : ℕ} {R B U V E : Type} [Fintype σ] [Fintype E]
variable (S : Schema R B) (L : Schema U V) (A₀ : Access R B U V E σ a d t k w)
variable (hd : d≤q) (ht : t≤q) (room : a<2^q) (croom : C<2^k)
variable (hs : ∀ r, S.width r ≤ w) (hl : ∀ u, L.width u ≤ w)

private def oneScalar {T X : Type} {m : ℕ} (f : Pins T X m → σ) (zero : σ) (schema : Schema T X)
    (bound : ∀ r, schema.width r ≤ w) (r : T) (j : Fin cap) : Fin w → σ :=
  if h : j.val < (schema.tags r).length then extend (bound r) zero (fun b => f (.inr (schema.pin r ⟨j.val,h⟩ b)))
  else fun _ => zero

private def scalarPin (row : Slot a R U) (j : Fin cap) : Fin w → σ :=
  match row with
  | .inr (some (.inl r)) => oneScalar A₀.history A₀.zero S hs r j
  | .inr (some (.inr u)) => oneScalar A₀.binding A₀.zero L hl u j
  | _ => fun _ => A₀.zero

omit [Fintype σ] in
private theorem one_value {T X : Type} {m : ℕ} (f : Pins T X m → σ) (zero : σ) (schema : Schema T X)
    (bound : ∀ r, schema.width r ≤ w) (x : σ → Bool) (hz : x zero = false) (r : T) (j : Fin cap) :
    value (fun b => x (oneScalar f zero schema bound r j b)) = readScalar schema (x ∘ f) r j.val := by
  by_cases h : j.val < (schema.tags r).length
  · simp only [oneScalar,h,dite_true,extend_value _ _ _ _ hz,readScalar]
    rfl
  · simp [oneScalar,h,readScalar,hz,zero_value]

private def selectPin : Base (roster a S L).length k w E (Field cap) → σ ⊕ (Fin (roster a S L).length × Column k w)
  | .inl (.inl (i,j)) => .inr (i,.inl j)
  | .inl (.inr (.inl ej)) => .inl (A₀.field ej)
  | .inl (.inr (.inr ())) => .inl A₀.valid
  | .inr (i,.inl b,j) => .inr (i,.inr (b,j))
  | .inr (i,.inr f,j) => .inl (scalarPin S L A₀ hs hl ((roster a S L).get i) f j)

/-- Every frozen scalar, including zero extension and unused scalar pins, is
selected from existing wires. The one batched site lookup is the only gate cost. -/
noncomputable def source : Frame σ (Base (roster a S L).length k w E (Field cap)) :=
  (sites S L A₀ hd ht room croom).withInput.select (selectPin S L A₀ hs hl)

/-- The public anchor bus used by the stable site sort. -/
noncomputable def anchors : Frame σ (Fin (roster a S L).length × Fin q) :=
  (Frame.initial (id : σ → σ)).step fun z => request A₀ hd ht room ((roster a S L).get z.1) z.2

theorem source_size : (source (cap := cap) S L A₀ hd ht room croom hs hl).size ≤ siteCost a (roster a S L).length q k w := by
  simpa only [source,Frame.select_size,Frame.withInput_size] using sites_size S L A₀ hd ht room croom

omit [Fintype E] in
theorem anchors_size : (anchors S L A₀ hd ht room).size ≤ (roster a S L).length*q*8 := by
  simpa only [anchors,Frame.initial_size,Fintype.card_prod,Fintype.card_fin,zero_add] using
    Frame.step_size_le (Frame.initial (id : σ → σ)) (fun z : Fin (roster a S L).length × Fin q =>
      request A₀ hd ht room ((roster a S L).get z.1) z.2) 8 (fun z => request_size A₀ hd ht room _ _)

variable (x : σ → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
variable (old : ∀ r ∈ S.rows, x (A₀.history (.inl (r,.inl ()))) = true → owner (x ∘ A₀.history) r < a)
variable (last : ∀ u ∈ L.rows, x (A₀.binding (.inl (u,.inl ()))) = true → owner (x ∘ A₀.binding) u < a)
local notation3 "F₀" => source (cap := cap) S L A₀ hd ht room croom hs hl

include old last in
omit [Fintype E] in
theorem anchors_value (i : Fin (roster a S L).length) : value (fun j => (anchors S L A₀ hd ht room).eval x (i,j)) =
    (anchor S L (x ∘ A₀.history) (x ∘ A₀.binding) i).val := by
  have e : (Frame.initial (id : σ → σ)).eval x = x := funext fun j => Frame.initial_eval ..
  simpa only [anchors,Frame.step_eval,e,wordValue] using request_value A₀ hd ht room S L x old last i

include old last in
theorem source_cell (values : ∀ s, value (fun j => x (A₀.table s (.inl j))) = (cells s).val)
    (i : Fin (roster a S L).length) : value (fun j => (F₀).eval x (.inl (.inl (i,j)))) =
      (cellOf S L (x ∘ A₀.history) (x ∘ A₀.binding) cells i).val := by
  simp only [source,selectPin,Frame.select_eval,Frame.withInput_eval_inr,sites_bits S L A₀ hd ht room croom x old last,Sum.elim_inl,cellOf]
  cases siteOf (x ∘ A₀.history) (x ∘ A₀.binding) ((roster a S L).get i) with
  | none => exact value_encode _
  | some s => exact values s

include old last in
theorem source_scalar (hz : x A₀.zero = false)
    (starts : ∀ s b, value (fun j => x (A₀.table s (.inr (b,j)))) = (if b then box else off) s)
    (i : Fin (roster a S L).length) (g : Field cap) :
    value (fun j => (F₀).eval x (.inr (i,g,j))) =
      scalarArgs S L (x ∘ A₀.history) (x ∘ A₀.binding) off box ((roster a S L).get i) g := by
  rcases g with b | field
  · simp only [source,selectPin,Frame.select_eval,Frame.withInput_eval_inr,sites_bits S L A₀ hd ht room croom x old last,Sum.elim_inr,scalarArgs]
    cases siteOf (x ∘ A₀.history) (x ∘ A₀.binding) ((roster a S L).get i) with
    | none => exact zero_value
    | some s => exact starts s b
  · simp only [source,selectPin,Frame.select_eval,Frame.withInput_eval_inl]
    rcases (roster a S L).get i with j | _ | r | u
    · simp [scalarArgs,scalarPin,hz,zero_value]
    · simp [scalarArgs,scalarPin,hz,zero_value]
    · exact one_value A₀.history A₀.zero S hs x hz r field
    · exact one_value A₀.binding A₀.zero L hl x hz u field

theorem source_field (e : E) (j : Fin w) : (F₀).eval x (.inl (.inr (.inl (e,j)))) = x (A₀.field (e,j)) := by
  simp [source,selectPin]

theorem source_valid : (F₀).eval x (.inl (.inr (.inr ()))) = x A₀.valid := by
  simp [source,selectPin]

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
