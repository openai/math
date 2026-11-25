import OAI.Computability.BorderVNP.ParseBatchKeyPins
import OAI.Computability.BorderVNP.ParseBatchRawWord

/-! # Two simultaneous child reads per preorder row

Each physical slot carries a table entry or one of the two proposed child
records. Inactive and padding slots repeat a table entry, introducing no
additional choices. A single Batcher sort and adjacent scan checks all reads.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TwoReads

open VPVNP.VerifierNetwork BorderVNP.ParseBatchSort BorderVNP.ParseBatchLookup
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {ι : Type*} {J a p : ℕ}

/-- Live fields for the table value and two requested address/value pairs per row. -/
structure Columns (ι : Type*) (J a p : ℕ) where
  /-- Table row payload. -/
  table : Fin J → Fin p → Expr ι
  /-- Only binary productions issue child reads. -/
  active : Fin J → Expr ι
  /-- The two child addresses, encoded most significant bit first. -/
  address : Fin J → Bool → Fin a → Expr ι
  /-- The depth and state requested at each child. -/
  payload : Fin J → Bool → Fin p → Expr ι

/-- The payload returned by a simultaneous read must equal the proposed payload.
An out-of-range address has no row that could satisfy this condition. -/
def Checks (c : Columns ι J a p) (z : ι → Bool) : Prop :=
  ∀ u side, (c.active u).eval z = true → ∃ v : Fin J,
    v.val = value (fun k => (c.address u side k).eval z) ∧
      (fun k => (c.table v k).eval z) = fun k => (c.payload u side k).eval z

/-- Number of Batcher address bits needed for the table and both reads. -/
def sortBits (J : ℕ) := Nat.clog 2 (3*J)

private def index (hJ : 0 < J) (lane : Fin (2^(sortBits J))) : Fin J :=
  ⟨lane.val % J, Nat.mod_lt _ hJ⟩

private def side (J : ℕ) (lane : Fin (2^(sortBits J))) : Option Bool :=
  if lane.val / J = 1 then some false else if lane.val / J = 2 then some true else none

private def position (u : Fin J) (t : Fin 3) : Fin (2^(sortBits J)) :=
  ⟨t.val*J+u.val, lt_of_lt_of_le (by have := t.isLt; have := u.isLt; nlinarith) (Nat.le_pow_clog (by decide) _)⟩

private theorem index_position (hJ : 0 < J) (u : Fin J) (t : Fin 3) : index hJ (position u t) = u := by
  apply Fin.ext
  simp only [index, position, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt u.isLt]

private theorem side_position (hJ : 0 < J) (u : Fin J) (t : Fin 3) :
    side J (position u t) = if t.val = 1 then some false else if t.val = 2 then some true else none := by
  simp [side, position, Nat.mul_comm t.val J, Nat.mul_add_div hJ, Nat.div_eq_of_lt u.isLt]

private def tableAt (c : Columns ι J a p) (z : ι → Bool) (k : ℕ) : Option (Fin p → Bool) :=
  if h : k < J then some (fun j => (c.table ⟨k,h⟩ j).eval z) else none

private theorem tableAt_iff (c : Columns ι J a p) (z : ι → Bool) (k : ℕ) (out : Fin p → Bool) :
    tableAt c z k = some out ↔ ∃ v : Fin J, v.val = k ∧ (fun j => (c.table v j).eval z) = out := by
  constructor
  · unfold tableAt
    split
    · intro he; exact ⟨_,rfl,Option.some.inj he⟩
    · simp
  · rintro ⟨v,rfl,rfl⟩
    simp [tableAt, v.isLt]

private def tableRow (c : Columns ι J a p) (z : ι → Bool) (u : Fin J) : Row (Fin p → Bool) :=
  ⟨u.val, false, fun k => (c.table u k).eval z⟩

private def childRow (c : Columns ι J a p) (z : ι → Bool) (u : Fin J) (s : Bool) : Row (Fin p → Bool) :=
  ⟨value (fun k => (c.address u s k).eval z), true, fun k => (c.payload u s k).eval z⟩

private def row (hJ : 0 < J) (c : Columns ι J a p) (z : ι → Bool) (lane : Fin (2^(sortBits J))) :
    Row (Fin p → Bool) :=
  let u := index hJ lane
  match side J lane with
  | none => tableRow c z u
  | some s => if (c.active u).eval z then childRow c z u s else tableRow c z u

private theorem spec (hJ : 0 < J) (c : Columns ι J a p) (z : ι → Bool) :
    TableSpec (tableAt c z) (row hJ c z) := by
  constructor
  · intro lane
    cases hs : side J lane with
    | none => simp [row, hs, tableAt, tableRow, (index hJ lane).isLt]
    | some s =>
      cases ha : (c.active (index hJ lane)).eval z <;>
        simp [row, hs, ha, tableAt, tableRow, childRow, (index hJ lane).isLt]
  · intro k val hv
    obtain ⟨u,hu,_⟩ := (tableAt_iff c z k val).mp hv
    refine ⟨position u 0, ?_⟩
    simpa [row, index_position, side_position hJ, tableRow] using hu

private theorem rows_check_iff (hJ : 0 < J) (c : Columns ι J a p) (z : ι → Bool) :
    (∀ lane, tableAt c z (row hJ c z lane).address = some (row hJ c z lane).payload) ↔ Checks c z := by
  constructor
  · intro h u s ha
    let t : Fin 3 := if s then 2 else 1
    have hh := h (position u t)
    cases s <;> simpa [row, index_position, side_position hJ, t, ha, childRow, tableAt_iff] using hh
  · intro h lane
    cases hs : side J lane with
    | none => simp [row, hs, tableRow, tableAt, (index hJ lane).isLt]
    | some s =>
      cases ha : (c.active (index hJ lane)).eval z with
      | false => simp [row, hs, ha, tableRow, tableAt, (index hJ lane).isLt]
      | true =>
        simpa [row, hs, ha, childRow, tableAt_iff] using h (index hJ lane) s ha

private def tableKey (c : Columns ι J a p) (u : Fin J) :=
  bits (ParseRecords.constWord a u.val) (.const false) (c.table u)

private def requestKey (c : Columns ι J a p) (u : Fin J) (s : Bool) :=
  bits (c.address u s) (.const true) (c.payload u s)

/-- Pack the table and both conditional read requests into a power-of-two block. -/
def expr (hJ : 0 < J) (c : Columns ι J a p) (lane : Fin (2^(sortBits J))) (k : Fin ((p+1)+a)) :
    Expr ι :=
  let u := index hJ lane
  match side J lane with
  | none => tableKey c u k
  | some s => mux (c.active u) (requestKey c u s k) (tableKey c u k)

private theorem decoded (hJ : 0 < J) (hwidth : J ≤ 2^a) (c : Columns ι J a p) (z : ι → Bool)
    (lane : Fin (2^(sortBits J))) :
    fromWord p (selectedPayload a id) (fun k => (expr hJ c lane k).eval z) = row hJ c z lane := by
  let E := fun e : Expr ι => e.eval z
  have tableDecoded (u : Fin J) : fromWord p (selectedPayload a id) (E ∘ tableKey c u) = tableRow c z u := by
    simp only [tableKey, map_bits, fromWord_bits, selectedPayload_bits]
    have h := ParseRecords.constWord_value z a u.val (u.isLt.trans_le hwidth)
    exact congrArg (fun v => Row.mk v false (E ∘ c.table u)) h
  have requestDecoded (u : Fin J) (s : Bool) :
      fromWord p (selectedPayload a id) (E ∘ requestKey c u s) = childRow c z u s := by
    simp only [requestKey, map_bits, fromWord_bits, selectedPayload_bits]
    rfl
  cases hs : side J lane with
  | none => simpa [expr, row, hs, E, Function.comp_def] using tableDecoded (index hJ lane)
  | some s =>
    cases ha : (c.active (index hJ lane)).eval z with
    | false => simpa [expr, row, hs, ha, mux_eval, E, Function.comp_def] using tableDecoded (index hJ lane)
    | true => simpa [expr, row, hs, ha, mux_eval, E, Function.comp_def] using requestDecoded (index hJ lane) s

/-- Compile simultaneous child lookups into a Boolean frame after any preceding shared gates. -/
noncomputable def frame {σ : Type*} [Fintype σ] [Fintype ι] (f : Frame σ ι)
    (hJ : 0 < J) (c : Columns ι J a p) : Frame σ Unit :=
  lookupFrame (f.step fun i : Pins (sortBits J) ((p+1)+a) => expr hJ c i.1 i.2) id

/-- The emitted gates check both child requests at every active row. -/
theorem frame_eval {σ : Type*} [Fintype σ] [Fintype ι] (f : Frame σ ι) (hJ : 0 < J)
    (hwidth : J ≤ 2^a) (c : Columns ι J a p) (x : σ → Bool) :
    (frame f hJ c).eval x () = true ↔ Checks c (f.eval x) := by
  let g := f.step fun i : Pins (sortBits J) ((p+1)+a) => expr hJ c i.1 i.2
  let z := f.eval x
  have dec (i) : fromWord p (selectedPayload a id) (fun k => g.eval x (i,k)) = row hJ c z i := by
    simpa only [g, z, Frame.step_eval] using decoded hJ hwidth c z i
  have htable : TableSpec (tableAt c z) (fun i => fromWord p (selectedPayload a id) (fun k => g.eval x (i,k))) := by
    simpa only [dec] using spec hJ c z
  change (lookupFrame g id).eval x () = true ↔ _
  rw [lookupFrame_eval g id x (tableAt c z) htable, ← rows_check_iff hJ c z]
  apply forall_congr'
  intro i
  rw [← dec i, row_from_pins]
  rfl

/-- Each primitive field bit is a wire selection or constant in a packed child lookup. -/
def UnitFields (c : Columns ι J a p) : Prop :=
  (∀ u j, (c.table u j).size ≤ 1) ∧ (∀ u, (c.active u).size ≤ 1) ∧
  (∀ u s j, (c.address u s j).size ≤ 1) ∧ (∀ u s j, (c.payload u s j).size ≤ 1)

private theorem expr_size (c : Columns ι J a p) (h : UnitFields c) (hJ : 0 < J)
    (lane : Fin (2^(sortBits J))) (k : Fin ((p+1)+a)) : (expr hJ c lane k).size ≤ 8 := by
  have hh (u : Fin J) : ∀ k, (tableKey c u k).size ≤ 1 :=
    forall_prepend (fun e : Expr ι => e.size ≤ 1) (ParseRecords.constWord a u.val)
      (Fin.cons (.const false) (c.table u)) (fun _ => le_rfl) (fun j => by
        induction j using Fin.cases with
        | zero => exact le_rfl
        | succ j => exact h.1 u j)
  have hq (u : Fin J) (s : Bool) : ∀ k, (requestKey c u s k).size ≤ 1 :=
    forall_prepend (fun e : Expr ι => e.size ≤ 1) (c.address u s)
      (Fin.cons (.const true) (c.payload u s)) (h.2.2.1 u s) (fun j => by
        induction j using Fin.cases with
        | zero => exact le_rfl
        | succ j => exact h.2.2.2 u s j)
  cases hs : side J lane with
  | none => simpa only [expr, hs] using (hh (index hJ lane) k).trans (by decide : 1 ≤ 8)
  | some s =>
    simp only [expr, hs, mux, StatementCircuit.Expr.size]
    have ha := h.2.1 (index hJ lane)
    have ht := hh (index hJ lane) k
    have hr := hq (index hJ lane) s k
    omega

/-- Gate cost including table packing, both reads, sorting, and the adjacent checks. -/
theorem frame_size {σ : Type*} [Fintype σ] [Fintype ι] (f : Frame σ ι) (hJ : 0 < J)
    (c : Columns ι J a p) (h : UnitFields c) :
    let b := sortBits J
    (frame f hJ c).size ≤ f.size + 2^b*((p+1)+a)*8 +
      b^2*(2^b*(24*((p+1)+a)+1)) + 2^b*(10*(a+p)+11)+2 := by
  have hs := Frame.step_size_le f (fun i : Pins (sortBits J) ((p+1)+a) => expr hJ c i.1 i.2) 8
    (fun i => expr_size c h hJ i.1 i.2)
  simp only [Pins, Fintype.card_prod, Fintype.card_fin] at hs
  exact (lookupFrame_size _ _).trans (by gcongr)

end TwoReads

end BorderVNP
end Computability
end OAI
