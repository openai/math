import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFinal
import OAI.Computability.BorderVNP.PackedInheritedWordCircuit

/-! # Gate-level site requests from the enabled, numerically encoded frozen owner columns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Packing.Inherited FrozenTape ParseBatchSort ParseBatchLookup PackedHistogram VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private zero_value from OAI.Computability.BorderVNP.PackedInheritedWordCircuit

variable {a k w d t q : ℕ} {R B U V E σ A : Type}

/-- Physical table for one real final site's cell, bit start, and merged box start. -/
abbrev Column (k w : ℕ) := Fin k ⊕ (Bool × Fin w)

/-- Static pin selections on the actual joined public upstream frame. -/
structure Access (R B U V E σ : Type) (a d t k w : ℕ) where
  /-- The saved numeric records and owner flags of the historical site program. -/
  history : Pins R B d → σ
  /-- The final absolute incidence record bus. -/
  binding : Pins U V t → σ
  /-- The final cell, bit start, and box start of each stable site ID. -/
  table : Fin a → Column k w → σ
  /-- The shared private-size, report-address, and original-site pointer words. -/
  field : E × Fin w → σ
  /-- The validity bit propagated to the packet frame. -/
  valid : σ
  /-- One shared false wire for zero extension and empty field slots. -/
  zero : σ

/-- Copy a narrower big-endian word onto the suffix of a wider bus. -/
def widen {s z : ℕ} (h : s≤z) (f : Fin s → Expr σ) : Fin z → Expr σ :=
  fun j => prepend (fun _ : Fin (z-s) => .const false) f (j.cast (by omega))

theorem widen_value {s z : ℕ} (h : s≤z) (f : Fin s → Expr σ) (x : σ → Bool) :
    wordValue x (widen h f) = wordValue x f := by
  have cast_value {n m : ℕ} (he : n=m) (v : Fin m → Bool) : value (v ∘ Fin.cast he)=value v := by
    cases he; rfl
  have e := prepend_map (StatementCircuit.Expr.eval x) (fun _ : Fin (z-s) => (StatementCircuit.Expr.const false : Expr σ)) f
  have hc := cast_value (show z=s+(z-s) by omega)
    (fun j => (prepend (fun _ : Fin (z-s) => (StatementCircuit.Expr.const false : Expr σ)) f j).eval x)
  exact hc.trans ((congrArg value e).trans (by simp [value_prepend,zero_value,Function.comp_def,StatementCircuit.Expr.eval,wordValue]))

theorem widen_pin_size {s z : ℕ} (h : s≤z) (f : Fin s → σ) (j : Fin z) :
    (widen h (fun i => .input (f i)) j).size = 1 := by
  let e := prepend_map StatementCircuit.Expr.size (fun _ : Fin (z-s) => (StatementCircuit.Expr.const false : Expr σ))
    (fun i : Fin s => .input (f i))
  have he := prepend_map (fun _ : Unit => (1:ℕ)) (fun _ : Fin (z-s) => ()) (fun _ : Fin s => ())
  exact congrFun (e.trans he.symm) (j.cast (by omega))

variable (A₀ : Access R B U V E σ a d t k w) (hd : d≤q) (ht : t≤q) (room : a<2^q)

/-- Disabled row slots use the separate hole anchor. All original numeric owner
bits are forwarded, independently of how many old pieces share their site. -/
noncomputable def request : Slot a R U → Fin q → Expr σ
  | .inl i => fixed ⟨i.val,i.isLt.trans room⟩
  | .inr none => fixed ⟨a,room⟩
  | .inr (some (.inl r)) => fun j => mux (.input (A₀.history (.inl (r,.inl ()))))
      (widen hd (fun b => .input (A₀.history (.inl (r,.inr b)))) j) (fixed ⟨a,room⟩ j)
  | .inr (some (.inr u)) => fun j => mux (.input (A₀.binding (.inl (u,.inl ()))))
      (widen ht (fun b => .input (A₀.binding (.inl (u,.inr b)))) j) (fixed ⟨a,room⟩ j)

theorem request_size (r : Slot a R U) (j : Fin q) : (request A₀ hd ht room r j).size ≤ 8 := by
  rcases r with i | _ | r | u <;> simp [request,mux,StatementCircuit.Expr.size,widen_pin_size,fixed]

private theorem name_value {T X : Type} {d' : ℕ} (f : Pins T X d' → σ) (h : d'≤q)
    (x : σ → Bool) (r : T) (live : x (f (.inl (r,.inl ()))) = true → owner (x ∘ f) r < a) :
    wordValue x (fun j => mux (.input (f (.inl (r,.inl ()))))
      (widen h (fun b => .input (f (.inl (r,.inr b)))) j) (fixed ⟨a,room⟩ j)) =
      (name a (x ∘ f) r).elim a Fin.val := by
  by_cases yes : x (f (.inl (r,.inl ()))) = true
  · have bit : (fun j => (mux (.input (f (.inl (r,.inl ()))))
        (widen h (fun b => .input (f (.inl (r,.inr b)))) j) (fixed ⟨a,room⟩ j)).eval x) =
        fun j => (widen h (fun b => .input (f (.inl (r,.inr b)))) j).eval x := by
      funext j; simp [mux_eval,StatementCircuit.Expr.eval,yes]
    rw [wordValue,bit,← wordValue,widen_value]
    have hn : name a (x ∘ f) r = some ⟨owner (x ∘ f) r,live yes⟩ := dite_eq_left ⟨yes,live yes⟩
    rw [hn]
    rfl
  · have bit : (fun j => (mux (.input (f (.inl (r,.inl ()))))
        (widen h (fun b => .input (f (.inl (r,.inr b)))) j) (fixed ⟨a,room⟩ j)).eval x) =
        fun j => (fixed (σ := σ) ⟨a,room⟩ j).eval x := by
      funext j; simp [mux_eval,StatementCircuit.Expr.eval,yes]
    rw [wordValue,bit,← wordValue,fixed_value]
    simp [name,Function.comp_def,yes]

/-- On all actual roster slots the native address is exactly the real grouping
anchor, including every disabled history/binding row. -/
theorem request_value (S : Schema R B) (L : Schema U V) (x : σ → Bool)
    (old : ∀ r ∈ S.rows, x (A₀.history (.inl (r,.inl ()))) = true → owner (x ∘ A₀.history) r < a)
    (last : ∀ u ∈ L.rows, x (A₀.binding (.inl (u,.inl ()))) = true → owner (x ∘ A₀.binding) u < a)
    (i : Fin (roster a S L).length) :
    wordValue x (request A₀ hd ht room ((roster a S L).get i)) =
      (anchor S L (x ∘ A₀.history) (x ∘ A₀.binding) i).val := by
  have mem := List.get_mem (roster a S L) i
  unfold anchor
  rcases z : (roster a S L).get i with j | _ | r | u
  · simp [request,siteOf,anchorSlot]
  · simp [request,siteOf,holeSlot]
  · rw [z] at mem
    have rm : r ∈ S.rows := by simpa [roster] using mem
    have key := name_value room A₀.history hd x r (old r rm)
    change _ = ((name a _ _).elim (holeSlot a S L) (anchorSlot S L)).val
    exact key.trans (by cases name a (x ∘ A₀.history) r <;> rfl)
  · rw [z] at mem
    have um : u ∈ L.rows := by simpa [roster] using mem
    have key := name_value room A₀.binding ht x u (last u um)
    change _ = ((name a _ _).elim (holeSlot a S L) (anchorSlot S L)).val
    exact key.trans (by cases name a (x ∘ A₀.binding) u <;> rfl)

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
