import OAI.Computability.BorderVNP.CellPacketGeometryOrderedBuffer
import OAI.Computability.BorderVNP.PackedFrozenTapeSections

/-! # Reading the emitted packet source fields from genuine retained site programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Packing.Inherited FrozenTape VPVNP.VerifierNetwork ParseBatchSort CellSparse LiveWords

variable {a C cap k w d t q : ℕ} {R B U V E σ A : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]
variable (F : Feeds σ R B U V E a d t k w) (S : Schema R B) (L : Schema U V)
variable (x : σ → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
variable (siteID : A ↪ Fin a) (state : A → Site) (binding : A → List Record)
variable (historic : S.Image (F.history.eval x) (siteID.trans Fin.valEmbedding) state)
variable (final : L.Section (F.binding.eval x) (siteID.trans Fin.valEmbedding) binding)
variable (hd : d≤q) (ht : t≤q) (room : a<2^q) (croom : C<2^k)
variable (hs : ∀ r, S.width r ≤ w) (hl : ∀ u, L.width u ≤ w)
local notation3 "A₀" => (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w)
local notation3 "up₀" => source (cap := cap) S L A₀ hd ht room croom hs hl
local notation3 "site₀" => anchor S L (F.history.eval x) (F.binding.eval x)
local notation3 "cells₀" => cellOf S L (F.history.eval x) (F.binding.eval x) cells

/-- Public operand numerals from the genuine source-field producer. -/
noncomputable def Feeds.arguments (e : E) : ℕ := value (fun j => F.field.eval x (e,j))

include historic final in
/-- All raw numerical pins required by the native ordered geometry come from
the four actual feed frames, with the two historical owner-range guarantees
derived from the installed per-site programs. -/
theorem Feeds.bus (tc : ∀ i, value (fun j => F.table.eval x (i,.inl j))=(cells i).val)
    (ts : ∀ i b, value (fun j => F.table.eval x (i,.inr (b,j)))=(if b then box else off) i) :
    (∀ i, value (fun j => (anchors S L A₀ hd ht room).eval (F.frame.eval x) (i,j)) = (site₀ i).val) ∧
    (∀ i, value (fun j => (up₀).eval (F.frame.eval x) (.inl (.inl (i,j)))) = (cells₀ i).val) ∧
    (fun (e : E) => value (fun j => (up₀).eval (F.frame.eval x) (.inl (.inr (.inl (e,j)))))) = F.arguments x ∧
    (fun (i : Fin (roster a S L).length) (g : Field cap) => value (fun j => (up₀).eval (F.frame.eval x) (.inr (i,g,j)))) =
      fun i => scalarArgs S L (F.history.eval x) (F.binding.eval x) off box ((roster a S L).get i) := by
  have old (r : R) (hr : r∈S.rows) (active : F.frame.eval x ((A₀).history (.inl (r,.inl ()))) = true) :
      owner (F.frame.eval x ∘ (A₀).history) r < a := by
    rw [F.history_read]
    have yes := (congrFun (F.history_read x) (.inl (r,.inl ()))).symm.trans active
    obtain ⟨v,hit⟩ := historic.owners r hr yes
    rw [hit]
    exact (siteID v).isLt
  have last (r : U) (hr : r∈L.rows) (active : F.frame.eval x ((A₀).binding (.inl (r,.inl ()))) = true) :
      owner (F.frame.eval x ∘ (A₀).binding) r < a := by
    rw [F.binding_read]
    have yes := (congrFun (F.binding_read x) (.inl (r,.inl ()))).symm.trans active
    obtain ⟨v,hit⟩ := final.owners r hr yes
    rw [hit]
    exact (siteID v).isLt
  refine ⟨fun i => ?_,fun i => ?_,?_,?_⟩
  · simpa only [F.history_read,F.binding_read] using
      anchors_value S L A₀ hd ht room (F.frame.eval x) old last i
  · have cellsRead s : value (fun j => F.frame.eval x ((A₀).table s (.inl j))) = (cells s).val := by
      simpa only [F.table_read] using tc s
    simpa only [F.history_read,F.binding_read] using source_cell (cap := cap) S L A₀ hd ht room croom hs hl
      (F.frame.eval x) cells old last cellsRead i
  · funext e
    simp only [source_field,F.field_read,Feeds.arguments]
  · funext i g
    have starts s b : value (fun j => F.frame.eval x ((A₀).table s (.inr (b,j)))) = (if b then box else off) s := by
      simpa only [F.table_read] using ts s b
    simpa only [F.history_read,F.binding_read] using source_scalar S L A₀ hd ht room croom hs hl (F.frame.eval x)
      off box old last (F.zero_read x) starts i g

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
