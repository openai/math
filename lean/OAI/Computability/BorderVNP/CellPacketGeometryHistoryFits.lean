import OAI.Computability.BorderVNP.CellPacketGeometryStoredFits
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryLiteralFits
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFinal
import OAI.Computability.BorderVNP.CellPacketFields

/-! # Native arithmetic fits on the real final rows and the skipped history pieces -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Crossing Shortening Packing CellSparse CellSparse.Packet Packing.Inherited FrozenTape Packing.BankPacket Packing.Word LiveWords SiteWords
open private record_fields from OAI.Computability.BorderVNP.CellPacketFields
open private readScalar from OAI.Computability.BorderVNP.CellPacketGeometryHistoryFields

variable {a C cap d t w : ℕ} {R B U V E Orig : Type}
variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

local notation3 "T₀" => template S L boxes sh lh priv rep
local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box

private theorem scalar_small {A Q : Type} {d' : ℕ} (F : Schema A Q) (v : Pins A Q d' → Bool) (r : A)
    (width : F.width r ≤ w) (j : ℕ) : readScalar F v r j < 2^w := by
  unfold readScalar
  split
  · exact (ParseBatchSort.value_lt _).trans_le (Nat.pow_le_pow_right (by decide) width)
  · exact Nat.two_pow_pos _

private theorem frozen_member (r : R) (hr : r ∈ S.rows) (j : Fin a) (active : name a x r=some j) :
    ((S.typed x r).shift (off j)).rebaseBox (box j) ∈ (G₀).cellRecords (cells j).castSucc := by
  rw [cell_rows S L boxes sh lh priv rep args x y cells off box]
  refine List.mem_flatMap.mpr ⟨j,by simp [owned],?_⟩
  rw [rows_at_anchor S L boxes sh lh priv rep args x y cells off box]
  apply List.mem_append_left
  apply List.mem_map.mpr
  have h := (name_eq x r j).mp active
  exact ⟨r,by simp [Schema.selected,hr,h.1,h.2],rfl⟩

private theorem historical_word (r : R) (hr : r ∈ S.rows) (width : S.width r≤w)
    (len : cap < 2^w) (three : 3<2^w)
    (small : ∀ c : Fin C, ∀ row ∈ (G₀).cellRecords c.castSucc, ∀ n ∈ record row, n<2^w) :
    let g := scalarArgs (cap := cap) S L x y off box (.inr (some (.inl r)) : Slot a R U)
    let code := (Stored.fromTags (S.tags r) (pin _ (sh r))).placed
      (.field (.inl false : Field cap)) (.field (.inl true))
    ∀ e ∈ code.words, e.Fits w g := by
  intro g code e he
  have inputs (j : Fin (S.tags r).length) : g (pin _ (sh r) j) < 2^w :=
    scalar_small S x r width j.val
  cases active : name a x r with
  | none =>
    apply Stored.placed_zero_fits _ _ (.inl false) (.inl true) g _ _ inputs three ((sh r).trans_lt len) e he
    · simp [g,scalarArgs,siteOf,active]
    · simp [g,scalarArgs,siteOf,active]
  | some j =>
    apply Stored.placed_word_fits _ _ (.inl false) (.inl true) g e he
    apply small (cells j) _ (frozen_member S L boxes sh lh priv rep args x y cells off box r hr j active)
    have read : code.read g = ((S.typed x r).shift (off j)).rebaseBox (box j) := by
      simpa only [format,rowRecords,active,Option.elim_some,List.map_cons,List.map_nil,List.cons.injEq,and_true,
        code,g] using format_read S L sh lh x y off box (.inr (some (.inl r)))
    rw [←read,←code.words_eval g]
    exact List.mem_map_of_mem he

/-- All intermediate arithmetic of every canonical native row-word expression
fits the machine. Active relocated rows use their genuine output values in the
final cells. Ignored history rows use zero offsets and arbitrary bounded input bits. -/
theorem rowPin_fits (widthS : ∀ r, S.width r≤w) (widthL : ∀ r, L.width r≤w)
    (len : cap<2^w) (three : 3<2^w)
    (small : ∀ c : Fin C, ∀ row ∈ (G₀).cellRecords c.castSucc, ∀ n ∈ record row, n<2^w)
    (z : (T₀).RowPin) :
    ((tape ((T₀).format z.1))[z.2.val]).Fits w
      (scalarArgs S L x y off box ((roster a S L).get z.1)) := by
  let v := (roster a S L).get z.1
  let g := scalarArgs (cap := cap) S L x y off box v
  have hm : v ∈ roster a S L := List.get_mem ..
  have all : ∀ e ∈ tape (format S L sh lh v), e.Fits w g := by
    intro e he
    rcases eqn : v with i | _ | r | u
    · simp [eqn,format,tape] at he
      subst e
      exact Nat.two_pow_pos _
    · simp [eqn,format,tape] at he
      subst e
      exact Nat.two_pow_pos _
    · rw [eqn] at hm he
      have hr : r∈S.rows := by simpa [roster] using hm
      simp only [format,tape,List.mem_cons,List.flatMap_singleton] at he
      rcases he with rfl | he
      · change 1<2^w; omega
      · change e.Fits w (scalarArgs S L x y off box v)
        rw [eqn]
        exact historical_word S L boxes sh lh priv rep args x y cells off box r hr (widthS r) len three small e he
    · rw [eqn] at he
      simp only [format,tape,List.mem_cons,List.flatMap_singleton] at he
      rcases he with rfl | he
      · change 1<2^w; omega
      · change e.Fits w (scalarArgs S L x y off box v)
        rw [eqn]
        exact Stored.fromTags_word_fits (L.tags u) (pin _ (lh u))
          (scalarArgs S L x y off box (.inr (some (.inr u)))) (fun j => scalar_small L y u (widthL u) j.val)
          three ((lh u).trans_lt len) e he
  exact all _ (List.getElem_mem z.2.isLt)

variable {D n p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin n) (portID : P ↪ Fin p)
variable (state : N.Site → Site)

/-- Bounds on the fields of the genuine final network directory imply the actual
intermediate-fit obligations of the native history emitter, including all skipped
pieces. Site and final binding sections identify each real cell's physical records. -/
theorem rowPin_fits_final (fs : Orig → List Factor)
    (historical : S.Image x (siteID.trans Fin.valEmbedding) state)
    (final : L.Section y (siteID.trans Fin.valEmbedding) (FinalCell.binding N cell siteID edgeID portID state))
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots siteID (fun v => (state v).boxes) i)
    (bitBase : ∀ v, off (siteID v)=CellAddresses.siteBase N cell (cell v) siteID (fun z => (state z).size) ⟨v,rfl⟩)
    (boxBase : ∀ v, box (siteID v)=FinalCell.firstBox siteID (fun j => (cells j).val) state v)
    (widthS : ∀ r, S.width r≤w) (widthL : ∀ r, L.width r≤w) (len : cap<2^w)
    (three : 3<2^w) (limit : Fin C → ℕ) (room : ∀ c, limit c<2^w)
    (bounded : ∀ c : Fin C, ∀ r ∈ (FinalCell.directory (fun i => (cells i).val) N cell siteID edgeID
      portID state c.val ((G₀).reports c.castSucc)).records, RecordFields r (limit c))
    (z : (T₀).RowPin) :
    ((tape ((T₀).format z.1))[z.2.val]).Fits w
      (scalarArgs S L x y off box ((roster a S L).get z.1)) := by
  apply rowPin_fits S L boxes sh lh priv rep args x y cells off box widthS widthL len three _ z
  intro c r hr b hb
  have eqn := congrArg CellSparse.Directory.records
    (placed_directory S L boxes sh lh priv rep args x y cells off box N cell siteID edgeID portID state c
      0 (fun _ => 0) fs 0 0 0 0 0 [] historical final resolved bitBase boxBase)
  change (directory S L boxes sh lh priv rep args x y cells off box).cellRecords c.castSucc =
    (FinalCell.directory (fun i => (cells i).val) N cell siteID edgeID portID state c.val ((G₀).reports c.castSucc)).records at eqn
  exact (record_fields r (bounded c r (eqn ▸ hr)) b hb).trans_lt (max_lt three (room c))

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
