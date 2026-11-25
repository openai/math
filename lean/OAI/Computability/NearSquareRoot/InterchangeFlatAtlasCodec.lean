import OAI.Computability.NearSquareRoot.InterchangeFlatAtlas
import OAI.Computability.NearSquareRoot.InterchangeOpcode

/-!
# Decoding verified flat atlas tables

When a flat word spells a typed instruction list, the raw price and legality tests
recover its typed resource bounds. Equality of raw matrix columns then verifies
the endpoint triangles and the diagonal pivot at every recursive width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open IntegerMultiplication.Port Interchange Interchange.RectangleAtlas Interchange.StageLedger
  InterchangeSlots Opcode

variable {L T b a m : ℕ} {r : Fin T → Rectangle (Fin L)} (A : List Opcode.Word)
    (w : AddressROM.Catalog r a m b)
    (h : ∀ c : Chart r m, chart A (chartIndex c) = (w c).map encode)

include h

private theorem shape_iff (c : Chart r m) :
    shape b a m A (AddressROM.affordable a c) (chartIndex c) = true ↔
      (∀ op ∈ w c, op.legal Fin.val) ∧ ((w c).map Lag.prices).sum ≤ AddressROM.affordable a c := by
  rw [shape, h, Bool.and_eq_true, admissible_encode_iff, price_encode, decide_eq_true_eq]

private theorem edge_iff (hb : 1 < b) (s : Bool) (j : Fin m) (u : Endpoint r s) :
    edge a m L T A s j u.1 u.2.val = true ↔ ∀ f x,
      AddressROM.run w (Chart.common j u.2) f (AddressROM.run w (Chart.localMap j u) f
        (AddressROM.run w (Chart.prepare u) f x)) = AddressROM.run w (Chart.label s j u.1) f x := by
  change Opcode.equal _ (chart A (chartIndex (Chart.prepare u)) ++
    chart A (chartIndex (Chart.localMap j u)) ++ chart A (chartIndex (Chart.common (r := r) j u.2)))
    (chart A (chartIndex (Chart.label (r := r) s j u.1))) = true ↔ _
  rw [h,h,h,h, ← List.map_append, ← List.map_append, equal_encode_iff hb]
  simp only [List.foldl_append, AddressROM.run]

private theorem diag_iff (hb : 1 < b) (j : Fin m) (v : Fin L) :
    diag a m L A j v = true ↔ ∀ f x, AddressROM.run w (Chart.label true j v) f
      (Lag.fire f x (.pivot (mainRank a j) (mainRank a j))) = AddressROM.run w (Chart.label false j v) f x := by
  let p : Lag (Fin (a+m+a)) b := .pivot (mainRank a j) (mainRank a j)
  change Opcode.equal _ (encode p :: chart A (chartIndex (Chart.label (r := r) true j v)))
    (chart A (chartIndex (Chart.label (r := r) false j v))) = true ↔ _
  rw [h,h, ← List.map_cons, equal_encode_iff hb]
  simp only [List.foldl_cons, AddressROM.run,p]

omit h

/-- A table spelling a typed catalog passes the flat verifier exactly when that
catalog satisfies the native verifier at the same radix. -/
theorem catalog_iff {bits : List Bool} (H : Represents bits r) (hb : 1 < b)
    (A : List Opcode.Word) (w : AddressROM.Catalog r a m b)
    (h : ∀ c : Chart r m, chart A (chartIndex c) = (w c).map encode) :
    valid b a m L T bits A = true ↔ AddressROM.valid w = true := by
  rw [valid_iff_on H A, AddressROM.valid_iff hb w]
  simp only [shape_iff A w h, edge_iff A w h hb, diag_iff A w h hb]

/-- A passing raw table provides a native catalog. Every word on an active
chart is reconstructed exactly, including the signed rational coefficients. -/
theorem exists_catalog_of_valid {bits : List Bool} (H : Represents bits r) (hb : 1 < b)
    (A : List Opcode.Word) (hver : valid b a m L T bits A = true) :
    ∃ w : AddressROM.Catalog r a m b, AddressROM.valid w = true ∧
      ∀ c : Chart r m, chart A (chartIndex c) = (w c).map encode := by
  have hs := ((valid_iff_on H A).mp hver).1
  have hword (c : Chart r m) : admissible b (a+m+a) (chart A (chartIndex c)) = true :=
    by
      have hc := hs c
      simp only [shape, Bool.and_eq_true] at hc
      exact hc.1
  let w : AddressROM.Catalog r a m b := fun c => decodeWord _ (hword c)
  have h (c : Chart r m) : chart A (chartIndex c) = (w c).map encode :=
    (encode_decodeWord _ (hword c)).symm
  exact ⟨w, (catalog_iff H hb A w h).mp hver, h⟩

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
