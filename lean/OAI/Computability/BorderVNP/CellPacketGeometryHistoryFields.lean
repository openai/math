import OAI.Computability.BorderVNP.CellPacketGeometryHistoryTemplate

/-! # Numerical source operands for the cumulative history and final bindings -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse CellSparse.Packet Packing.Inherited Packing.BankPacket Packing.Word
open FrozenTape LiveWords
open private portAt routeAt from OAI.Computability.BorderVNP.CellPacketGeometryRecordPositions

variable {a C cap d t : ℕ} {R B U V E Orig I J : Type}

private theorem code_congr (s : Stored.Shape) (f : ℕ → WidthExpr I) (g : ℕ → WidthExpr J) (x : I → ℕ) (y : J → ℕ)
    (eqn : ∀ n, (f n).eval x = (g n).eval y) :
    (s.code f).read x = (s.code g).read y := by
  cases s <;> simp [Stored.Shape.code,RecordCode.read,portAt,routeAt,PortCode.read,RouteCode.read,eqn,
    List.map_ofFn,Function.comp_def]

private def readScalar (S : Schema R B) (x : Pins R B d → Bool) (r : R) (j : ℕ) :=
  if h : j<(S.tags r).length then S.scalar x r ⟨j,h⟩ else 0

/-- The stored scalar field, or the shared final anchor offset. Final absolute
binding rows ignore the offset inputs. Inactive anchor operands can be zero. -/
def scalarArgs (S : Schema R B) (L : Schema U V) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (off box : Fin a → ℕ) (row : Slot a R U) : Field cap → ℕ
  | .inl b => (siteOf x y row).elim 0 (if b then box else off)
  | .inr j => match row with
    | .inr (some (.inl r)) => readScalar S x r j.val
    | .inr (some (.inr u)) => readScalar L y u j.val
    | _ => 0

private theorem decoded (S : Schema R B) (x : Pins R B d → Bool) (r : R) (sh : (S.tags r).length≤cap)
    (v : Field cap → ℕ) (vals : ∀ i : Fin (S.tags r).length, v (pin _ sh i) = S.scalar x r i) :
    (Stored.fromTags (S.tags r) (pin _ sh)).read v = S.typed x r := by
  apply code_congr
  intro j
  by_cases h : j<(S.tags r).length <;> simp [Stored.fieldOf,h,WidthExpr.eval,vals]

/-- Direct numeric interpretation of every static slot in the true history
template. It is defined for inactive slots as well as live ones. -/
def rowRecords (S : Schema R B) (L : Schema U V) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (off box : Fin a → ℕ) : Slot a R U → List Record
  | .inl _ | .inr none => []
  | .inr (some (.inl r)) => [((S.typed x r).shift ((name a x r).elim 0 off)).rebaseBox ((name a x r).elim 0 box)]
  | .inr (some (.inr u)) => [L.typed y u]

/-- Every native piece's geometry format has exactly its actual stored values.
All the old arithmetic intermediate operands were eliminated by freezing the row. -/
theorem format_read (S : Schema R B) (L : Schema U V) (sh : ∀ r, (S.tags r).length≤cap)
    (lh : ∀ u, (L.tags u).length≤cap) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (off box : Fin a → ℕ) (r : Slot a R U) :
    (format S L sh lh r).map (RecordCode.read (scalarArgs S L x y off box r)) = rowRecords S L x y off box r := by
  rcases r with j | _ | r | u
  · rfl
  · rfl
  · have hr : (Stored.fromTags (S.tags r) (pin _ (sh r))).read
        (scalarArgs S L x y off box (.inr (some (.inl r)))) = S.typed x r :=
      decoded S x r _ _ (fun i => by simp [scalarArgs,pin,readScalar,i.isLt])
    simp only [format,List.map_cons,List.map_nil,RecordCode.placed_read,hr,rowRecords,WidthExpr.eval,scalarArgs,siteOf,
      Bool.false_eq_true,ite_false,ite_true]
  · have hu : (Stored.fromTags (L.tags u) (pin _ (lh u))).read
        (scalarArgs S L x y off box (.inr (some (.inr u)))) = L.typed y u :=
      decoded L y u _ _ (fun i => by simp [scalarArgs,pin,readScalar,i.isLt])
    simp only [format,List.map_cons,List.map_nil,hu,rowRecords]

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
