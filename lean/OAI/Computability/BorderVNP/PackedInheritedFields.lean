import OAI.Computability.BorderVNP.PackedInheritedState
import OAI.Computability.BorderVNP.PackedBankPacket

/-! # Address and directory tags on frozen site-local packet words

The public site history marks precisely the fields to be relocated. A final
pass adds the site's absolute bit offset or its merged one-copy directory
offset to those words. Other scalar fields are copied verbatim. The tag order
is fixed by the sparse record schema, including all routes in a profile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse BankPacket Word

/-- Whether a stored public word is copied, shifted in the local bit bank, or
shifted in the merged one-copy box directory. -/
inductive Kind where | plain | bitAddress | boxID
  deriving DecidableEq

/-- Execute the relocation designated for one stored word. -/
def Kind.move (offset boxOffset : ℕ) : Kind → ℕ → ℕ
  | .plain,n => n
  | .bitAddress,n => offset+n
  | .boxID,n => boxOffset+n

private def plain (xs : List ℕ) := xs.map (fun n => (Kind.plain,n))

private def port (p : Port) : List (Kind × ℕ) :=
  [(.bitAddress,p.base),(.plain,p.copyStride),(.plain,p.laneStride)]

private def route (r : Route) : List (Kind × ℕ) := plain [r.term,r.lanes] ++ port r.original ++ port r.compact

/-- Annotate the actual packet fields of one frozen local row. -/
def marked : Record → List (Kind × ℕ)
  | .zero n w p => plain [0,n,w] ++ port p
  | .equal n w p q => plain [1,n,w] ++ port p ++ port q
  | .box i b n d => [(.plain,2),(.boxID,i),(.bitAddress,b),(.plain,n),(.plain,d)]
  | .profile n s w h rs => plain [3,n] ++ port s ++ plain [w] ++ plain (h.length :: h) ++
      ((.plain,rs.length) :: rs.flatMap route)

private theorem plain_move (off id : ℕ) (xs : List ℕ) :
    (plain xs).map (fun w => w.1.move off id w.2) = xs := by
  simp [plain,List.map_map,Function.comp_def,Kind.move]

private theorem route_move (off id : ℕ) (r : Route) :
    (route r).map (fun w => w.1.move off id w.2) = Packet.route (r.shift off) := rfl

/-- The final address pass writes the exact canonical words of the relocated row. -/
theorem marked_move (off id : ℕ) (r : Record) :
    (marked r).map (fun w => w.1.move off id w.2) = Packet.record ((r.shift off).rebaseBox id) := by
  cases r with
  | zero | equal | box => rfl
  | profile n s w h rs =>
    simp only [marked,Record.shift,Record.rebaseBox,Packet.record,Packet.fieldList,Packet.vector,
      List.map_append,List.map_cons,plain_move,List.map_flatMap,List.flatMap_map,List.length_map]
    congr 2

/-- All stored site blocks carry their own relocation information, independent of which
final cell receives the site. -/
def Site.markedWords (s : Site) := s.rows.flatMap marked

/-- Applying the scalar relocator to the flattened history gives precisely the body's
actual tagged packet payload, in its stable observation order. -/
theorem Site.markedWords_move (s : Site) (off id : ℕ) :
    s.markedWords.map (fun w => w.1.move off id w.2) = (s.placedRows off id).flatMap Packet.record := by
  simp only [Site.markedWords,Site.placedRows,List.map_flatMap,List.flatMap_map]
  apply List.flatMap_congr
  intro r _
  exact marked_move off id r

/-- Growing the retained history preserves all prior marked words and appends only
the concrete new interval descriptors. -/
theorem Site.markedWords_retain (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).markedWords = s.markedWords ++ cuts.flatMap (marked ∘ Slice.record s) := by
  simp only [Site.markedWords,Site.retain_rows,List.flatMap_append,List.flatMap_map,Function.comp_def]

/-- Number of frozen public words added by an interval layer. -/
theorem Site.markedWords_growth (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).markedWords.length = s.markedWords.length + 9*cuts.length := by
  rw [s.markedWords_retain,List.length_append,List.length_flatMap]
  change _ + (cuts.map (fun _ => 9)).sum = _
  simp [Nat.mul_comm]

variable {I : Type*}

private def rawCode (xs : List (WidthExpr I)) := xs.map (fun v => (Kind.plain,v))

private def portCode (p : PortCode I) : List (Kind × WidthExpr I) :=
  [(.bitAddress,p.base),(.plain,p.copyStride),(.plain,p.laneStride)]

private def routeCode (r : RouteCode I) : List (Kind × WidthExpr I) :=
  rawCode [r.term,r.lanes] ++ portCode r.original ++ portCode r.compact

/-- Tags and expressions emitted by the same circuit that creates a seed packet. -/
def markedCode : RecordCode I → List (Kind × WidthExpr I)
  | .zero n w p => rawCode [.const 0,n,w] ++ portCode p
  | .equal n w s t => rawCode [.const 1,n,w] ++ portCode s ++ portCode t
  | .box i b n d => [(.plain,.const 2),(.boxID,i),(.bitAddress,b),(.plain,n),(.plain,d)]
  | .profile n s w h rs => rawCode [.const 3,n] ++ portCode s ++ rawCode [w] ++
      rawCode (.const h.length :: h) ++ ((.plain,.const rs.length) :: rs.flatMap routeCode)

/-- The compiled seed packet's plain numeric operands are exactly the projection of
the frozen, tagged program. -/
theorem markedCode_words (r : RecordCode I) : (markedCode r).map Prod.snd = r.words := by
  cases r with
  | zero | equal | box => rfl
  | profile n s w h rs =>
    simp only [markedCode,RecordCode.words,rawCode,List.map_append,List.map_map,Function.comp_def,
      List.map_cons,List.map_nil,List.map_flatMap]
    congr 2
    simp

/-- Evaluating the annotated program produces exactly the tags of the real local record.
Thus a previously generated seed site can later be retained without reparsing a private box. -/
theorem markedCode_eval (r : RecordCode I) (x : I → ℕ) :
    (markedCode r).map (fun w => (w.1,w.2.eval x)) = marked (r.read x) := by
  cases r with
  | zero | equal | box => rfl
  | profile n s w h rs =>
    simp only [markedCode,RecordCode.read,marked,plain,rawCode,List.map_append,List.map_map,
      List.map_cons,List.map_nil,List.map_flatMap,List.flatMap_map,List.length_map,Function.comp_def,WidthExpr.eval]
    congr 2

end Packing.Inherited

end BorderVNP
end Computability
end OAI
