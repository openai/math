import OAI.Computability.BorderVNP.CellPacketGeometryRecordPositions
import OAI.Computability.BorderVNP.PackedFrozenTapeRows

/-! # Recovering complete typed site programs from the actual frozen history image -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open CellSparse BankPacket Word ParseBatchSort
variable {R B V I : Type*} {d : ℕ}

/-- Native record slots selected by their actual enable and owner, in the
same chronological order as the immutable source rectangle. -/
def Schema.selected (S : Schema R B) (x : Pins R B d → Bool) (k : ℕ) : List R :=
  S.rows.filter fun r => x (.inl (r,.inl ())) && decide (owner x r=k)

/-- The selected real records are precisely the stored image of this site. -/
theorem Schema.selected_read (S : Schema R B) (x : Pins R B d → Bool) (k : ℕ) :
    (S.selected x k).map (S.read x) = S.atSite x k := by
  unfold Schema.selected Schema.atSite
  generalize S.rows = xs
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    cases h : x (.inl (r,.inl ())) <;> by_cases live : owner x r=k <;> simp [h,live,ih]

/-- One physical source scalar of the history's stored numerical tape. -/
def Schema.scalar (S : Schema R B) (x : Pins R B d → Bool) (r : R) (i : Fin (S.tags r).length) :=
  value fun j => x (.inr (S.pin r i j))

/-- The actual fixed typed record decoded on these numerical source operands. -/
def Schema.typed (S : Schema R B) (x : Pins R B d → Bool) (r : R) : Record :=
  (Stored.fromTags (S.tags r) id).read (S.scalar x r)

private theorem map_pair {A Q U : Type*} (f : R → A) (g : Q → A) (p : R → U) (q : Q → U)
    (h : ∀ a b, f a=g b → p a=q b) (xs : List R) (ys : List Q)
    (equal : xs.map f=ys.map g) : xs.map p=ys.map q := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at equal
    | cons b ys =>
      simp only [List.map_cons,List.cons.injEq] at equal ⊢
      exact ⟨h a b equal.1,ih ys equal.2⟩

/-- A true selected tagged row section determines its entire typed record list. -/
theorem Schema.typed_section (S : Schema R B) (x : Pins R B d → Bool) (key : ℕ) (rows : List Record)
    (physical : S.atSite x key = rows.map marked) : (S.selected x key).map (S.typed x) = rows := by
  have reads := (S.selected_read x key).trans physical
  simpa only [List.map_id] using
    map_pair (S.read x) marked (S.typed x) id
      (fun r a h => Stored.fromTags_read (S.tags r) id (S.scalar x r) a h) _ _ reads

/-- The complete program of every live site is read from the literal history
output, including all prior birth, terminal-hook, retained and subdivision rows.
The image assumption is the one proved inductively by the shared tape producer. -/
theorem Schema.typed_atSite (S : Schema R B) (x : Pins R B d → Bool) (names : V ↪ ℕ)
    (states : V → Site) (image : S.Image x names states) (v : V) :
    (S.selected x (names v)).map (S.typed x) = (states v).rows := by
  exact S.typed_section x (names v) _ (image.records v)

/-- The actual typed row section after final physical bit and merged-box prefixes
are applied to every historical row of this site. -/
theorem Schema.placed_atSite (S : Schema R B) (x : Pins R B d → Bool) (names : V ↪ ℕ)
    (states : V → Site) (image : S.Image x names states) (v : V) (off idx : ℕ) :
    (S.selected x (names v)).map (fun r => ((S.typed x r).shift off).rebaseBox idx) =
      (states v).placedRows off idx := by
  rw [Site.placedRows,←S.typed_atSite x names states image v]
  simp only [List.map_map,Function.comp_def]

/-- The per-row typed geometry formula may use any finite shared scalar alphabet.
Only true immutable numerical fields and the two final prefixes enter this computation. -/
theorem Schema.placed_code (S : Schema R B) (x : Pins R B d → Bool) (r : R) (pin : Fin (S.tags r).length → I)
    (args : I → ℕ) (off idx : WidthExpr I) (scalar : ∀ j, args (pin j)=S.scalar x r j)
    (a : Record) (trueRow : S.read x r = marked a) :
    ((Stored.fromTags (S.tags r) pin).placed off idx).read args = (a.shift (off.eval args)).rebaseBox (idx.eval args) := by
  rw [RecordCode.placed_read]
  have data : List.ofFn (fun j : Fin (S.tags r).length => ((S.tags r)[j.val],args (pin j))) = marked a := by
    simp only [scalar]
    exact trueRow
  rw [Stored.fromTags_read (S.tags r) pin args a data]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
