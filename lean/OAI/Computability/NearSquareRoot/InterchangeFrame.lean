import OAI.Computability.NearSquareRoot.InterchangeAddress
import OAI.Computability.IntegerMultiplication.Spindle.Frame

/-!
# Cutting a variable-width interchange address into equal recursive fields

A leading group and trailing remainder fit around the ordered recursive
fields on each wing. All views tabulate the same bytes. In particular the
spectators in the gap may have arbitrary dimensions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeFrame

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom IntegerMultiplication.Spindle

variable {J : Type} {n : ℕ} (ord : J ≃ Fin n) (b h f t : ℕ)

abbrev middle := threads (line b f) ord
abbrev piece := Board (field b h) (middle ord b f) (field b t)
abbrev value := Block b h × (J → Block b f) × Block b t
abbrev width := h + (n * f + t)

/-- The same ordered bits occupy the whole radix word, at arbitrary width. -/
noncomputable def pack : Adopt (piece ord b h f t) (line b (width (n:=n) h f t)) := by
  have hmid : Nonempty (Adopt (middle ord b f) (line b (n*f))) := by
    unfold line
    rw [← rack_eq]
    exact ⟨undye (line b f) ord (Adopt.same _)⟩
  let low := ((Classical.choice hmid).split (Adopt.same (line b t))).thenDo
    (fPlus b (n*f) t)
  exact ((Adopt.same (line b h)).split low).thenDo (fPlus _ _ _)

variable (P G B : Dims.Tape)
abbrev expanded := Path P (piece ord b h f t) G (piece ord b h f t) B
abbrev address := SpanKey P G B (value (J:=J) b h f t)

noncomputable def parent :
    Adopt (expanded ord b h f t P G B) (stock b P G B (width (n:=n) h f t)) :=
  let u := pack ord b h f t
  (Adopt.same _).split (u.split ((Adopt.same _).split (u.split (Adopt.same _))))

abbrev pre := P ++ field b h
abbrev gap := field b t ++ (G ++ field b h)
abbrev post := field b t ++ B

/-- The two equal-width collections are the middle of the expanded fields.
The outer address and all leading/trailing coordinates join the spectators. -/
def axis :
    Axis (expanded ord b h f t P G B) (pre b h P) (middle ord b f)
      (gap b h t G) (middle ord b f) (post b t B) :=
  let slot : Slot (piece ord b h f t) (field b h) (middle ord b f) (field b t) :=
    ⟨Adopt.same _⟩
  let right := (slot.exit (Adopt.same (layout B))).enter (Adopt.same (layout G))
  (Axis.both slot right).enter (Adopt.same (layout P))

def leading (z : address (J:=J) b h f t P G B) : address (J:=J) b h f t P G B :=
  (z.1,(z.2.2.2.1.1,z.2.1.2),z.2.2.1,(z.2.1.1,z.2.2.2.1.2),z.2.2.2.2)

def center (z : address (J:=J) b h f t P G B) : address (J:=J) b h f t P G B :=
  (z.1,(z.2.1.1,z.2.2.2.1.2.1,z.2.1.2.2),z.2.2.1,
    (z.2.2.2.1.1,z.2.1.2.1,z.2.2.2.1.2.2),z.2.2.2.2)

def trailing (z : address (J:=J) b h f t P G B) : address (J:=J) b h f t P G B :=
  (z.1,(z.2.1.1,z.2.1.2.1,z.2.2.2.1.2.2),z.2.2.1,
    (z.2.2.2.1.1,z.2.2.2.1.2.1,z.2.1.2.2),z.2.2.2.2)

private def wings {X Y : Type} {x : Series X} {y : Series Y} {D E : Dims.Tape}
    (side : Slot x D y E) :
    Axis (Path P x G x B) (P ++ D) y (E ++ (G ++ D)) y (E ++ B) :=
  (Axis.both side ((side.exit (Adopt.same (layout B))).enter (Adopt.same (layout G)))).enter
    (Adopt.same (layout P))

private theorem wings_swapped {X Y : Type} {x : Series X} {y : Series Y} {D E : Dims.Tape}
    (side : Slot x D y E) (z : SpanKey P G B X) :
    (wings P G B side).view.cast
      (z.1,side.alter z.2.1 (side.read z.2.2.2.1),z.2.2.1,
        side.alter z.2.2.2.1 (side.read z.2.1),z.2.2.2.2) =
      swapper _ _ _ ((wings P G B side).view.cast z) := by
  let a := wings P G B side
  have e := a.changed z ((a.pair z).2,(a.pair z).1)
  change _ = swapper _ _ _ (a.view.cast z)
  rw [← show a.bridge z ((a.pair z).2,(a.pair z).1) =
      (z.1,side.alter z.2.1 (side.read z.2.2.2.1),z.2.2.1,
        side.alter z.2.2.2.1 (side.read z.2.1),z.2.2.2.2) by
    rcases z with ⟨u, v, g, w, k⟩
    simp [a,wings]]
  exact e

private def firstSlot : Slot (piece ord b h f t) [] (line b h)
    ([] ++ (Rack (field b f) n ++ field b t)) :=
  let low := ((undye (line b f) ord (Adopt.same _)).split
    (Adopt.same (line b t))).thenDo (unite _ _)
  (Slot.sole (line b h)).exit low

private def lastSlot : Slot (piece ord b h f t) (field b h ++ (Rack (field b f) n ++ []))
    (line b t) [] :=
  ((Slot.sole (line b t)).enter (undye (line b f) ord (Adopt.same _))).enter
    (Adopt.same (line b h))

def leadingAxis := wings P G B (firstSlot ord b h f t)
def trailingAxis := wings P G B (lastSlot ord b h f t)

theorem leading_cast (z : address (J:=J) b h f t P G B) :
    (leadingAxis ord b h f t P G B).view.cast (leading b h f t P G B z) =
      swapper _ _ _ ((leadingAxis ord b h f t P G B).view.cast z) := by
  rcases z with ⟨p, ⟨lh, lc, lt⟩, g, ⟨rh, rc, rt⟩, s⟩
  simpa [leadingAxis,firstSlot,leading] using wings_swapped P G B (firstSlot ord b h f t)
    (p,(lh,lc,lt),g,(rh,rc,rt),s)

theorem trailing_cast (z : address (J:=J) b h f t P G B) :
    (trailingAxis ord b h f t P G B).view.cast (trailing b h f t P G B z) =
      swapper _ _ _ ((trailingAxis ord b h f t P G B).view.cast z) := by
  rcases z with ⟨p, ⟨lh, lc, lt⟩, g, ⟨rh, rc, rt⟩, s⟩
  simpa [trailingAxis,lastSlot,trailing] using wings_swapped P G B (lastSlot ord b h f t)
    (p,(lh,lc,lt),g,(rh,rc,rt),s)

theorem center_cast (z : address (J:=J) b h f t P G B) :
    (axis ord b h f t P G B).view.cast (center b h f t P G B z) =
      swapper _ _ _ ((axis ord b h f t P G B).view.cast z) := rfl

theorem parent_cast (z : address (J:=J) b h f t P G B) :
    (parent ord b h f t P G B).cast
      (leading b h f t P G B (center b h f t P G B (trailing b h f t P G B z))) =
      swapper P G B ((parent ord b h f t P G B).cast z) := rfl

end InterchangeFrame

end NearSquareRoot
end Computability
end OAI
