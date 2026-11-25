import OAI.Computability.BorderVNP.CubeScatterAssignmentViews
import OAI.Computability.BorderVNP.CubeScatterVisits

/-! # Directed group views owning the private bits of a selected packet row

The two views of an increasing pair have distinct first symbols. A private
demand end or a non-cut supply belongs to the view at its own vertex. A
same-symbol singleton belongs to the repeated-symbol view. These addresses
are defined before mapping symbols to teams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.VertexIndex

variable {n d blocks b h K s : ℕ} {select : Packet n d blocks → Selector n K h}

/-- Directed endpoint view of a strict unordered symbol pair. -/
def symbolView (pair : Symbols d) (high : Bool) : Fin d × Fin d :=
  if high then (pair.val.2,pair.val.1) else pair.val

/-- The packet and side of a genuine private packet bit. A cut bit is carried
on the common stream and therefore has no private packet view. -/
def packetBitView (i : Fin (n+1)) : Assignment.BitIndex b s select → Option (Packet n d blocks × Bool)
  | .inl _ => none
  | .inr (.inl (p,e,_)) => some (p,cornerBits p (Assignment.endVertex e) i)
  | .inr (.inr ⟨p,e,_⟩) => if e.2 = i then none else some (p,cornerBits p e.1 i)

/-- Directed scan address of any private key, including diagonal singleton slots. -/
def privateView (i : Fin (n+1)) (k : Assignment.BitIndex b s select) : Option (Fin d × Fin d) :=
  match k with
  | .inl z => if z.1.val.1 i = z.1.val.2 i then some (z.1.val.1 i,z.1.val.2 i) else none
  | .inr _ => (packetBitView i k).map (fun ph => symbolView (ph.1.1.1 i) ph.2)

private theorem symbolView_first (pair : Symbols d) (high : Bool) :
    (symbolView pair high).1 = (if high then pair.val.2 else pair.val.1) := by cases high <;> rfl

private theorem symbolView_ne (pair : Symbols d) (high : Bool) :
    (symbolView pair high).1 ≠ (symbolView pair high).2 := by
  cases high <;> first | exact pair.property.ne | exact pair.property.ne'

/-- The numerical order of the two symbols determines both the strict pair and its side. -/
theorem symbolView_inj {a c : Symbols d} {x y : Bool} (eq : symbolView a x = symbolView c y) :
    a = c ∧ x = y := by
  have hf := congrArg Prod.fst eq
  have hs := congrArg Prod.snd eq
  have ha := a.property
  have hc := c.property
  cases x <;> cases y <;> simp only [symbolView,Bool.false_eq_true,ite_false,ite_true] at hf hs ⊢
  · exact ⟨Subtype.ext (Prod.ext hf hs),trivial⟩
  · rw [hf,hs] at ha; exact (hc.not_gt ha).elim
  · rw [hf,hs] at ha; exact (hc.not_gt ha).elim
  · exact ⟨Subtype.ext (Prod.ext hs hf),trivial⟩

/-- The first symbol of the unique directed view has exactly the team prescribed
by the physical assignment. Shared keys satisfy neither side of this equivalence. -/
theorem route_private_iff_view {T : Type*} (i : Fin (n+1)) (owner : Fin d → T)
    (k : Assignment.BitIndex b s select) (team : T) :
    Assignment.route i owner k = .inr team ↔ ∃ v, privateView i k = some v ∧ owner v.1 = team := by
  rcases k with z | (⟨p,e,j⟩|⟨p,e,j⟩)
  · by_cases hz : z.1.val.1 i = z.1.val.2 i <;> simp [Assignment.route,privateView,hz]
  · simp [Assignment.route,privateView,packetBitView,symbolView_first,vertexLabel]
  · by_cases cut : e.2 = i <;> simp [Assignment.route,privateView,packetBitView,cut,symbolView_first,vertexLabel]

/-- Exactly the diagonal singletons can occur in the view of a repeated symbol. -/
theorem privateView_diagonal (i : Fin (n+1)) (k : Assignment.BitIndex b s select) (a : Fin d) :
    privateView i k = some (a,a) ↔
      ∃ z : SingleSlot n d blocks (h*b), k = .inl z ∧ z.1.val.1 i = a ∧ z.1.val.2 i = a := by
  cases k with
  | inl z =>
    by_cases eq : z.1.val.1 i = z.1.val.2 i
    · simp [privateView,eq]
    · simp [privateView,eq]
      intro ha hb
      exact eq (ha.trans hb.symm)
  | inr other =>
    simp only [privateView,Sum.inr_ne_inl,false_and,exists_false,iff_false]
    cases he : packetBitView i (.inr other) with
    | none => simp
    | some ph =>
      simp only [Option.map_some,Option.some.injEq]
      intro e
      exact symbolView_ne (ph.1.1.1 i) ph.2 ((congrArg Prod.fst e).trans (congrArg Prod.snd e).symm)

/-- A key of a strict view has that row's packet and the advertised endpoint side. -/
theorem privateView_strict (i : Fin (n+1)) (k : Assignment.BitIndex b s select) (pair : Symbols d) (high : Bool) :
    privateView i k = some (symbolView pair high) ↔
      ∃ p : Packet n d blocks, p.1.1 i = pair ∧ packetBitView i k = some (p,high) := by
  cases k with
  | inl z =>
    simp [privateView,packetBitView]
    intro equal he
    have left := congrArg Prod.fst he
    have right := congrArg Prod.snd he
    exact symbolView_ne pair high (left.symm.trans (equal.trans right))
  | inr other =>
    simp only [privateView]
    cases e : packetBitView i (.inr other) with
    | none => simp
    | some ph =>
      simp only [Option.map_some,Option.some.injEq]
      constructor
      · intro eq
        obtain ⟨hp,hh⟩ := symbolView_inj eq
        exact ⟨ph.1,hp,Prod.ext rfl hh⟩
      · rintro ⟨p,hrow,hp⟩
        rw [hp]
        exact congrArg (fun sym => symbolView sym high) hrow

end Cube.Scatter

end BorderVNP
end Computability
end OAI
