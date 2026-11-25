import OAI.Hierarchy.TaggedWireRowGraph

namespace OAI
/-! # Reindexing directed walks onto their sorted physical chords -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators

variable {S : ℕ} {E D : Type}

theorem reversed [Fintype E] (G : PortGraph (Fin S) E) {a b : Fin S} {xs : List E}
    (ok : Traverses G a xs b) : Traverses G b xs.reverse a := by
  classical
  let : Nonempty (Fin S) := ⟨a⟩
  induction ok with
  | nil a=>exact .nil a
  | forward e p ih =>
    simpa only [List.reverse_cons] using
      (Traverses.append (G:=G) ih (Traverses.backward (G:=G) e (.nil (G.tail e))))
  | backward e p ih =>
    simpa only [List.reverse_cons] using
      (Traverses.append (G:=G) ih (Traverses.forward (G:=G) e (.nil (G.head e))))

/-- The native port ledger may list either endpoint first, independently per row. -/
theorem unordered_walk (G : PortGraph (Fin S) E) (H : PortGraph (Fin S) D) (edge : E→D)
    (ends : ∀e,(H.tail (edge e)=G.tail e ∧ H.head (edge e)=G.head e) ∨
      (H.tail (edge e)=G.head e ∧ H.head (edge e)=G.tail e)) {a b : Fin S}
    {xs : List E} (ok : Traverses G a xs b) : Traverses H a (xs.map edge) b := by
  induction ok with
  | nil a=>exact .nil a
  | forward e _ ih=>
    rcases ends e with h|h
    · simpa only [List.map_cons,h.1] using (Traverses.forward (G:=H) (edge e) (by simpa only [h.2] using ih))
    · simpa only [List.map_cons,h.2] using (Traverses.backward (G:=H) (edge e) (by simpa only [h.1] using ih))
  | backward e _ ih=>
    rcases ends e with h|h
    · simpa only [List.map_cons,h.2] using (Traverses.backward (G:=H) (edge e) (by simpa only [h.1] using ih))
    · simpa only [List.map_cons,h.1] using (Traverses.forward (G:=H) (edge e) (by simpa only [h.2] using ih))

def oriented (a b : Fin S) (xs : List E) := if a<b then xs else xs.reverse

theorem oriented_walk [Fintype E] (G : PortGraph (Fin S) E) (a b : Fin S) (different : a≠b)
    (xs : List E) (ok : Traverses G a xs b) :
    Traverses G (orderedChord a b different).1.1 (oriented a b xs) (orderedChord a b different).1.2 := by
  by_cases h:a<b
  · simpa [orderedChord,oriented,h] using ok
  · simpa [orderedChord,oriented,h] using reversed G ok

@[simp] theorem oriented_count [BEq E] [LawfulBEq E] (a b : Fin S) (xs : List E) (e : E) :
    (oriented a b xs).count e=xs.count e := by
  unfold oriented
  split <;> simp

end Hierarchy.WireTelescope

end
end OAI
