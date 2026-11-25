import OAI.ThreeFlat.Diagonal.HistoryPortBit
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Physical tick pin addresses in the inherited local order -/

namespace ThreeFlat.Diagonal.HistoryContraction.PortLayout

noncomputable section
open MotifBinaryPacking
variable {S : Shape} {Pins F : Type*} [CommSemiring F] {p : ℕ}
    (L : PortLayout S Pins) {R : Rewrite S F} {t : Fin R.count} (W : PortLayout (R.target t) Pins)
    (c : (R.target t).Site → ℕ) (ord : ∀ v, Fin (c v) ≃ {u // R.owner t u = v})

/-- A selected node's external pin-pointer table consists of the individual
children's earlier tables in child order. No heap search is needed to find
the physical endpoint of an inherited old/new pair. -/
def inheritedSources (src : ∀ u, Fin (L.ext u) → Fin p) (v : (R.target t).Site) :
    Fin ((L.inherit W c ord).ext v) → Fin p := fun x =>
  let q : (i : Fin (c v)) × Fin (L.ext (ord v i).val) := finSigmaFinEquiv.symm x
  src (ord v q.1).val q.2

theorem inheritedSources_at (src : ∀ u, Fin (L.ext u) → Fin p) (v : (R.target t).Site)
    (i : Fin (c v)) (j : Fin (L.ext (ord v i).val)) :
    inheritedSources L W c ord src v (L.inheritedIndex W c ord v i j) = src (ord v i).val j := by
  rw [inheritedSources,inheritedIndex,Equiv.symm_apply_apply]

theorem inheritedSources_read (src : ∀ u, Fin (L.ext u) → Fin p) (v : (R.target t).Site)
    (pin : Pins) (x : Fin p → Bool) (agree : ∀ u j, x (src u j) = L.pin u pin j) (i : Fin ((L.inherit W c ord).ext v)) :
    x (inheritedSources L W c ord src v i) = (L.inherit W c ord).pin v pin i := by
  obtain ⟨⟨a,b⟩,rfl⟩ := finSigmaFinEquiv.surjective i
  let y := L.inheritedIndex W c ord v a b
  change x (inheritedSources L W c ord src v y) = (L.inherit W c ord).pin v pin y
  rw [inheritedSources_at,L.inherited_pin]
  exact agree _ _

/-- On the terminal pass the pointer stream of the external endpoints and
the shared final edge-word pointers form a single map into the physical task. -/
def physicalSource (ext : ∀ u, Fin (L.ext u) → Fin p) (edge : ∀ e, Fin (L.width e) → Fin p)
    (u : S.Site) : Fin (L.form.width u) → Fin p := Fin.append (ext u) (fun z =>
  let q : (i : Fin (L.count u)) × Fin (L.lengths u i) := finSigmaFinEquiv.symm z
  edge (L.port u q.1).1.1 q.2)

theorem physicalSource_read (ext : ∀ u, Fin (L.ext u) → Fin p) (edge : ∀ e, Fin (L.width e) → Fin p)
    (u : S.Site) (pin : Pins) (x : Fin p → Bool) (b : S.Half u)
    (endpoints : ∀ j, x (ext u j) = L.pin u pin j)
    (wires : ∀ a : S.graph.Port u, ∀ j, x (edge a.1.1 j) = L.binary a.1.1 (b a) j) :
    ∀ z, x (physicalSource L ext edge u z) = L.form.read u pin b z := by
  refine Fin.addCases (fun j => ?_) (fun z => ?_)
  · simpa [physicalSource,form] using endpoints j
  · let addr (k : Fin (L.halfBits u)) : Fin p :=
      let q : (i : Fin (L.count u)) × Fin (L.lengths u i) := finSigmaFinEquiv.symm k
      edge (L.port u q.1).1.1 q.2
    let q : (i : Fin (L.count u)) × Fin (L.lengths u i) := finSigmaFinEquiv.symm z
    have hw : x (addr z) = L.encode u b z := wires (L.port u q.1) q.2
    exact ((congrArg x (Fin.append_right (ext u) addr z)).trans hw).trans
      (Fin.append_right (L.pin u pin) (L.encode u b) z).symm

theorem physicalSource_eval (ext : ∀ u, Fin (L.ext u) → Fin p) (edge : ∀ e, Fin (L.width e) → Fin p)
    (u : S.Site) (pin : Pins) (x : Fin p → Bool) (b : S.Half u) (T : BitNetwork F (L.form.width u))
    (endpoints : ∀ j, x (ext u j) = L.pin u pin j)
    (wires : ∀ a : S.graph.Port u, ∀ j, x (edge a.1.1 j) = L.binary a.1.1 (b a) j) :
    (T.restrictPins (some ∘ physicalSource L ext edge u)).eval x = T.eval (L.form.read u pin b) := by
  rw [BitNetwork.restrictPins_eval]
  apply congrArg T.eval
  funext z
  simpa using physicalSource_read L ext edge u pin x b endpoints wires z

end
end ThreeFlat.Diagonal.HistoryContraction.PortLayout

end OAI
