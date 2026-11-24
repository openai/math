import OAI.Computability.VPVNP.DegreeRefreshStep
import OAI.Computability.VPVNP.DegreeRefreshPayloads
import OAI.Computability.VPVNP.DegreeRefreshPorts
import OAI.Computability.VPVNP.NetworkIso

/-!
# The degree refresh on the actual lifted slots

The blockwise contraction uses source-port order within each bundle. The
isomorphisms below restore the original and refreshed slot coordinates,
including their lane translations, without identifying parallel arcs. The
actual widths are those charged to equation (7.3).
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

open NetworkKernel

variable {V H L : Type} {D dH d₀ : ℕ}

/-- The word network on a lifted graph. Its edges are actual outgoing slots,
and widths are indexed by a base arc and source lane. -/
noncomputable def actualWireGraph {U K : Type} [Fintype U] [Fintype K] [AddCommGroup K]
    {d : ℕ} (G : LiftedSlots U d K) (w : (U × Fin d) × K → ℕ) : Network where
  Site := U × K
  siteFintype := inferInstance
  Edge := (U × K) × Fin d
  edgeFintype := inferInstance
  src := Prod.fst
  dst e := (G.actualGraph.target e).1
  Payload e := Word (w ((e.1.1,e.2),e.1.2))
  payloadFintype _ := inferInstance

/-- Old positions in bundle coordinates have their original port as the
last component, separate from the remaining lane. -/
def originalSites (port : H ≃ Fin D) : (V × L) × Fin D ≃ V × (H × L) where
  toFun p := (p.1.1,port.symm p.2,p.1.2)
  invFun p := ((p.1,p.2.2),port p.2.1)
  left_inv _ := by simp
  right_inv _ := by simp

/-- Restore the outgoing slot number and the source lane of an individual
old segment. -/
def originalEdges (port : H ≃ Fin D) : Arc (V × L) D ≃ (V × (H × L)) × Fin D where
  toFun p := (originalSites port (source p),p.1.2)
  invFun p := (((p.1.1,p.1.2.2),p.2),port p.1.2.1)
  left_inv _ := by simp [originalSites, source]
  right_inv _ := by simp [originalSites, source]

/-- The regrouped old width is exactly the field carried by the original
arc in its original lane. -/
abbrev groupedWidths (port : H ≃ Fin D) (w : (V × Fin D) × (H × L) → ℕ) :
    Arc (V × L) D → ℕ := Function.uncurry (DegreeRefresh.bundleWidths port w)

variable [Fintype V] [Fintype H] [Fintype L] [AddCommGroup H] [AddCommGroup L]
  (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D) (w : (V × Fin D) × (H × L) → ℕ)

/-- Reindex the old wire tensor by its actual directed slots. Both endpoint
maps and the full alphabet on every arc are preserved. -/
noncomputable def originalIso :
    Network.Iso (oldWireGraph (oldPortMatching G port) (groupedWidths port w))
      (actualWireGraph G w) where
  site := originalSites port
  edge := originalEdges port
  src _ := rfl
  dst := by
    rintro ⟨⟨⟨v,l⟩,i⟩,j⟩
    change originalSites port (source (oldPortMatching G port (((v,l),i),j))) = _
    rw [oldPortMatching_apply]
    simp [originalSites, source, actualWireGraph, originalEdges]
    rfl
  payload _ := Equiv.refl _

/-- Promote the port to part of the new base vertex while retaining the
remaining lane. -/
def promotedSites : (V × L) × Fin D ≃ (V × Fin D) × L where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def outputClasses :
    OutputEdge (V × L) (Fin D × Fin dH) D (d₀ - (dH + 1)) ≃
      ((V × L) × Fin D) × RefreshSlot dH d₀ where
  toFun
    | .inl p => (p,.inl 0)
    | .inr (.inl (s,j,h)) => ((s,j),.inr (.inl h))
    | .inr (.inr (p,h)) => (p,.inr (.inr h))
  invFun
    | (p,.inl _) => .inl p
    | ((s,j),.inr (.inl h)) => .inr (.inl (s,j,h))
    | (p,.inr (.inr h)) => .inr (.inr (p,h))
  left_inv e := by rcases e with p | ⟨s,j,h⟩ | ⟨p,h⟩ <;> rfl
  right_inv p := by
    rcases p with ⟨p,h | h | h⟩
    · cases Subsingleton.elim h 0
      rfl
    · rfl
    · rfl

/-- All copies of the grouped external, expander and cyclic padding arcs
biject with the numbered outgoing slots of the refreshed graph. -/
def promotedEdges (hd : dH + 1 ≤ d₀) :
    OutputEdge (V × L) (Fin D × Fin dH) D (d₀ - (dH + 1)) ≃ ActualArc V L D d₀ :=
  outputClasses.trans (arcCoordinates hd).symm

variable (P : SlotGraph (Fin D) dH) (hD : 1 < D) (hd : dH + 1 ≤ d₀)

/-- The grouped output is isomorphic to the actual lifted graph with the
widths charged in (7.3). The selected motif may use any alphabet with the
specified word encoding at each expander slot. -/
noncomputable def promotedIso (A : (V × L) → Fin D × Fin dH → Type)
    [∀ s e, Fintype (A s e)] (internal : (V × L) → Fin D × Fin dH → ℕ)
    (encode : ∀ s e, A s e ≃ Word (internal s e)) :
    Network.Iso
      (refreshOutput (bundleTarget G) (groupedWidths port w) Prod.fst (fun e ↦ (P.target e).1)
        A (d₀ - (dH + 1)))
      (actualWireGraph (degreeRefresh G P hD hd) (DegreeRefresh.actualWidths hd port w internal)) where
  site := promotedSites
  edge := promotedEdges hd
  src e := by rcases e with p | ⟨s,j,k⟩ | ⟨p,k⟩ <;> rfl
  dst := by
    rintro (⟨⟨v,l⟩,j⟩ | ⟨⟨v,l⟩,j,k⟩ | ⟨⟨⟨v,l⟩,j⟩,k⟩)
    · exact congrArg Prod.fst (degreeRefresh_external G P hD hd (v,j) l).symm
    · exact congrArg Prod.fst (degreeRefresh_internal G P hD hd v j l k).symm
    · exact congrArg Prod.fst (degreeRefresh_padding G P hD hd v j l k).symm
  payload := by
    rintro (p | ⟨s,j,k⟩ | ⟨p,k⟩)
    · change Word (∑ j, groupedWidths port w (p,j)) ≃
        Word (DegreeRefresh.newWidths hd (DegreeRefresh.bundleWidths port w) internal p
          (refreshSlots hd (.inl 0)))
      simpa [DegreeRefresh.newWidths] using Equiv.refl (Word (∑ j, groupedWidths port w (p,j)))
    · change A s (j,k) ≃ Word (DegreeRefresh.newWidths hd (DegreeRefresh.bundleWidths port w)
        internal (s,j) (refreshSlots hd (.inr (.inl k))))
      simpa [DegreeRefresh.newWidths] using encode s (j,k)
    · change Word 0 ≃ Word (DegreeRefresh.newWidths hd (DegreeRefresh.bundleWidths port w)
        internal p (refreshSlots hd (.inr (.inr k))))
      simpa [DegreeRefresh.newWidths] using Equiv.refl (Word 0)

open WireTensor

variable {R : Type*} [CommSemiring R] {I : (V × L) → Type} [∀ s, Fintype (I s)]
  (A : (s : V × L) → I s → Fin D × Fin dH → Type) [∀ s i e, Fintype (A s i e)]
  (internal : (s : V × L) → I s → Fin D × Fin dH → ℕ)
  (encode : ∀ s i e, A s i e ≃ Word (internal s i e))
  (M : ∀ s (i : I s) j, (internalDemand R (oldPortMatching G port) (groupedWidths port w) s).Basis j →
    (blockSupply (R := R) Prod.fst (fun e ↦ (P.target e).1) A s i).Basis j → R)
  (h : ∀ s, (internalDemand R (oldPortMatching G port) (groupedWidths port w) s).coeff =
    ∑ i, applyLocal (M s i) (blockSupply (R := R) Prod.fst (fun e ↦ (P.target e).1) A s i).coeff)

/-- The exact degree-refresh step on actual slot coordinates, with one
motif choice per block and the selected word widths on the refreshed graph. -/
noncomputable def actualRefreshStep : Step R (actualWireGraph G w) :=
  let step := refreshStep (bundleTarget G) (groupedWidths port w) Prod.fst
    (fun e ↦ (P.target e).1) (d₀ - (dH + 1)) (oldPortMatching G port)
    (oldPortMatching_bundle G port) A M h
  step.reindex (originalIso G port w)
    (out := fun c ↦ actualWireGraph (degreeRefresh G P hD hd)
      (DegreeRefresh.actualWidths hd port w (fun s ↦ internal s (c s))))
    (fun c ↦ promotedIso G port w P hD hd (fun s ↦ A s (c s)) (fun s ↦ internal s (c s))
      (fun s ↦ encode s (c s)))

/-- In each branch the output network uses the stated refreshed slot graph
and its corresponding actual widths. -/
theorem actualRefreshStep_output (c : (s : V × L) → I s) :
    ((actualRefreshStep G port w P hD hd A internal encode M h).term c).output =
      actualWireGraph (degreeRefresh G P hD hd)
        (DegreeRefresh.actualWidths hd port w (fun s ↦ internal s (c s))) := rfl

/-- Each original vertex factor stays whole at the same physical position
after promoting its port to a base label. -/
theorem actualRefreshStep_place (c : (s : V × L) → I s) (x : V × (H × L)) :
    ((actualRefreshStep G port w P hD hd A internal encode M h).term c).place x =
      refreshPositions port x := rfl

end Compression.Refresh

end VPVNP
end Computability
end OAI
