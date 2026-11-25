import OAI.Hierarchy.TaggedPruneOpen
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths

namespace OAI
/-! # Initial signed-routing state from the literal exposed matching -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open TaggedPrune Catalyst Tagged
open scoped Classical BigOperators

abbrev MatchEdge (h w : ℕ) {k : ℕ} (b : Fin k → ℕ) := (Row h × Fin w) ⊕ Wire b

variable {h w k S : ℕ} {b : Fin k → ℕ} (p : Equiv.Perm (Row h))

/-- Payload edges run from source row `p i` to target row `i`; the catalyst
has an independent bit-edge connecting each of its two exposed ends. -/
def matchEnd : MatchEdge h w b × Bool ≃ RoutingPin h w b where
  toFun
    | (.inl (i,j),false) => .inl ((p i,j),false)
    | (.inl ij,true) => .inl (ij,true)
    | (.inr v,s) => .inr (v,s)
  invFun
    | .inl ((i,j),false) => (.inl (p.symm i,j),false)
    | .inl (ij,true) => (.inl ij,true)
    | .inr (v,s) => (.inr v,s)
  left_inv := by
    rintro ⟨(⟨i,j⟩|v),s⟩ <;> cases s <;> simp
  right_inv := by
    rintro (⟨⟨i,j⟩,s⟩|⟨v,s⟩) <;> cases s <;> simp

def matchGraph (τ : RoutingPin h w b → Fin S) : PortGraph (Fin S) (MatchEdge h w b) where
  tail e := τ (matchEnd p (e,false))
  head e := τ (matchEnd p (e,true))

theorem match_vertex (τ : RoutingPin h w b → Fin S) (e : MatchEdge h w b) (s : Bool) :
    (matchGraph p τ).vertex e s = τ (matchEnd p (e,s)) := by cases s <;> rfl

theorem match_edges {F : Type*} [Field F] (x : RoutingPin h w b → Bool) :
    routingMatch (F:=F) p x =
      if ∀ e : MatchEdge h w b,x (matchEnd p (e,false))=x (matchEnd p (e,true)) then 1 else 0 := by
  have valid : (∀ e : MatchEdge h w b,x (matchEnd p (e,false))=x (matchEnd p (e,true))) ↔
      (∀ v : Wire b,x (.inr (v,false))=x (.inr (v,true))) ∧
      ∀ i : Row h,(fun j : Fin w => x (.inl ((i,j),true))) = (fun j=>x (.inl ((p i,j),false))) := by
    constructor
    · intro eqn
      exact ⟨fun v=>eqn (.inr v),fun i=>funext fun j=>(eqn (.inl (i,j))).symm⟩
    · rintro ⟨cat,data⟩ (⟨i,j⟩|v)
      · exact (congrFun (data i) j).symm
      · exact cat v
  unfold routingMatch
  by_cases cat : ∀v : Wire b,x (.inr (v,false))=x (.inr (v,true))
  · by_cases hw : ∀i : Row h,(fun j : Fin w=>x (.inl ((i,j),true)))=(fun j=>x (.inl ((p i,j),false)))
    · rw [ite_eq_left cat,ite_eq_left hw,ite_eq_left (valid.mpr ⟨cat,hw⟩)]
    · rw [ite_eq_left cat,ite_eq_right hw,ite_eq_right (fun all=>hw (valid.mp all).2)]
  · rw [ite_eq_right cat,ite_eq_right (fun all=>cat (valid.mp all).1)]

/-- Sorting endpoints and combining parallel edges gives the actual common
named-site chord tensor of the exposed ideal at this single permutation. -/
theorem matching_restricts {F : Type*} [Field F] [Nonempty (Fin S)] (τ : RoutingPin h w b → Fin S) :
    ((CorrectionProducts.raw (routingMatch (F:=F) p)).group τ).Restricts
      (raw F ((matchGraph p τ).chordWidths (fun _=>1))) := by
  let G := matchGraph p τ
  let incident (s : Fin S) : G.Port s ≃ {i // τ i=s} :=
    (matchEnd p).subtypeEquiv (fun u => by rw [match_vertex])
  let coords (s : Fin S) := (incident s).symm.arrowCongr finTwoEquiv.symm
  have paired : ((CorrectionProducts.raw (routingMatch (F:=F) p)).group τ).Equivalent
      (G.rawWiring F (fun _=>Fin (2^1))) := by
    apply Raw.reindex_equivalent coords
    intro y
    let x : RoutingPin h w b → Bool := fun i => y (τ i) ⟨i,rfl⟩
    change routingMatch p x = G.wiring (fun _=>Fin (2^1)) (fun s=>coords s (y s))
    rw [match_edges]
    unfold PortGraph.wiring
    congr 1
    apply propext
    constructor
    · intro H e
      exact congrArg finTwoEquiv.symm (H e)
    · intro H e
      exact finTwoEquiv.symm.injective (H e)
  apply ofRaw_le_iff.mp
  rw [ofRaw_eq_iff.mpr paired,G.ofRaw_rawWiring_eq_graphClass F (fun _=>1),ofRaw_raw]

end Hierarchy.WireTelescope

end
end OAI
