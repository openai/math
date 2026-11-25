import OAI.Hierarchy.TaggedWireSpineVisits

namespace OAI
/-! # Ordinals of the comparison turns of a word spine -/

noncomputable section
namespace Hierarchy.WireTelescope.Spine

open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators

variable {S : ℕ} {E : Type} {G : PortGraph (Fin S) E} {a b : Fin S} {es : List E}

variable {P : Fin S → Type}

/-- A turn belongs to exactly one site's equality list. -/
def gateAt (v s : Fin S) (l r : P v) : List (P s × P s) :=
  if h : v=s then [(h ▸ l,h ▸ r)] else []

def namedTurns : {a b : Fin S} → {es : List E} → Spine G a es b →
    P a → P b → (∀ j : Fin es.length,∀ t : Bool,P (G.vertex (es.get j) t)) →
    (s : Fin S) → List (P s × P s)
  | _,_,_,.nil a,l,r,_,s => gateAt a s l r
  | _,_,_,.cons e t tail,l,r,port,s => gateAt (G.vertex e t) s l (port 0 t) ++
      namedTurns tail (port 0 (!t)) r (fun j u=>port j.succ u) s

theorem namedTurns_length {P : Fin S → Type} (sp : Spine G a es b) (l : P a) (r : P b)
    (port : ∀ j : Fin es.length, ∀ t, P (G.vertex (es.get j) t)) (s : Fin S) :
    (sp.namedTurns l r port s).length = Fintype.card {j // sp.visit j = s} := by
  have gate (v : Fin S) (x y : P v) :
      (gateAt v s x y).length = if v=s then 1 else 0 := by
    by_cases h : v=s <;> simp [gateAt,h]
  have card {n : ℕ} (v : Fin n → Fin S) :
      Fintype.card {j // v j = s} = ∑ j, if v j=s then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [card]
  induction sp with
  | nil v =>
    by_cases eq : v=s <;> simp [namedTurns,gateAt,visit,eq]
  | cons e side tail ih =>
    let head := gateAt (G.vertex e side) s l (port 0 side)
    let rest := tail.namedTurns (port 0 (!side)) r (fun j u=>port j.succ u) s
    have count := congrArg₂ Nat.add (gate (G.vertex e side) l (port 0 side))
      (ih (port 0 (!side)) r (fun j u=>port j.succ u))
    have split := Fin.sum_univ_succ (fun j=>if (Spine.cons e side tail).visit j=s then (1:ℕ) else 0)
    change (head++rest).length=_
    exact (show (head++rest).length=head.length+rest.length by simp only [List.length_append]).trans
      (count.trans split.symm)

end Hierarchy.WireTelescope.Spine

end
end OAI
