import OAI.Computability.BorderVNP.PackedHistoryBoundaryPoints

/-! # The input of each geodesic subdivision site in the sparse rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Crossing Cover Cover.AddressCircuit Epoch
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Row-major numbering of the old sites and the reserved equality sites. -/
def siteIndex (V E extra : ℕ) : Fin V ⊕ (Fin E × Fin extra) ≃ Fin (V+extra*E) :=
  ((Equiv.refl (Fin V)).sumCongr (finProdFinEquiv.trans (finCongr (Nat.mul_comm E extra)))).trans finSumFinEquiv

/-- Input pins after the single endpoint lookup has been shared. -/
abbrev Joined (Move : Type*) (q l V E w : ℕ) :=
  Pins Move q l V E w ⊕ ((Fin E × Bool) × ProductSlots q l)

variable {I : Type*} [Fintype I] {L h : ℝ} {q V E d w : ℕ}

/-- Select the source origin and the fixed hop slot from a row's finite move
field. Retained vertices use the origin template and their own site address. -/
private noncomputable def originBit (site : Fin V ⊕ (Fin E × Fin ⌈L/h⌉₊)) :
    Option (Hop I L h) ⊕ ProductSlots q (d+1) → Expr (Joined (allowedMoves I L) q (d+1) V E w) :=
  match site with
  | .inl v => Sum.elim (fun t => .const (decide (t=none))) (fun j => .input (.inl (.inr (.inr (.inl (v,j))))))
  | .inr (e,j) => Sum.elim (fun t => match t with
      | none => .const false
      | some (m,i) => if i.val=j.val then .input (.inl (.inl (e,.inr m))) else .const false)
    (fun bit => .input (.inr ((e,true),bit)))

/-- Public input selection for one reserved row of the next site's catalog table. -/
noncomputable def originFrame (site : Fin V ⊕ (Fin E × Fin ⌈L/h⌉₊)) :
    Frame (Joined (allowedMoves I L) q (d+1) V E w) (Option (Hop I L h) ⊕ ProductSlots q (d+1)) :=
  (Frame.initial id).step (originBit site)

theorem originFrame_size (site : Fin V ⊕ (Fin E × Fin ⌈L/h⌉₊)) :
    (originFrame (I := I) (q := q) (d := d) (w := w) site).size ≤
      Fintype.card (Option (Hop I L h) ⊕ ProductSlots q (d+1)) := by
  apply (Frame.step_size_le _ _ 1 ?_).trans (by simp)
  intro i
  rcases site with v | ⟨e,j⟩ <;> cases i with
  | inr i => rfl
  | inl t =>
    cases t with
    | none => rfl
    | some z =>
      cases z with
      | mk m i =>
        simp only [originBit,Sum.elim_inl]
        first | rfl | split <;> rfl

variable {D : ℕ} {P : Type*} {K : Type*} {bits : P → ℕ}
    (enum : Fin q ≃ I) (p : Pack D P bits K) (r : SiteRoutes p I d L) {s : Shape}
    (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)
    {x : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool}
    (ready : Ready enum p r row dummy x) (fit : s.sites ≤ 2^w)

include ready

/-- Every retained site reads its own original integral tile, even if its name has holes before it. -/
theorem originFrame_old (v : p.layout.Site) :
    let z := (endpoints q (d+1) s.sites s.edges w (allowedMoves I L) fit).eval x
    (originFrame (h := h) (.inl (row.site v))).eval z = Sum.elim (fun t => @decide (t=none) (Classical.propDecidable _))
      (productWires (d+1) (fun i => (r.origin v (enum i) : Deck (d+1)))) := by
  intro z
  funext j
  cases j with
  | inl j => simp [originFrame,originBit,Expr.eval]
  | inr j => simpa [originFrame,originBit,Expr.eval,z,endpoints] using ready.origins v j

/-- An inserted equality site reads the precise preceding hop and the common source origin
of that physical wire. No representative or deck rank is searched for. -/
theorem originFrame_inner {e : p.layout.Edge} (he : r.active e) (j : Fin ⌈L/h⌉₊) :
    let z := (endpoints q (d+1) s.sites s.edges w (allowedMoves I L) fit).eval x
    let t : Hop I L h := (r.step e he,⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    (originFrame (.inr (row.edge e,j))).eval z = Sum.elim (fun u => @decide (u=some t) (Classical.propDecidable _))
      (productWires (d+1) (fun i => (r.origin (p.layout.src e) (enum i) : Deck (d+1)))) := by
  intro z t
  funext u
  cases u with
  | inr bit =>
    simpa [originFrame,originBit,Expr.eval,z] using endpoints_origin enum p r row dummy ready fit e true bit
  | inl v =>
    cases v with
    | none => simp [originFrame,originBit,Expr.eval]
    | some v =>
      rcases v with ⟨m,i⟩
      by_cases hi : i.val=j.val
      · have hj : i=t.2 := Fin.ext hi
        simpa [originFrame,originBit,Expr.eval,hi,z,endpoints,t,hj] using ready.move e he m
      · have hj : i≠t.2 := fun eq => hi (congrArg Fin.val eq)
        simp [originFrame,originBit,Expr.eval,hi,t,Prod.ext_iff,hj]

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
