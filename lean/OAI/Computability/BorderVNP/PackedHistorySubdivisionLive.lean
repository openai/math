import OAI.Computability.BorderVNP.PackedHistorySubdivisionPointers

/-! # Correct pointer, width and charge at every real subdivision cable -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Shortening.PublicEndpoints Crossing Cover Cover.AddressCircuit Epoch Packing.Names
open ParseBatchSort
open scoped Classical

variable {D q d w : ℕ} {P : Type*} {K : Type*} [CommSemiring K] {bits : P → ℕ}
    {I : Type*} [Fintype I] {L h : ℝ} (enum : Fin q ≃ I) (p : Pack D P bits K)
    (r : SiteRoutes p I d L) {s : Shape} (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)
    {x : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool} (ready : Ready enum p r row dummy x)

/-- Every true hop has its prescribed stripe number even when the old row is frozen. -/
theorem live_edgeIndex (e : p.layout.Edge) (j : Fin ((r.routes h).interior e+1)) :
    (row.siteRoutes r h).edge ⟨e,j⟩ =
      edgeIndex s.edges ⌈L/h⌉₊ (row.edge e,j.castLE (Nat.succ_le_succ (Rows.route_interior_le r h e))) := Fin.ext rfl

omit [CommSemiring K] in
include ready in
theorem original_pointer (e : p.layout.Edge) (side : Bool) :
    (Pointer.old side).value x (row.edge e) = (row.site (if side then p.layout.src e else p.layout.dst e)).val := by
  cases side
  · exact (ready.names.addresses (row.edge e) false).trans
      (congrArg (fun v => (row.site v).val) (dst_slot p.layout row.edge dummy e))
  · exact (ready.names.addresses (row.edge e) true).trans
      (congrArg (fun v => (row.site v).val) (src_slot p.layout row.edge dummy e))

include ready in
/-- The static equality-site offsets and dynamic original endpoints reproduce the
source and destination of the actual equality-subdivided network. -/
theorem physical_pointer (fit : (s.subdivide ⌈L/h⌉₊).sites ≤ 2^w) (e : p.layout.Edge)
    (j : Fin ((r.routes h).interior e+1)) (side : Bool) :
    (pointer s.sites ⌈L/h⌉₊ (row.edge e).val j.val (r.active e) side).value x (row.edge e) =
      ((row.siteRoutes r h).site (if side then (r.subdivided h).layout.src ⟨e,j⟩ else (r.subdivided h).layout.dst ⟨e,j⟩)).val := by
  let extra := ⌈L/h⌉₊
  have interior (he : r.active e) : (r.routes h).interior e = extra := by simp [SiteRoutes.routes,he,extra]
  let site := (row.siteRoutes r h).site
  have old (side : Bool) : (Pointer.old side).value x (row.edge e) =
      (site (.inl (if side then p.layout.src e else p.layout.dst e))).val :=
    original_pointer enum p r row dummy ready e side
  have eqsite (i : Fin ((r.routes h).interior e)) :
      (Pointer.equality (s.sites+extra*(row.edge e).val+i.val)).value x (row.edge e) = (site (.inr ⟨e,i⟩)).val := by
    have hv : (site (.inr ⟨e,i⟩)).val = s.sites+extra*(row.edge e).val+i.val := by
      change s.sites+(i.val+extra*(row.edge e).val) = _
      omega
    change _ % 2^w = _
    rw [← hv]
    exact Nat.mod_eq_of_lt ((site (.inr ⟨e,i⟩)).isLt.trans_le fit)
  have srcFirst : (r.subdivided h).layout.src ⟨e,0⟩ = Sum.inl (p.layout.src e) := by
    simp [SiteRoutes.subdivided,Network.subdivide]
  have dstLast : (r.subdivided h).layout.dst ⟨e,Fin.last ((r.routes h).interior e)⟩ = Sum.inl (p.layout.dst e) := by
    simp [SiteRoutes.subdivided,Network.subdivide]
  have srcInner (i : Fin ((r.routes h).interior e)) :
      (r.subdivided h).layout.src ⟨e,i.succ⟩ = Sum.inr ⟨e,i⟩ := by simp [SiteRoutes.subdivided,Network.subdivide]
  have dstInner (i : Fin ((r.routes h).interior e)) :
      (r.subdivided h).layout.dst ⟨e,i.castSucc⟩ = Sum.inr ⟨e,i⟩ := by simp [SiteRoutes.subdivided,Network.subdivide]
  by_cases he : r.active e
  · cases side with
    | true =>
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [pointer,he,ite_true,Fin.val_zero]
        exact (old true).trans (congrArg (fun v => (site v).val) srcFirst.symm)
      · simp only [pointer,he,ite_true,Fin.val_succ,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
        exact (eqsite i).trans (congrArg (fun v => (site v).val) (srcInner i).symm)
    | false =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pointer,he,ite_true,Bool.false_eq_true,ite_false,Fin.val_last,interior he,extra]
        exact (old false).trans (congrArg (fun v => (site v).val) dstLast.symm)
      · have hi : i.val ≠ ⌈L/h⌉₊ := ne_of_lt (i.isLt.trans_eq (interior he))
        simp only [pointer,he,ite_true,Bool.false_eq_true,ite_false,Fin.val_castSucc,hi]
        exact (eqsite i).trans (congrArg (fun v => (site v).val) (dstInner i).symm)
  · have hz : (r.routes h).interior e = 0 := by simp [SiteRoutes.routes,he]
    have hj : j.val=0 := by have := j.isLt; omega
    cases side with
    | true =>
      rw [show j = 0 from Fin.ext hj]
      simp only [pointer,he,Fin.val_zero,ite_true]
      exact (old true).trans (congrArg (fun v => (site v).val) srcFirst.symm)
    | false =>
      rw [show j = Fin.last _ from Fin.ext (hj.trans hz.symm)]
      simp only [pointer,he,Fin.val_last,hz,ite_true]
      exact (old false).trans (congrArg (fun v => (site v).val) dstLast.symm)

include ready in
/-- Every real wire survives with its full width, independent of its new subdivision length. -/
theorem live_width (e : p.layout.Edge) (j : Fin ((r.routes h).interior e+1)) :
    let f := cableFrame (allowedMoves I L) q (d+1) s.sites s.edges w ⌈L/h⌉₊
    value (fun b => f.eval x ((row.siteRoutes r h).edge ⟨e,j⟩,.inr (.inl b))) = p.layout.width e := by
  intro f
  rw [live_edgeIndex,cableFrame_width,ready.active]
  have hd : j.val=0 ∨ r.active e=true := by
    by_cases he : r.active e
    · exact Or.inr he
    · have hj := j.isLt
      simp [SiteRoutes.routes,he] at hj
      exact Or.inl (congrArg Fin.val hj)
  simp only [Fin.val_castLE,ite_eq_left hd]
  exact (ready.names.widths (row.edge e)).trans (width_slot p.layout row.edge dummy e)

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
