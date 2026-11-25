import OAI.ThreeFlat.Diagonal.HistoryActualPieces

namespace OAI
/-! # The physical half-port selected by a crossing motif wire -/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks MotifKernel HistoryContraction MotifBinaryPacking
open scoped Classical
noncomputable section

variable {M J E V D Pad : Type} [Fintype M] [Fintype J] [Fintype E] [Fintype V] [DecidableEq V] [Fintype D]
variable (G : M → PortGraph J E) (site : M → J → V) (I : M → E → Type)
    [∀ m e, Fintype (I m e)] [∀ m e, Inhabited (I m e)]

namespace MotifKernel

/-- The source endpoint has priority, as in `visible`. For a crossing edge
there is exactly one endpoint at this site. -/
def incidentPort (v : V) (m : M) (x : ExternalAt (G m) (site m) v) : (crossGraph G site).Port v :=
  if h : site m ((G m).tail x.val) = v then ⟨(⟨m,x.val⟩,false),h⟩
  else ⟨(⟨m,x.val⟩,true),x.property.resolve_left h⟩

omit [Fintype M] [Fintype J] [Fintype E] [Fintype V] in
@[simp] theorem incidentPort_edge (v : V) (m : M) (x : ExternalAt (G m) (site m) v) :
    (incidentPort G site v m x).1.1 = ⟨m,x.val⟩ := by unfold incidentPort; split <;> rfl

omit [Fintype J] in
theorem incident_read (v : V) (m : M) (x : ExternalAt (G m) (site m) v) (y : (crossShape G site I).Half v) :
    cast (congrArg (crossShape G site I).Label (incidentPort_edge G site v m x))
      (y (incidentPort G site v m x)) = visible G site I v y m x.val := by
  have move (a b : (crossGraph G site).Port v) (same : a=b) (edge : a.1.1=b.1.1) :
      cast (congrArg (crossShape G site I).Label edge) (y a) = y b := by
    subst b
    rfl
  by_cases ht : site m ((G m).tail x.val) = v
  · rw [visible,dite_eq_left ht]
    exact move (incidentPort G site v m x) ⟨(⟨m,x.val⟩,false),ht⟩
      (by simp [incidentPort,ht]) (incidentPort_edge G site v m x)
  · have hh := x.property.resolve_left ht
    rw [visible,dite_eq_right ht,dite_eq_left hh]
    exact move (incidentPort G site v m x) ⟨(⟨m,x.val⟩,true),hh⟩
      (by simp [incidentPort,ht]) (incidentPort_edge G site v m x)

end MotifKernel

namespace SlotRefinement

variable {A : E → Type} [∀ e, Fintype (A e)] (S : PortGraph V E) (T : PortGraph V D) (n b : E → ℕ)
    (hn : ∀ e, 0<n e) (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) (code : ∀ e, A e ≃ Fin (2^b e))
    (ends : ∀ e (i : Fin (n e)) side, T.vertex (cover (.inl ⟨e,i⟩)) side = S.vertex e side)

/-- A split surviving wire reads exactly one numbered physical pin, even
when its continuation occupies several balanced pieces. -/
def piecePin {p : ℕ} {v : V}
    (addr : (a : T.Port v) → Fin (actualWidth n b cover a.1.1) → Fin p)
    (x : S.Port v) (j : Fin (b x.1.1)) : Fin p :=
  let q := (SlotEnergy.pieceIndex _ _ (hn x.1.1)).symm j
  let a : T.Port v := ⟨(cover (.inl ⟨x.1.1,q.1⟩),x.1.2),(ends _ _ _).trans x.property⟩
  addr a (Fin.cast (by simp [a,actualWidth]) q.2)

omit [DecidableEq V] [Fintype E] [Fintype V] [Fintype D] [(e : E) → Fintype (A e)] in
theorem piecePin_read {p : ℕ} {v : V} (ys : T.State (fun a => Fin (2^actualWidth n b cover a)) v)
    (addr : (a : T.Port v) → Fin (actualWidth n b cover a.1.1) → Fin p)
    (pin : Fin p → Bool) (read : ∀ a t, pin (addr a t) = (ys a).val.testBit t.val)
    (x : S.Port v) (j : Fin (b x.1.1)) : pin (piecePin S T n b hn cover ends addr x j) =
      (code _ ((balanced S A T n b hn cover code ends).read v ys x)).val.testBit j.val :=
  pieceSource_read S T n b hn cover code ends ys (fun a t => BitSource.pin (internal:=0) (addr a t)) Fin.elim0 pin read x j

end SlotRefinement
end
end ThreeFlat.Diagonal

end OAI
