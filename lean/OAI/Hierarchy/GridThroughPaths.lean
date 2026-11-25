import OAI.Hierarchy.GridThroughDisjoint

namespace OAI
/-! # The geometric certificate of a native grid program -/

namespace Hierarchy.GridThrough.Program
open GridLens
open scoped Classical
noncomputable section

variable {E k n p : ℕ} {width : Fin k → ℕ} (P : GridThrough.Program (Fin E) n p width)

/-- The certificate uses the actual equality occurrence and actual cell ordinal, transported
through their enumerations. Reserved catalyst pairs use the two halves of their mounted passage. -/
def paths (R : ℝ) (eqAt : Fin P.wiring.equal.length → Bool → EuclideanSpace ℝ (Fin k))
    (attached : ∀ i b, eqAt i b = WireRoute.site P.direction P.row R
      (P.physicalRoute (.inl (P.edgeDecode i))) b) :
    PathCertificate P.direction P.row R (demandEnds width (cellOrdinal (k:=k) (n:=n)).symm eqAt) := by
  apply WireRoute.certificate P.direction P.row R _ (fun a => P.physicalRoute (P.demandDecode a))
  · rintro (i | ⟨c,w⟩) b
    · exact attached i b
    · change cellPort ((cellOrdinal (k:=k) (n:=n)).symm c) w.1 b =
        cellPort (cellOnRail (P.direction (P.pass ((cellOrdinal (k:=k) (n:=n)).symm c) w))
          (P.row (P.pass ((cellOrdinal (k:=k) (n:=n)).symm c) w))
          ((cellOrdinal (k:=k) (n:=n)).symm c (P.direction (P.pass ((cellOrdinal (k:=k) (n:=n)).symm c) w))))
          (P.direction (P.pass ((cellOrdinal (k:=k) (n:=n)).symm c) w)) b
      rw [P.pass_line, P.pass_dir]
  · intro i i' z hi hi'
    have h : (P.demandDecode i.1, i.2) = (P.demandDecode i'.1, i'.2) :=
      P.physicalRoute_disjoint hi hi'
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    exact Prod.ext (P.demandDecode.injective ha) hb

/-- At the endpoints of a native edge the address geometry agrees with its selected rail label. -/
theorem edgePair_site (R : ℝ) (addr : P.Addr → EuclideanSpace ℝ (Fin k))
    (baseAt : ∀ e t s, addr (P.base e t s) = cellPort (P.railCell e t) (P.direction e) s)
    (centerAt : ∀ u, addr (P.center u) = cellCenter (P.railCell u.1.val.1 u.1.val.2))
    (focusAt : ∀ e s, addr (.inr (.inl (e,s))) = point (P.direction e) 0 (if s then R else -R))
    (edge : P.Edge) (b : Bool) :
    addr (if b then (P.edgePair edge).2 else (P.edgePair edge).1) =
      WireRoute.site P.direction P.row R (P.physicalRoute (.inl edge)) b := by
  rcases edge with ⟨e,s⟩ | ⟨e,t⟩ | z | ⟨u,s⟩
  · cases s <;> cases b <;> simp [edgePair, physicalRoute, WireRoute.site, segmentEnd,
      focusAt, baseAt, railCell]
  · cases b <;> simp [edgePair, physicalRoute, WireRoute.site, segmentEnd, baseAt, railCell]
  · cases b <;> simp [edgePair, physicalRoute, WireRoute.site, baseAt, railCell]
  · cases s <;> cases b <;> simp [edgePair, physicalRoute, WireRoute.site, segmentEnd,
      baseAt, centerAt, railCell]

/-- Native address placement yields a path certificate for the observed tests of `P.wiring`. -/
def paths_of_positions (R : ℝ) (addr : P.Addr → EuclideanSpace ℝ (Fin k))
    (eqAt : Fin P.wiring.equal.length → Bool → EuclideanSpace ℝ (Fin k))
    (edgeAt : ∀ i b, eqAt i b = addr (if b then (P.wiring.equal.get i).2 else (P.wiring.equal.get i).1))
    (baseAt : ∀ e t s, addr (P.base e t s) = cellPort (P.railCell e t) (P.direction e) s)
    (centerAt : ∀ u, addr (P.center u) = cellCenter (P.railCell u.1.val.1 u.1.val.2))
    (focusAt : ∀ e s, addr (.inr (.inl (e,s))) = point (P.direction e) 0 (if s then R else -R)) :
    PathCertificate P.direction P.row R (demandEnds width (cellOrdinal (k:=k) (n:=n)).symm eqAt) := by
  apply P.paths R eqAt
  intro i b
  rw [edgeAt, P.equal_get]
  exact P.edgePair_site R addr baseAt centerAt focusAt (P.edgeDecode i) b


end
end Hierarchy.GridThrough.Program

end OAI
