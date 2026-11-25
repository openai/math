import OAI.Hierarchy.ProbeInducedBall

namespace OAI
/-! # Local price tests on the physical commodity, catalyst, core, and purchased wires -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical
noncomputable section

/-- A local commodity is either center-to-center payload or the signed end of a tile.
The center-to-center case stores the distinct-position fact from the external tag banks. -/
inductive LocalCommodity (I : Type*) (k : ℕ) where
  | payload (pair : DistinctPair I)
  | altimeter (input output : I) (j : Fin k) (s : Bool)

namespace LocalCommodity
variable {I A B : Type*} {k : ℕ}

def ends : LocalCommodity I k → DistinctPair (ColumnSite I k)
  | .payload p => ⟨(p.left,none),(p.right,none),fun h => p.apart (congrArg Prod.fst h)⟩
  | .altimeter i o j s => ⟨(i,none),(o,some (j,s)),by simp⟩

def extraEnds (d : A → LocalCommodity I k) (p : B → DistinctPair I) : A ⊕ B → DistinctPair (ColumnSite I k)
  | .inl a => (d a).ends
  | .inr b => (LocalCommodity.payload (k:=k) (p b)).ends

def extraPrice (price : A → ℝ) : A ⊕ B → ℝ
  | .inl a => price a
  | .inr _ => 1

def sources {H : Type*} (d : A → LocalCommodity I k) (p : B → DistinctPair I) :
    (A ⊕ B) → Source I (ColumnWires.Role I H (A ⊕ B) k) k
  | .inl a => match d a with
    | .payload e => .payload e.left e.right (.extra (.inl a))
    | .altimeter i o j s => .altimeter i o j s (.extra (.inl a))
  | .inr b => .probe (p b).left (p b).right

theorem all_wired [Fintype I] [SiteNaming (ColumnSite I k)] {H : Type*} (d : A → LocalCommodity I k) (p : B → DistinctPair I)
    (hor : H → DistinctPair I) (M : ℝ) (len : H → ℝ) (y : A → ℝ) (obs : A ⊕ B) :
    (sources d p obs).wired (ColumnWires.wires hor (extraEnds d p)) (ColumnWires.demand (Sum.inl (β:=B)))
      (ColumnWires.quote M len (extraPrice y)) (fun i => ColumnWires.site i none)
      (fun i j s => ColumnWires.site i (some (j,s))) := by
  cases obs with
  | inl a =>
    cases ha : d a with
    | payload e =>
      simp only [sources,ha,Source.wired]
      exact ⟨.inr a,by simpa [ColumnWires.demand,ColumnWires.wires,ColumnWires.ends,ColumnWires.site,extraEnds,ha,ends] using
        ((extraEnds d p (.inl a)).chord_joins),rfl⟩
    | altimeter i o j s =>
      simp only [sources,ha,Source.wired]
      exact ⟨.inr a,by simpa [ColumnWires.demand,ColumnWires.wires,ColumnWires.ends,ColumnWires.site,extraEnds,ha,ends] using
        ((extraEnds d p (.inl a)).chord_joins),rfl⟩
  | inr b => exact .wire (ColumnWires.Role.extra (I:=I) (H:=H) (k:=k) (Sum.inr (α:=A) b)) _ _ ((extraEnds d p (.inr b)).chord_joins)

/-- Only ordinary commodity prices vary within the compact test box. Purchased
probes have their printed unit length, including probes of zero installed width. -/
theorem compact_quotes [Fintype I] {H : Type*} (M : ℝ) (len : H → ℝ) (amax : A → ℝ) :
    IsCompact ((fun y : A → ℝ => ColumnWires.quote (I:=I) (k:=k) M len (extraPrice (B:=B) y)) '' Set.Icc 0 amax) := by
  apply isCompact_Icc.image
  apply continuous_pi
  intro r
  cases r with
  | catalyst | radius | cross | horizontal => exact continuous_const
  | extra e => cases e with
    | inl a => exact continuous_apply a
    | inr b => exact continuous_const

instance {V : Type*} [DecidableEq V] (next : V → Finset V) (root : V) (radius k : ℕ) :
    Nonempty (Fin (Fintype.card (ColumnSite (TestColumns next root radius) k))) :=
  ⟨SiteNaming.labels (X:=ColumnSite (TestColumns next root radius) k) (testBase next root radius,none)⟩

/-- One physical local test, at arbitrarily large M. Input is just a core socket
bank with its actual costs and indices; all horizontal path, signed-axis, demand and
purchased-chord hypotheses of `local_flattening` are proved here. -/
theorem test_flattening {F V H : Type*} [Field F] [DecidableEq V] [Fintype H] [Fintype A] [Fintype B]
    (next : V → Finset V) (root : V) (radius : ℕ) [SiteNaming (ColumnSite (TestColumns next root radius) k)] (hk : 0 < k) (no : ¬HasSpectralFlat F (k+1))
    (hor : H → DistinctPair (TestColumns next root radius)) (len : H → ℝ)
    (host : ∀ x y, y ∈ testNext next root radius x → ∃ e, len e ≤ 1 ∧
      (((hor e).left=x ∧ (hor e).right=y) ∨ ((hor e).left=y ∧ (hor e).right=x)))
    (commodities : A → LocalCommodity (TestColumns next root radius) k)
    (probes : B → DistinctPair (TestColumns next root radius)) {η : ℝ} (tol : 0 < η) :
    let I := TestColumns next root radius
    letI : Nonempty (ColumnWires.Role I H (A ⊕ B) k) := ⟨.catalyst (testBase next root radius) ⟨0,hk⟩⟩
    let free := fun i j => ∃ e, len e=0 ∧ (hor e).left=i ∧ (hor e).right=j
    let obs := sources (H:=H) commodities probes
    let wires := ColumnWires.wires hor (extraEnds commodities probes)
    let req := ColumnWires.demand (I:=I) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
    ∃ M₀ : ℕ, ∀ M : ℝ, 0<M → M₀≤M → ∀ amax : A → ℝ,
    ∃ ε : ℝ, 0<ε ∧ ∀ y ∈ Set.Icc (0:A → ℝ) amax,
      let p := ColumnWires.quote M len (extraPrice (B:=B) y)
      Probe.discrepancy F wires req p ≤ ε → ∃ z : I → Coordinates k,
      (∀ i j, free i j → z i=z j) ∧ ∀ l, |(obs l).quote M p-(obs l).model z|<η := by
  classical
  let I := TestColumns next root radius
  let free := fun i j => ∃ e, len e=0 ∧ (hor e).left=i ∧ (hor e).right=j
  let obs := sources (H:=H) commodities probes
  let wires := ColumnWires.wires hor (extraEnds commodities probes)
  let req := ColumnWires.demand (I:=I) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
  let base := testBase next root radius
  let : Nonempty I := ⟨base⟩
  let : Nonempty (ColumnWires.Role I H (A ⊕ B) k) := ⟨.catalyst base ⟨0,hk⟩⟩
  let : Nonempty (Fin (Fintype.card (ColumnSite I k))) := Fin.pos_iff_nonempty.mp (Fintype.card_pos (α:=ColumnSite I k))
  obtain ⟨N,flatten⟩ := local_flattening (F:=F) (S:=Fintype.card (ColumnSite I k))
    (A:=(I×Fin k) ⊕ A) (E:=ColumnWires.Role I H (A⊕B) k) (L:=A⊕B) base no (2*radius) free tol
  refine ⟨N,?_⟩
  intro M pos large amax
  let quote := fun y : A → ℝ => ColumnWires.quote (I:=I) (k:=k) M len (extraPrice (B:=B) y)
  let box := quote '' Set.Icc 0 amax
  have paths := test_connects next root radius hor (fun x y edge => by
    obtain ⟨e,_,ends⟩ := host x y edge; exact ⟨e,ends⟩)
  have conn := ColumnWires.connected (extra:=extraEnds commodities probes) base paths
  have setup := flatten M pos large wires req conn (fun i => ColumnWires.site i none)
    (fun i j s => ColumnWires.site i (some (j,s))) obs box (compact_quotes (I:=I) (B:=B) (k:=k) M len amax)
  obtain ⟨ε,ep,read⟩ := setup (by
    rintro _ ⟨y,_,rfl⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact fun i j => ColumnWires.catalyst_demanded M len _ _ i j
    · exact fun i j => (ColumnWires.radius_bounds M len _ i j false).symm
    · exact fun i j => ColumnWires.radius_bounds M len _ i j true
    · exact fun i j => test_diameter next root radius hor _ M len _ host i j none
    · exact fun i j l s => test_diameter next root radius hor _ M len _ host i j (some (l,s))
    · exact ColumnWires.cross_bound M len _
    · rintro i j ⟨e,cost,rfl,rfl⟩
      rw [←cost]; exact ColumnWires.horizontal_bound M len _ e none
    · exact all_wired commodities probes hor M len y)
  exact ⟨ε,ep,fun y hy => read (quote y) ⟨y,hy,rfl⟩⟩

end LocalCommodity
end
end Hierarchy.AdaptiveProbe

end OAI
