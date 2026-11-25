import OAI.Hierarchy.DescentObservedReservations

namespace OAI
/-! # The populated direct-link matrices configure the actual selected devices -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentGL DescentColonies DescentBaseProfile DescentRouterSlots DescentRotor
open scoped Classical BigOperators
noncomputable section
variable {V I H K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Field K]
variable {k n : ℕ} {B factor : ℝ} {u : ℕ} (D : Dyadic V I k)
local notation "Y" => (2^n:ℕ)
local notation "S" => (factor*B)
variable (L : D.Loads (2^n) B (factor*B) (u : ℝ)) (pos : 0 < factor*B) (pu : 0 < u)
variable (ub : (u:ℝ) ≤ B) (ys : ((2^n : ℕ) : ℝ)*B ≤ factor*B) (fallback : Bool→V×Block k→H)
private abbrev installedAt := D.install L pos (Nat.cast_pos.mpr pu) ub ys fallback
local notation "puR" => (Nat.cast_pos.mpr pu : (0:ℝ)<u)
local notation "P" => installedAt D L pos pu ub ys fallback

private theorem placed (s : Bool) (g : D.G) (p : D.Paid) :
    (P).owner s ((P).contact p.val)=.inl g ↔ D.endAt s (D.edge p)=g := by
  have yes : useRotor (P).b (P).depth (P).L (P).keys (P).hub (P).old p.val := p.property
  simp only [Placement.owner,Placement.contact,DescentChosenRouter.contact,
    dite_eq_left yes,DescentChosenRouter.owner]
  exact ⟨Sum.inl.inj,congrArg Sum.inl⟩

def bundleEquiv (s : Bool) (g : D.G) : D.AtBase s g ≃ Cells P s g where
  toFun p := ⟨p.val.val,(placed D L pos pu ub ys fallback s g p.val).mpr p.property⟩
  invFun e := by
    have yes : useRotor D.b D.hk D.L D.keys D.hub D.old e.val :=
      (in_good_iff D.b D.hk D.L D.keys D.hub D.old D.endAt (D.span L) (D.ticket L pos puR)
        fallback s e.val).mp ⟨g,e.property⟩
    exact ⟨⟨e.val,yes⟩,(placed D L pos pu ub ys fallback s g ⟨e.val,yes⟩).mp e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem read_source (s : Bool) (g : D.G) (p : D.AtBase s g) :
    source P s g (D.bundleEquiv L pos pu ub ys fallback s g p)=
      (D.assignment L pos puR ub ys s g).choose (D.whole s g p) := by
  rw [←D.row_at L pos puR ub ys s g p]
  have paidRow (r : InputId (P).site s (.inl g)) (a : D.G) (j : Fin Y)
      (eq : r.val = Sum.inl (a,j)) : head P s g r = j := by
    rcases r with ⟨w,hw⟩
    change w = _ at eq
    subst w
    rfl
  apply paidRow _ (D.endpoint s p.val) _
  change (P).input s p.val.val = Sum.inl (D.endpoint s p.val,_)
  exact dite_eq_left p.val.property

private theorem read_target (s : Bool) (g : D.G) (p : D.AtBase s g) :
    target P s g (D.bundleEquiv L pos pu ub ys fallback s g p)=D.lastRow L pos puR s g p := by
  rcases p with ⟨i,eq⟩
  subst g
  let g := D.endAt s (D.edge i)
  have paidSlot (r : LinkId (P).owner s (.inl g)) (c : Reserve (P).span)
      (eq : r.val = Sum.inl c) : tail P s g r = (P).columns s g
        ((slot (P).b (P).keys (P).hub (P).ends (P).span (P).room s c).2) := by
    rcases r with ⟨w,hw⟩
    change w = _ at eq
    subst w
    rfl
  let e := (D.bundleEquiv L pos pu ub ys fallback s g) ⟨i,rfl⟩
  refine (paidSlot (link (P).contact (P).owner s (.inl g) e) (D.ticket L pos puR i) ?_).trans ?_
  · change (P).contact i.val = Sum.inl (D.ticket L pos puR i)
    exact dite_eq_left i.property
  · rfl

private theorem transport {A Z : Type} [Fintype A] [Fintype Z] (e : A≃Z)
    (f g : A→Fin Y) (f' g' : Z→Fin Y) (h : ∀a,f' (e a)=f a) (h' : ∀a,g' (e a)=g a) (i j : Fin Y) :
    matrixOfBundles f' g' i j=matrixOfBundles f g i j := by
  unfold matrixOfBundles
  symm
  apply Finset.card_bij' (fun a _=>e a) (fun z _=>e.symm z)
  · intro a mem
    simpa [h,h'] using mem
  · intro z mem
    obtain ⟨a,rfl⟩ := e.surjective z
    simpa [h,h'] using mem
  · simp
  · simp

/-- Physical input/output row matrices can be read directly in terms of the
same round-robin ordinal and original uncut tensor as in their scalar budget. -/
theorem observed_matrix (s : Bool) (g : D.G) (i j : Fin Y) :
    matrixOfBundles (source P s g) (target P s g) i j =
      matrixOfBundles ((D.assignment L pos puR ub ys s g).choose ∘ D.whole s g)
        (D.lastRow L pos puR s g) i j :=
  transport (D.bundleEquiv L pos pu ub ys fallback s g) _ _ _ _
    (D.read_source L pos pu ub ys fallback s g) (D.read_target L pos pu ub ys fallback s g) i j

private theorem matrix_instances {A : Type} (a b : Fintype A) {m : ℕ}
    (src dst : A → Fin m) (i j : Fin m) :
    @matrixOfBundles A a m src dst i j = @matrixOfBundles A b m src dst i j := by
  cases Subsingleton.elim a b
  rfl

/-- Install each configured trivalent rotor from observed capacities, whole
input masses and the real number of bundles on each paid pair. -/
def observed_hardware {h bits C₀ : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
    (menu : ∀p : Equiv.Perm (Fin Y),Configures K G.arcs C₀ bits p)
    (scale : (Y:ℝ)^2*bits≤factor) : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw S := by
  have read (s : Bool) (g : D.G) (i j : Fin Y)
      (a : Fintype (Cells P s g)) (b : Fintype (D.AtBase s g)) :
      @matrixOfBundles _ a _ (source P s g) (target P s g) i j =
      @matrixOfBundles _ b _ ((D.assignment L pos puR ub ys s g).choose ∘ D.whole s g)
        (D.lastRow L pos puR s g) i j :=
    (matrix_instances a _ _ _ i j).trans
      ((D.observed_matrix L pos pu ub ys fallback s g i j).trans (matrix_instances _ b _ _ i j))
  apply build (F:=factor) (B:=B) P G hw pu menu ub scale
  · intro s g i
    simp only [Nat.cast_mul,mul_assoc]
    refine Eq.trans_le ?_ ((D.assignment L pos puR ub ys s g).choose_spec.2.1 i)
    exact Finset.sum_congr rfl fun j _ => congrArg (fun q : ℕ => (q : ℝ)) (read s g i j _ _)
  · intro s g j
    simp only [Nat.cast_mul,mul_assoc]
    refine Eq.trans_le ?_ ((D.assignment L pos puR ub ys s g).choose_spec.2.2 j)
    exact Finset.sum_congr rfl fun i _ => congrArg (fun q : ℕ => (q : ℝ)) (read s g i j _ _)

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
