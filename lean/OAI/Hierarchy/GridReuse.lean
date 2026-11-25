import OAI.Hierarchy.GridReuseNetwork
import OAI.Hierarchy.GridReuseMixed
import OAI.Hierarchy.GridReuseRescale
import OAI.Hierarchy.GridPriceReindex
import OAI.Hierarchy.GridReuseScale
import OAI.Hierarchy.PointwiseCollapse

namespace OAI
/-! # Grid reuse with separate pins and shared catalyst junctions -/

noncomputable section
namespace Hierarchy.GridReuse

open Catalyst CatalystSubstitution GridThrough GridLens LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

variable {F : Type*} [Field F] {m p : ℕ}

def product (m n : ℕ) (f : (Fin p → Bool) → F) (d : Fin (Copies m n*p) → Bool) :=
  ∏ c : Fin (Copies m n), f (localPin n d c)

private theorem exact_cells {E k n : ℕ} {b : Fin k → ℕ}
    (P : Program (Fin E) n 0 b) (idle : ∀e, P.touch e=none)
    (v : Fin ((n+1)^k) → F) (x : GridDiagonal.Pins (Fin E)) :
    P.wiring.mixedEval (fun i => ideal b (fun _ : Fin 0 → Bool => v i)) x =
      (∏ i, v i) * GridDiagonal.identity F x := by
  rw [← P.eval_identity (fun _ : Fin 0 → Bool => (1:F)) idle (fun _ => rfl) x]
  unfold UniversalGrid.Wiring.mixedEval UniversalGrid.Wiring.eval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [ideal]
    split <;> simp
  · simp

private def endEquiv (n : ℕ) (b : Fin (m+1) → ℕ) :
    GridDiagonal.Ends (Fin (rails n b)) ≃ Wire (width n b) × Bool :=
  Equiv.prodCongr (Fintype.equivFin _).symm (Equiv.refl _)

private theorem target_cells (n : ℕ) (X : Approximation F (m+1) p)
    (f : (Fin p → Bool) → F) (d : Fin (Copies m n*p) → Bool)
    (w : Wire (width n X.width) × Bool → Bool) :
    (program (n:=n) X.width).wiring.mixedEval
      (fun c => ideal X.width (fun _ : Fin 0 → Bool => f (localPin n d c)))
      (external n X.width w) = ideal (width n X.width) (product m n f) (Sum.elim d w) := by
  rw [exact_cells _ (fun _ => rfl)]
  have eqs : (∀ i, external n X.width w (i,false) = external n X.width w (i,true)) ↔
      ∀ a : Wire (width n X.width), w (a,false) = w (a,true) := by
    exact (Fintype.equivFin (Wire (width n X.width))).symm.forall_congr_right
      (q:=fun a => w (a,false) = w (a,true))
  simp only [GridDiagonal.identity,ideal,Sum.elim_inr,Sum.elim_inl,eqs]
  by_cases ok : ∀ a : Wire (width n X.width), w (a,false) = w (a,true) <;>
    simp [ok,product]

private theorem width_sum (n : ℕ) (b : Fin (m+1) → ℕ) :
    (∑ j, (width n b j : ℝ)) = (rails n b : ℝ) := by
  change _ = (Fintype.card (Wire (width n b)) : ℝ)
  exact_mod_cast (wire_card (width n b)).symm

private theorem focus_scale_eq (n : ℕ) (b : Fin (m+1) → ℕ) (R : ℝ)
    (v : GridDiagonal.Ends (Fin (rails n b))) :
    GridDiagonal.focus R ((program b).direction v.1,v.2) =
      R • sites (p:=p) (width n b) (.inr (endEquiv n b v)) := by
  rcases v with ⟨e,s⟩
  let j := ((Fintype.equivFin (Wire (width n b))).symm e).1
  change point j 0 (if s then R else -R) = R • EuclideanSpace.single j (if s then 1 else -1)
  apply PiLp.ext
  intro i
  by_cases same : i=j
  · subst i
    cases s <;> simp []
  · cases s <;> simp [same]

/-- At a prescribed radius, this pointwise bound applies to the actual compact
network at every independent public word, including the zero-rail case. -/
theorem splice_gap (n : ℕ) (X : Approximation F (m+1) p) (f : (Fin p → Bool) → F)
    {D R : ℝ} (gap : X.PointwiseGap f D) (pos : 0<D) (far : 8*((n:ℝ)+1)≤R)
    (rail : (18:ℝ)*m*(rails n X.width)*((n:ℝ)+1)^2/R≤D/4)
    (terms : (2:ℝ)*(m+1:ℕ)*R*Copies m n≤D/4) :
    (splice n X).PointwiseGap (product m n f) (D/(2*R)) := by
  let P := program (n:=n) X.width
  have rpos : 0<R := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  intro Q d
  let actual := P.wiring.mixedEval (fun c => (pinWord X (localPin n d c)).coeff)
  let idealCells := P.wiring.mixedEval
    (fun c => ideal X.width (fun _ : Fin 0 → Bool => f (localPin n d c)))
  let er := actual-idealCells
  have coeff (w : Wire (width n X.width) × Bool → Bool) :
      ((splice n X).pinnedError (product m n f) d).coeff w = er (w ∘ endEquiv n X.width) := by
    change (splice n X).coeff (Sum.elim d w) - ideal (width n X.width) _ (Sum.elim d w) = _
    rw [splice_coeff,← target_cells]
    rfl
  have exact_of_zero (z : er = 0) :
      ((splice n X).pinnedError (product m n f) d).coeff = 0 := by
    funext w
    exact (coeff w).trans (congrFun z _)
  rcases isEmpty_or_nonempty (Fin (rails n X.width)) with empty | live
  · left
    let := empty
    have bw : Fintype.card (Wire X.width) = 0 := by
      have az : rails n X.width = 0 := by
        simpa only [Fintype.card_fin] using Fintype.card_eq_zero (α:=Fin (rails n X.width))
      rw [rails_eq] at az
      rw [wire_card]
      exact (Nat.mul_eq_zero.mp az).resolve_left (pow_ne_zero _ (Nat.succ_ne_zero _))
    have inst := Fintype.card_eq_zero_iff.mp bw
    let : IsEmpty (Wire X.width) := inst
    have same (a : Fin p → Bool) : (pinWord X a).coeff = ideal X.width (fun _ => f a) := by
      have zero := (gap Q a).resolve_right (fun price => by
        have pt : (fun j => sites (p:=p) X.width (.inr j)) = fun _ => 0 :=
          funext (fun j => isEmptyElim j.1)
        rw [pt,Q.collapsed] at price
        have sw : (∑ j, (X.width j : ℝ)) = 0 := by
          exact_mod_cast (show ∑ j, X.width j = 0 by rwa [wire_card] at bw)
        linarith)
      funext z
      exact sub_eq_zero.mp ((pinWord_error X a f z).trans (congrFun zero _))
    apply exact_of_zero
    simp only [er,actual,idealCells,same,sub_self]
  · let := live
    have bound := P.pinned_product_error X (localPin n d) f gap pos R far (rescale Q R rpos)
    change er=0 ∨ _ at bound
    rcases bound with zero | val
    · exact Or.inl (exact_of_zero zero)
    right
    let sites' : Wire (width n X.width) × Bool → Space (m+1) :=
      fun w => sites (p:=Copies m n*p) (width n X.width) (.inr w)
    have focus : (fun v => GridDiagonal.focus R (P.direction v.1,v.2)) =
        fun v => R • (sites' ∘ endEquiv n X.width) v :=
      funext (focus_scale_eq (p:=Copies m n*p) n X.width R)
    rw [focus, rescale_price] at val
    have raw : (splice n X).pinnedError (product m n f) d =
        CorrectionProducts.raw (fun w => er (w ∘ endEquiv n X.width)) := by
      exact congrArg (fun h => CorrectionProducts.raw h) (funext coeff)
    change Q.price _ sites' ≤ 2*(∑ j, (width n X.width j:ℝ)) - D/(2*R)
    rw [raw,raw_price_reindex,width_sum]
    have saving : R * Q.price (GridDiagonal.raw er) (sites' ∘ endEquiv n X.width) ≤
        2*R*rails n X.width-D/2 := by
      simp only [Nat.add_sub_cancel] at val
      linarith only [val,rail,terms]
    apply (le_of_mul_le_mul_left _ rpos)
    calc
      _ ≤ 2*R*rails n X.width-D/2 := saving
      _ = _ := by field_simp [rpos.ne']

/-- One radius works at each width for every network obeying the same growth
envelopes. Both the near-volume gap and the exact open network are explicit. -/
theorem uniform (m : ℕ) (n B : ℕ → ℕ) (D : ℕ → ℝ)
    (growth : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in Filter.atTop,
      ((n w+1:ℕ):ℝ) ≤ GridScale.dyad (ε*w) ∧
      (B w:ℝ) ≤ GridScale.dyad ((1+ε)*w) ∧ GridScale.dyad ((1-ε)*w) ≤ D w) :
    ∃ R : ℕ → ℕ, (∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in Filter.atTop,
      (R w:ℝ) ≤ GridScale.dyad (ε*w) ∧ GridScale.dyad ((1-ε)*w) ≤ D w/(2*R w)) ∧
    ∀ᶠ w : ℕ in Filter.atTop, ∀ {p : ℕ} (X : Approximation F (m+1) p) (f : (Fin p → Bool) → F),
      (∑ j, X.width j) ≤ B w → X.PointwiseGap f (D w) →
      (splice (n w) X).PointwiseGap (product m (n w) f) (D w/(2*R w)) := by
  obtain ⟨R,envelope,room⟩ := GridScale.uniform_reuse (g:=fun w => n w+1) (B:=B) (m+1) growth
  refine ⟨R,envelope,?_⟩
  filter_upwards [room,growth 1 (by norm_num)] with w ready bounds
  intro p X f pairs gap
  rcases ready with ⟨far,railsRoom,termsRoom⟩
  have pos : 0<D w := (by dsimp [GridScale.dyad]; positivity : 0<GridScale.dyad ((1-1)*w)).trans_le bounds.2.2
  have cap : (rails (n w) X.width : ℝ) ≤ ((n w+1:ℕ):ℝ)^m*(B w:ℝ) := by
    rw [rails_eq,Nat.cast_mul,Nat.cast_pow]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast pairs) (by positivity)
  apply splice_gap (n w) X f gap pos (by exact_mod_cast far)
  · calc
      _ ≤ (18:ℝ)*m*(((n w+1:ℕ):ℝ)^m*(B w:ℝ))*((n w:ℝ)+1)^2/R w := by
        gcongr
      _ ≤ _ := by simpa using railsRoom
  · simpa [Copies] using termsRoom

/-- Row-major data words agree after flattening the cell index and the tick
index within the cell. -/
theorem product_tick (n : ℕ) (tick : ThreeFlat.BitNetwork F p)
    (q : ℕ) (d : Fin (Copies m n*(q*p)) → Bool) :
    product m n (tickProduct tick q) d =
      tickProduct tick (Copies m n*q) (d ∘ Fin.cast (Nat.mul_assoc _ _ _)) := by
  unfold product tickProduct
  rw [← (finProdFinEquiv (m:=Copies m n) (n:=q)).prod_comp]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  apply congrArg tick.eval
  funext a
  apply congrArg d
  apply Fin.ext
  simp [finProdFinEquiv_apply_val,Nat.mul_add,Nat.add_assoc,Nat.mul_comm,Nat.mul_left_comm]

private theorem cast_gap {k a b : ℕ} (h : a=b) (X : Approximation F k a)
    (f : (Fin a → Bool) → F) (g : (Fin b → Bool) → F) {D : ℝ}
    (old : X.PointwiseGap f D) (pins : ∀ d, f d = g (d ∘ Fin.cast h.symm)) :
    (h ▸ X : Approximation F k b).PointwiseGap g D := by
  subst b
  have same : f = g := funext (fun d => pins d)
  rwa [←same]

/-- The physical spliced grid with the precise arity of the next tick product. -/
def spliceTicks (n q : ℕ) (X : Approximation F (m+1) (q*p)) :
    Approximation F (m+1) ((Copies m n*q)*p) :=
  (Nat.mul_assoc (Copies m n) q p).symm ▸ splice n X

theorem spliceTicks_gap (n q : ℕ)
    (tick : ThreeFlat.BitNetwork F p)
    (X : Approximation F (m+1) (q*p)) {D : ℝ}
    (h : (splice n X).PointwiseGap (product m n (tickProduct tick q)) D) :
    (spliceTicks n q X).PointwiseGap (tickProduct tick (Copies m n*q)) D :=
  cast_gap _ _ _ _ h (product_tick n tick q)

end Hierarchy.GridReuse

end
end OAI
