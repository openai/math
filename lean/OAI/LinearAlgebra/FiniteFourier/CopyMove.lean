import OAI.LinearAlgebra.FiniteFourier.PlaneCopying
import OAI.LinearAlgebra.FiniteFourier.PhasePrice

/-! # Moving matching phase labels by copying

When a label at one index is determined by an index at a second position, it
can be copied to a third position and the old copy erased by a local map.
The row and column labels of a controlled phase admit two such moves.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {I J : Type} {K : Type*} [Fintype I] [Fintype J] [Field K]

/-- Erase the old index after its label has been appended at its destination.
The local coefficient sums have just one contributing tuple: all other old
coordinates are fixed by the output, and the appended label fixes the moved
coordinate by injectivity. -/
theorem move_restricts_appendLabel (T : Raw.{0} I K) (p q : I → J) (i₀ : I)
    (hagree : ∀ i, i ≠ i₀ → p i = q i) {D : Type} [Fintype D] (e : T.Leg i₀ ↪ D) :
    (T.group q).Restricts ((T.group p).appendLabel (q i₀) D
      (fun z ↦ e (z (p i₀) ⟨i₀, rfl⟩))) := by
  let S := (T.group p).appendLabel (q i₀) D (fun z ↦ e (z (p i₀) ⟨i₀,rfl⟩))
  let ok (j : J) (x : (T.group q).Leg j) (y : S.Leg j) : Prop :=
    (∀ i, i ≠ i₀ → ∀ (h : p i = j) (h' : q i = j), y.1 ⟨i,h⟩ = x ⟨i,h'⟩) ∧
    ∀ h : q i₀ = j, y.2 ⟨(),h⟩ = e (x ⟨i₀,h⟩)
  refine ⟨fun j x y ↦ if ok j x y then 1 else 0, fun x ↦ ?_⟩
  let v (i : I) := x (q i) ⟨i,rfl⟩
  let keep (j : J) : S.Leg j := (fun i ↦ v i.val, fun _ ↦ e (v i₀))
  have hok (j : J) : ok j (x j) (keep j) := by
    refine ⟨?_, ?_⟩
    · rintro i _ _ rfl
      rfl
    · rintro rfl
      rfl
  let matchLabel (y : ∀ j, S.Leg j) :=
    (y (q i₀)).2 ⟨(),rfl⟩ = e ((y (p i₀)).1 ⟨i₀,rfl⟩)
  have hcoeff (y : ∀ j, S.Leg j) : S.coeff y = if matchLabel y then
      T.coeff (fun i ↦ (y (p i)).1 ⟨i,rfl⟩) else 0 := rfl
  change T.coeff v = ∑ y : ∀ j, S.Leg j, S.coeff y * ∏ j, if ok j (x j) (y j) then 1 else 0
  have hprod (y : ∀ j, S.Leg j) : (∏ j, if ok j (x j) (y j) then (1 : K) else 0) =
      if ∀ j, ok j (x j) (y j) then 1 else 0 := Fintype.prod_boole
  simp_rw [hprod]
  rw [Finset.sum_eq_single keep]
  · rw [hcoeff, ite_eq_left (show matchLabel keep from rfl), ite_eq_left hok, mul_one]
  · intro y _ hy
    by_cases hm : matchLabel y
    · by_cases ho : ∀ j, ok j (x j) (y j)
      · exfalso
        apply hy
        have hlabel := (ho (q i₀)).2 rfl
        funext j
        apply Prod.ext
        · funext ⟨i, hi⟩
          subst j
          by_cases h : i = i₀
          · subst i
            exact e.injective (hm.symm.trans hlabel)
          · have transport (j : J) (hj : q i = j) : x j ⟨i,hj⟩ = v i := by
              subst j; rfl
            exact ((ho _).1 i h rfl (hagree i h).symm).trans (transport _ _)
        · funext ⟨_, hj⟩
          subst j
          exact hlabel
      · simp [ho]
    · simp [hcoeff, hm]
  · simp

/-- Copying a matching label between three positions and then forgetting the
old copy moves one basis-indexed register. The second endpoint is retained. -/
theorem PlaneCopying.move_matched {P : SpectralPlacementPrices K Plane} (hc : PlaneCopying P)
    (T : Raw.{0} I K) (a b : I) {d : ℕ} (hd : 0 < d) (e : T.Leg a ↪ Fin d)
    (e' : T.Leg b → Fin d) (hmatch : ∀ z, T.coeff z ≠ 0 → e (z a) = e' (z b))
    (u v : I → Plane) (hmove : ∀ i, i ≠ a → v i = u i) :
    P.price T v ≤ P.price T u +
      (dist (u a) (v a) + dist (u b) (v a) - dist (u a) (u b)) / 2 * Real.logb 2 d := by
  let p (i : I) : Option I := some i
  let q (i : I) : Option I := if i = a then none else some i
  let y (j : Option I) := j.elim (v a) u
  let σ : Fin 3 → Option I := ![some a, some b, none]
  let hA (z : (T.group p).Leg (σ 0)) := e (z ⟨a, rfl⟩)
  let hB (z : (T.group p).Leg (σ 1)) := e' (z ⟨b, rfl⟩)
  have ho : y ∘ p = u := rfl
  have hn : y ∘ q = v := by
    funext i
    by_cases hi : i = a <;> simp [q,y,hi,hmove]
  have h₁ := hc (T.group p) y σ hd hA hB (fun z ht ↦
    hmatch (fun i ↦ z (p i) ⟨i,rfl⟩) ht)
  have hloc := move_restricts_appendLabel T p q a (fun i hi ↦ by simp [p,q,hi]) e
  have h₂ := placed_price_mono P y hloc
  have hq : q a = none := by simp [q]
  rw [hq] at h₂
  rw [show y (σ 0) = u a from rfl, show y (σ 1) = u b from rfl,
    show y (σ 2) = v a from rfl] at h₁
  calc
    P.price T v = P.price (T.group q) y := by simpa only [hn] using P.group T q y
    _ ≤ P.price (T.group p) y + _ := h₂.trans h₁
    _ = _ := by rw [← P.group T p y, ho]

variable {G : Type} [Fintype G] [Nonempty G]

/-- The long-move copying estimate for the phase tensor of a square matrix.
Its row and column indices each have `card G` labels. -/
theorem fourierPhasePrice_longMove {P : SpectralPlacementPrices K Plane} (hc : PlaneCopying P)
    (M : Matrix G G K) (A B A' B' X Y : Plane) :
    fourierPhasePrice P M ![X, Y, A', B'] ≤ fourierPhasePrice P M ![A, B, A', B'] +
      Real.logb 2 (Fintype.card G) / 2 *
        (‖X-A‖ + ‖X-A'‖ - ‖A-A'‖ + ‖Y-B‖ + ‖Y-B'‖ - ‖B-B'‖) := by
  let e := Fintype.equivFin G
  have hmatch (z : ∀ i, (phaseRaw M).Leg i) (hz : (phaseRaw M).coeff z ≠ 0) :
      z 0 = z 2 ∧ z 1 = z 3 := by
    by_contra h
    apply hz
    rw [phaseRaw_coeff M z]
    exact ite_eq_right (fun h' ↦ False.elim (h h'))
  have hr := hc.move_matched (phaseRaw M) 0 2 Fintype.card_pos e.toEmbedding e
    (fun z hz ↦ congrArg e (hmatch z hz).1) ![A,B,A',B'] ![X,B,A',B']
    (fun i hi ↦ by fin_cases i <;> simp_all)
  have hd := hc.move_matched (phaseRaw M) 1 3 Fintype.card_pos e.toEmbedding e
    (fun z hz ↦ congrArg e (hmatch z hz).2) ![X,B,A',B'] ![X,Y,A',B']
    (fun i hi ↦ by fin_cases i <;> simp_all)
  change P.price (phaseRaw M) ![X,B,A',B'] ≤ P.price (phaseRaw M) ![A,B,A',B'] +
    (dist A X + dist A' X - dist A A') / 2 * Real.logb 2 (Fintype.card G) at hr
  change P.price (phaseRaw M) ![X,Y,A',B'] ≤ P.price (phaseRaw M) ![X,B,A',B'] +
    (dist B Y + dist B' Y - dist B B') / 2 * Real.logb 2 (Fintype.card G) at hd
  change P.price (phaseRaw M) _ ≤ P.price (phaseRaw M) _ + _
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
  rw [dist_comm X A, dist_comm X A', dist_comm Y B, dist_comm Y B']
  linarith only [hr, hd]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
