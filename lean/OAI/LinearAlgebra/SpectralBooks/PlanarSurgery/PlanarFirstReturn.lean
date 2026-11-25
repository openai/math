import OAI.Geometry.HyperbolicGroups.CycleCount
import OAI.Geometry.HyperbolicGroups.PermEuler

/-! # Face cycles after suppressing the internal ports of a patch

Each patch contour encounters a genuine stub. Collapse a walk of unmarked
ports to the first stub reached in the forward direction. When the actual
external edges are paired, this gives a bijection between the face cycles on
all darts and the face cycles of the stub permutation.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarSurgery

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {D S : Type*} [Fintype D] (p : Perm D) (j : S ↪ D)

/-- Each contour has a marked port. -/
def Covers : Prop := ∀ x : D, ∃ s : S, p.SameCycle x (j s)

variable (hc : Covers p j)

include hc in
private theorem eventually_marked (x : D) : ∃ n : ℕ, (p ^ n) x ∈ Set.range j := by
  obtain ⟨s, hs⟩ := hc x
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  exact ⟨n,s,hn.symm⟩

open scoped Classical in
def arrivalTime (x : D) := Nat.find (eventually_marked p j hc x)

theorem arrival_mem (x : D) : (p ^ arrivalTime p j hc x) x ∈ Set.range j := by
  classical
  exact Nat.find_spec (eventually_marked p j hc x)

theorem arrival_min {x : D} {n : ℕ} (h : (p ^ n) x ∈ Set.range j) :
    arrivalTime p j hc x ≤ n := by
  classical
  exact Nat.find_min' (eventually_marked p j hc x) h

/-- The first marked stub at or after the specified dart. -/
def firstStub (x : D) : S := (arrival_mem p j hc x).choose

theorem firstStub_spec (x : D) :
    j (firstStub p j hc x) = (p ^ arrivalTime p j hc x) x := (arrival_mem p j hc x).choose_spec

@[simp] theorem arrivalTime_mark (s : S) : arrivalTime p j hc (j s) = 0 :=
  Nat.eq_zero_of_le_zero (arrival_min p j hc (n := 0) (by simp))

@[simp] theorem firstStub_mark (s : S) : firstStub p j hc (j s) = s := by
  apply j.injective
  simp [firstStub_spec]

theorem arrivalTime_advance {x : D} (hx : x ∉ Set.range j) :
    arrivalTime p j hc x = arrivalTime p j hc (p x) + 1 := by
  have hn : arrivalTime p j hc x ≠ 0 := by
    intro h
    have := arrival_mem p j hc x
    exact hx (by simpa [h] using this)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hl := arrival_mem p j hc x
  rw [hk, pow_succ, mul_apply] at hl
  have h₁ := arrival_min p j hc hl
  have h₂ := arrival_min p j hc (n := arrivalTime p j hc (p x) + 1) (x := x)
    (by simpa only [pow_succ, mul_apply] using arrival_mem p j hc (p x))
  omega

theorem firstStub_advance {x : D} (hx : x ∉ Set.range j) :
    firstStub p j hc (p x) = firstStub p j hc x := by
  apply j.injective
  rw [firstStub_spec, firstStub_spec, arrivalTime_advance p j hc hx, pow_succ, mul_apply]

variable [Fintype S]

private theorem nextSurjective : Function.Surjective (fun s : S => firstStub p j hc (p (j s))) := by
  let f := fun s : S => firstStub p j hc (p (j s))
  have closed (x : D) (hin : firstStub p j hc x ∈ Set.range f) : firstStub p j hc (p x) ∈ Set.range f := by
    by_cases h : x ∈ Set.range j
    · obtain ⟨s,rfl⟩ := h
      exact ⟨s,rfl⟩
    · rwa [firstStub_advance p j hc h]
  intro s
  have start : firstStub p j hc (p (j s)) ∈ Set.range f := ⟨s,rfl⟩
  have iter (n : ℕ) : firstStub p j hc ((p ^ n) (p (j s))) ∈ Set.range f := by
    induction n with
    | zero => simpa only [pow_zero, one_apply] using start
    | succ n ih => simpa only [pow_succ', mul_apply] using closed _ ih
  obtain ⟨n, hn⟩ := (SameCycle.rfl (f := p) (x := j s)).apply_right.symm.exists_nat_pow_eq
  change s ∈ Set.range f
  simpa only [hn, firstStub_mark] using iter n

/-- First positive return on marked ports, in the orientation of the contour. -/
def onStubs : Perm S := Equiv.ofBijective (fun s => firstStub p j hc (p (j s)))
  ⟨(Finite.surjective_iff_bijective.mp (nextSurjective p j hc)).1, nextSurjective p j hc⟩

@[simp] theorem onStubs_apply (s : S) : onStubs p j hc s = firstStub p j hc (p (j s)) := rfl

variable (e : Perm S) (g : Perm D) (hedge : ∀ s, g (j s) = p (j (e s)))
  (hghost : ∀ x, x ∉ Set.range j → g x = p x)

include hghost in
private theorem full_firstStub (x : D) : g.SameCycle x (j (firstStub p j hc x)) := by
  induction x using (measure (arrivalTime p j hc)).wf.induction with
  | h x ih =>
    by_cases h : x ∈ Set.range j
    · obtain ⟨s,rfl⟩ := h
      rw [firstStub_mark]
    · have hdecr : arrivalTime p j hc (p x) < arrivalTime p j hc x := by
        rw [arrivalTime_advance p j hc h]
        exact Nat.lt_succ_self _
      have hi := ih (p x) hdecr
      rw [firstStub_advance p j hc h] at hi
      apply (SameCycle.rfl (f := g) (x := x)).apply_right.trans
      rwa [hghost x h]

include hedge hghost in
/-- Close up the external stubs using their prescribed pairing. Ports in the
interior of an arc encounter the same next stub before and after closing. -/
def faceEquiv : Quotient (SameCycle.setoid g) ≃ Quotient (SameCycle.setoid (onStubs p j hc * e)) := by
  let q := onStubs p j hc * e
  have forward : SameCycle.setoid g ≤ (SameCycle.setoid q).comap (firstStub p j hc) := by
    apply sameCycle_le_of_apply
    intro x
    change q.SameCycle (firstStub p j hc x) (firstStub p j hc (g x))
    by_cases h : x ∈ Set.range j
    · obtain ⟨s,rfl⟩ := h
      rw [firstStub_mark, hedge]
      exact (SameCycle.rfl (f := q) (x := s)).apply_right
    · rw [hghost x h, firstStub_advance p j hc h]
  have backward : SameCycle.setoid q ≤ (SameCycle.setoid g).comap j := by
    apply sameCycle_le_of_apply
    intro s
    apply (SameCycle.rfl (f := g) (x := j s)).apply_right.trans
    rw [hedge]
    exact full_firstStub p j hc g hghost _
  refine ⟨Quotient.map (firstStub p j hc) (fun _ _ h => forward h),
    Quotient.map j (fun _ _ h => backward h), ?_, ?_⟩
  · intro x
    induction x using Quotient.inductionOn with
    | h x => exact Quotient.sound (full_firstStub p j hc g hghost x).symm
  · intro s
    induction s using Quotient.inductionOn with
    | h s => exact congrArg (Quotient.mk _) (firstStub_mark p j hc s)

include hedge hghost in
theorem cycles_close [DecidableEq D] [DecidableEq S] :
    cycles g = cycles (onStubs p j hc * e) := by
  rw [cycles_eq_card_classes, cycles_eq_card_classes]
  exact_mod_cast Nat.card_congr (faceEquiv p j hc e g hedge hghost)

end PlanarSurgery

end

end SpectralBooks
end LinearAlgebra
end OAI
