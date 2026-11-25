import OAI.Geometry.HyperbolicGroups.PictureEuler

/-!
# Local certificates for the face permutation of a planar map

Order the ports by vertex name and port number. Each port reports the least
port on its face cycle and the forward distance to that port. The local
successor equations force both reports. Counting one minimum per orbit
recovers the face count in the Euler test.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarFace

open Equiv Equiv.Perm
open HyperbolicObstruction.PictureSwitch

variable {D : Type*} [LinearOrder D] [Fintype D] (φ : Perm D)

/-- Ports visited on the face through `d`. -/
def orbit (d : D) : Finset D := Finset.univ.filter (φ.SameCycle d)

@[simp] theorem mem_orbit {d e : D} : e ∈ orbit φ d ↔ φ.SameCycle d e := by
  simp [orbit]

theorem orbit_congr {d e : D} (h : φ.SameCycle d e) : orbit φ d = orbit φ e := by
  ext a
  exact (mem_orbit φ).trans (Iff.trans ⟨h.symm.trans, h.trans⟩ (mem_orbit φ).symm)

theorem self_mem_orbit (d : D) : d ∈ orbit φ d := (mem_orbit φ).2 .rfl

/-- True least port on the directed face cycle. -/
def leastPort (d : D) : D := (orbit φ d).min' ⟨d, self_mem_orbit φ d⟩

theorem sameCycle_leastPort (d : D) : φ.SameCycle d (leastPort φ d) :=
  (mem_orbit φ).1 (Finset.min'_mem ..)

theorem leastPort_le {d e : D} (h : φ.SameCycle d e) : leastPort φ d ≤ e :=
  Finset.min'_le _ _ ((mem_orbit φ).2 h)

theorem leastPort_congr {d e : D} (h : φ.SameCycle d e) : leastPort φ d = leastPort φ e :=
  le_antisymm (leastPort_le φ (h.trans (sameCycle_leastPort φ e)))
    (leastPort_le φ (h.symm.trans (sameCycle_leastPort φ d)))

@[simp] theorem leastPort_apply (d : D) : leastPort φ (φ d) = leastPort φ d :=
  leastPort_congr φ SameCycle.rfl.apply_left

/-- The number of forward steps to the first visit to the least port. -/
def forwardDistance (d : D) : ℕ := Nat.find (sameCycle_leastPort φ d).exists_nat_pow_eq

theorem forwardDistance_hits (d : D) : (φ ^ forwardDistance φ d) d = leastPort φ d :=
  Nat.find_spec (sameCycle_leastPort φ d).exists_nat_pow_eq

theorem forwardDistance_le {d : D} {k : ℕ} (h : (φ ^ k) d = leastPort φ d) :
    forwardDistance φ d ≤ k := Nat.find_min' _ h

theorem forwardDistance_zero_iff {d : D} : forwardDistance φ d = 0 ↔ leastPort φ d = d := by
  constructor
  · intro h
    have hf := forwardDistance_hits φ d
    simpa [h] using hf.symm
  · intro h
    exact Nat.eq_zero_of_le_zero (forwardDistance_le φ (k := 0) (by simpa using h.symm))

theorem forwardDistance_succ {d : D} (h : leastPort φ d ≠ d) :
    forwardDistance φ d = forwardDistance φ (φ d) + 1 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (mt (forwardDistance_zero_iff φ).1 h)
  have hhit := forwardDistance_hits φ d
  rw [hk, pow_succ, mul_apply, ← leastPort_apply φ d] at hhit
  have h₁ := forwardDistance_le φ hhit
  have h₂ := forwardDistance_hits φ (φ d)
  rw [leastPort_apply, ← mul_apply, ← pow_succ] at h₂
  have h₃ := forwardDistance_le φ h₂
  omega

theorem forwardDistance_lt_card (d : D) : forwardDistance φ d < Fintype.card D := by
  have hcycle : φ.IsCycleOn (orbit φ d) := by
    constructor
    · refine ⟨fun x hx => (mem_orbit φ).2 ((mem_orbit φ).1 hx).apply_right,
        φ.injective.injOn, ?_⟩
      exact fun y hy => ⟨φ.symm y, (mem_orbit φ).2 ((mem_orbit φ).1 hy).symm_apply_right,
        φ.apply_symm_apply y⟩
    · exact fun _ hx _ hy => ((mem_orbit φ).1 hx).symm.trans ((mem_orbit φ).1 hy)
  have hm := (mem_orbit φ).2 (sameCycle_leastPort φ d)
  obtain ⟨k, hk, hhit⟩ := hcycle.exists_pow_eq (self_mem_orbit φ d) hm
  exact lt_of_le_of_lt (forwardDistance_le φ hhit) (hk.trans_le (Finset.card_le_univ _))

/-- The manuscript's local tests involve only the port and its face successor. -/
structure Valid (record : D → D × ℕ) : Prop where
  constant : ∀ d, (record (φ d)).1 = (record d).1
  lower : ∀ d, (record d).1 ≤ d
  zero : ∀ d, (record d).1 = d → (record d).2 = 0
  step : ∀ d, (record d).1 ≠ d → (record d).2 = (record (φ d)).2 + 1

/-- The true orbit minimum and first hitting distance pass the local checks. -/
theorem canonical_valid : Valid φ (fun d => (leastPort φ d, forwardDistance φ d)) :=
  ⟨leastPort_apply φ, fun _ => leastPort_le φ .rfl, fun _ => (forwardDistance_zero_iff φ).2,
    fun _ => forwardDistance_succ φ⟩

variable {φ} {record : D → D × ℕ}

omit [Fintype D] in
theorem Valid.constant_pow (h : Valid φ record) (d : D) (k : ℕ) :
    (record ((φ ^ k) d)).1 = (record d).1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply, h.constant, ih]

omit [Fintype D] in
/-- Following the stated number of forward steps actually attains the claimed
minimum. -/
theorem Valid.hits (h : Valid φ record) (d : D) : (φ ^ (record d).2) d = (record d).1 := by
  generalize hn : (record d).2 = n
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    by_cases hd : (record d).1 = d
    · rw [← hn, h.zero d hd, pow_zero, one_apply, hd]
    · have hs := h.step d hd
      have hrec := ih (record (φ d)).2 (by omega) (φ d) rfl
      rw [← hn, hs, pow_succ, mul_apply, hrec, h.constant]

theorem Valid.eq_leastPort (h : Valid φ record) (d : D) : (record d).1 = leastPort φ d := by
  have hhit := h.hits d
  have hin : φ.SameCycle d (record d).1 := hhit ▸ SameCycle.rfl.pow_right
  refine le_antisymm ?_ (leastPort_le φ hin)
  rw [← forwardDistance_hits φ d, ← h.constant_pow d (forwardDistance φ d)]
  exact h.lower _

/-- The tests have exactly one accepted record at every port. -/
theorem Valid.eq_canonical (h : Valid φ record) (d : D) :
    record d = (leastPort φ d, forwardDistance φ d) := by
  refine Prod.ext (h.eq_leastPort d) ?_
  generalize hn : (record d).2 = n
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    by_cases hd : (record d).1 = d
    · rw [← hn, h.zero d hd, (forwardDistance_zero_iff φ).2 ((h.eq_leastPort d).symm.trans hd)]
    · have hs := h.step d hd
      have hrec := ih (record (φ d)).2 (by omega) (φ d) rfl
      rw [← hn, hs, forwardDistance_succ φ (fun h' => hd ((h.eq_leastPort d).trans h')), hrec]

variable (φ)

/-- Ports witnessing one face each. -/
def minima : Finset D := Finset.univ.filter fun d => leastPort φ d = d

@[simp] theorem mem_minima {d : D} : d ∈ minima φ ↔ leastPort φ d = d := by simp [minima]

/-- The least ports are in bijection with the cycles, including one-port cycles. -/
def classEquivMinima : Quotient (SameCycle.setoid φ) ≃ ↥(minima φ) where
  toFun := Quotient.lift (fun d => ⟨leastPort φ d,
    (mem_minima φ).2 (leastPort_congr φ (sameCycle_leastPort φ d).symm)⟩)
    (fun _ _ h => Subtype.ext (leastPort_congr φ h))
  invFun d := Quotient.mk _ d.val
  left_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | h d => exact Quotient.sound (sameCycle_leastPort φ d).symm
  right_inv d := Subtype.ext ((mem_minima φ).1 d.property)

theorem card_minima : ((minima φ).card : ℤ) = cycles φ := by
  rw [cycles_eq_card_classes]
  have h : (minima φ).card = Nat.card (VertexClasses φ) := by
    simpa only [Nat.card_eq_fintype_card (α := ↥(minima φ)), Fintype.card_coe] using
      (Nat.card_congr (classEquivMinima φ)).symm
  exact_mod_cast h

/-- The reported face count uses the single exterior face for an edgeless,
one-vertex connected map. -/
def faceCount (record : D → D × ℕ) : ℕ :=
  if Fintype.card D = 0 then 1 else (Finset.univ.filter fun d => (record d).1 = d).card

theorem faceCount_dartless [IsEmpty D] (record : D → D × ℕ) : faceCount record = 1 := by
  simp [faceCount]

variable {φ} in
theorem faceCount_eq_cycles [Nonempty D] (h : Valid φ record) :
    (faceCount record : ℤ) = cycles φ := by
  classical
  unfold faceCount
  simp only [Fintype.card_ne_zero, ↓reduceIte]
  have he : (Finset.univ.filter fun d => (record d).1 = d) = minima φ := by
    ext d
    simp [h.eq_leastPort]
  rw [he, card_minima]

omit [LinearOrder D] [Fintype D] in
/-- Cross each port to its partner before taking the cyclic successor at
that vertex. In the side-pairing API this is exactly the face permutation. -/
theorem crossThenSuccessor (M : PictureMap D) : M.vertex * M.edge = M.face := by
  rw [PictureMap.vertex, mul_assoc, M.edge_sq, mul_one]

/-- For a connected map with ports the local face count yields exactly the
combinatorial genus-zero Euler test on its oriented side pairing. -/
theorem euler_test_iff [Nonempty D] (M : PictureMap D)
    (hconn : Nat.card (Quotient M.components) = 1)
    (h : Valid (M.vertex * M.edge) record) :
    cycles M.vertex - (Fintype.card D : ℤ) / 2 + faceCount record = 2 ↔ M.GenusZero := by
  rw [crossThenSuccessor] at h
  rw [faceCount_eq_cycles h, PictureMap.GenusZero, hconn, PictureMap.euler]
  push_cast
  omega

/-- The connected map with no ports has one vertex and one face. -/
theorem euler_test_dartless [IsEmpty D] (record : D → D × ℕ) :
    (1 : ℤ) - (Fintype.card D : ℤ) / 2 + faceCount record = 2 := by
  simp [faceCount_dartless]

end PlanarFace

end

end SpectralBooks
end LinearAlgebra
end OAI
