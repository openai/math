import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # Uniform one-edge tests for the face records

The proposed minimum is a pair of integers. Descent of the stated distance
forces it to be the code of an actual dart even on a malformed input.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarCertSize

variable {N : ℕ} {A D : Type*}

abbrev FaceKey := ℕ ×ₗ ℕ

/-- Current and reported dart identifiers are compared in lexicographic order. -/
def selfKey (b : BaseAlphabet N) (i : Fin 4) : FaceKey :=
  toLex (vertexVal b .preorderName, i.val + 1)

def faceKey (b : BaseAlphabet N) (i : Fin 4) : FaceKey :=
  toLex (portVal b i .minimumVertex, portVal b i .minimumPort)

def baseDegree (b : BaseAlphabet N) : ℕ :=
  (Finset.univ.filter (fun i => (b.2.1 i).isSome)).card

/-- Cyclically turn at the arrival end, using the type carried by that vertex. -/
def nextSlot (degree : ℕ) (i : Fin 4) : Fin 4 :=
  if h : i.val < degree ∧ degree ≤ 4 then
    Fin.castLE h.2 (finRotate degree ⟨i.val,h.1⟩) else 0

/-- Face equations at one port and at the successor at the opposite vertex. -/
def faceStep (b : BaseAlphabet N) (i : Fin 4) (w : BaseAlphabet N) (j : Fin 4) : Prop :=
  faceKey w j = faceKey b i ∧ faceKey b i ≤ selfKey b i ∧
    (faceKey b i = selfKey b i → portVal b i .forwardDistance = 0) ∧
    (faceKey b i ≠ selfKey b i →
      portVal b i .forwardDistance = portVal w j .forwardDistance + 1)

/-- At vacant slots all three face fields are zero. -/
def faceTest (z : PortView (BaseAlphabet N) 1) : Prop :=
  ∀ i : Fin 4, match z.2 i with
    | none => ∀ f, portVal z.1 i f = 0
    | some (j,w) => faceStep z.1 i w (nextSlot (baseDegree w) j)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
variable (b : V → BaseAlphabet N)

/-- Dart codes read relative to a tentative base labeling. -/
def atDart (g : BaseAlphabet N → Fin 4 → A) (p : E × Bool) : A :=
  g (b (M.graph.vertex p.1 p.2)) (M.slots _ ⟨p,rfl⟩)

theorem baseDegree_eq (x : BaseAlphabet N) (θ : MapType)
    (hx : x.2.1 = RootedMap.paddedDirection θ) : baseDegree x = θ.degree.val := by
  unfold baseDegree
  rw [hx]
  let u : Fin θ.degree.val ↪ Fin 4 := Fin.castLEEmb (Nat.le_of_lt_succ θ.degree.isLt)
  have he : Finset.univ.filter (fun i => (RootedMap.paddedDirection θ i).isSome) =
      Finset.univ.map u := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    by_cases hi : i.val < θ.degree.val
    · exact ⟨fun _ => ⟨⟨i.val,hi⟩,Fin.ext rfl⟩,
        fun _ => by simp [RootedMap.paddedDirection, hi]⟩
    · simp only [RootedMap.paddedDirection, hi, ↓reduceDIte, Option.isSome_none, Bool.false_eq_true,
        false_iff, not_exists]
      intro j hj
      exact hi (hj ▸ j.isLt)
  rw [he]
  simp

theorem nextSlot_port {v : V} (p : M.graph.Port v) :
    nextSlot (M.typeAt v).degree.val (M.slots v p) = M.slots v (M.num.successor v p) := by
  have h : (M.slots v p).val < (M.typeAt v).degree.val ∧ (M.typeAt v).degree.val ≤ 4 :=
    ⟨(M.num v p).isLt, M.degree v⟩
  apply Fin.ext
  simp only [nextSlot, dite_eq_left h, Fin.val_castLE]
  change _ = ((M.num v) ((M.num v).symm (finRotate _ ((M.num v) p)))).val
  simp
  rfl

theorem atDart_val {v : V} (p : M.graph.Port v) (g : BaseAlphabet N → Fin 4 → A) :
    atDart M b g p.val = g (b v) (M.slots v p) := by
  rcases p with ⟨p,rfl⟩
  rfl

/-- The coordinate form of the face recurrence; the comparison is between codes. -/
def CodedFaceEquations (φ : Equiv.Perm D) (own claim : D → FaceKey) (dist : D → ℕ) : Prop :=
  ∀ d, claim (φ d) = claim d ∧ claim d ≤ own d ∧
    (claim d = own d → dist d = 0) ∧ (claim d ≠ own d → dist d = dist (φ d) + 1)

theorem faceTest_iff (ht : ∀ v, (b v).2.1 = RootedMap.paddedDirection (M.typeAt v)) :
    (∀ v, faceTest (PortView.actual M.slots b 1 v)) ↔
      CodedFaceEquations M.num.rotation.picture.face (atDart M b selfKey)
        (atDart M b faceKey) (atDart M b (fun x i => portVal x i .forwardDistance)) ∧
      ∀ v i, (¬∃ p, M.slots v p = i) → ∀ f, portVal (b v) i f = 0 := by
  let check (v : V) (p : M.graph.Port v) :=
    faceStep (b v) (M.slots v p) (b (M.graph.vertex p.val.1 (!p.val.2))) (M.slots _ (M.num.successor _ (M.graph.pairedPort p)))
  have hact (v : V) (p : M.graph.Port v) :
      (PortView.actual M.slots b 1 v).2 (M.slots v p) =
        some (M.slots _ (M.graph.pairedPort p), b (M.graph.vertex p.val.1 (!p.val.2))) := by
    simp [PortView.actual]
    rfl
  have hn (v : V) (i : Fin 4) (hi : ¬∃ p, M.slots v p = i) :
      (PortView.actual M.slots b 1 v).2 i = none := by simp [PortView.actual, hi]
  have hc : (∀ v (p : M.graph.Port v), check v p) ↔
      CodedFaceEquations M.num.rotation.picture.face (atDart M b selfKey)
        (atDart M b faceKey) (atDart M b (fun x i => portVal x i .forwardDistance)) := by
    have hφ {v : V} (p : M.graph.Port v) :
        M.num.rotation.picture.face p.val = (M.num.successor _ (M.graph.pairedPort p)).val :=
      M.num.turn_port (M.graph.pairedPort p)
    let eqn := fun d => atDart M b faceKey (M.num.rotation.picture.face d) = atDart M b faceKey d ∧
      atDart M b faceKey d ≤ atDart M b selfKey d ∧
      (atDart M b faceKey d = atDart M b selfKey d →
        atDart M b (fun x i => portVal x i .forwardDistance) d = 0) ∧
      (atDart M b faceKey d ≠ atDart M b selfKey d →
        atDart M b (fun x i => portVal x i .forwardDistance) d =
        atDart M b (fun x i => portVal x i .forwardDistance) (M.num.rotation.picture.face d) + 1)
    have iff_at {v : V} (p : M.graph.Port v) : eqn p.val ↔ check v p := by
      simp only [eqn, hφ, atDart_val, check, faceStep]
    exact ⟨fun hh d => (iff_at (⟨d,rfl⟩ : M.graph.Port _)).mpr (hh _ _),
      fun hh v p => (iff_at p).mp (hh p.val)⟩
  rw [← hc]
  constructor
  · intro h
    refine ⟨fun v p => ?_, fun v i hi => ?_⟩
    · have hp := h v (M.slots v p)
      rw [hact] at hp
      simpa [PortView.actual, check, baseDegree_eq _ _ (ht _), nextSlot_port] using hp
    · have hp := h v i
      rwa [hn _ _ hi] at hp
  · rintro ⟨h,hnone⟩ v i
    by_cases hi : ∃ p, M.slots v p = i
    · obtain ⟨p,rfl⟩ := hi
      rw [hact]
      simpa [PortView.actual, check, baseDegree_eq _ _ (ht _), nextSlot_port] using h v p
    · rw [hn _ _ hi]
      exact hnone v i hi

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
