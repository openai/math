import OAI.LinearAlgebra.FiniteFourier.CircuitComposition
import OAI.LinearAlgebra.FiniteFourier.ScalarDescent

/-! # Simulating a binary linear circuit over a finite free coefficient algebra -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section Ring

variable {K E I O D T : Type*} [CommRing K] [CommRing E] [Algebra K E] [Fintype D]

/-- Append a weighted sum of already available values, retaining prior readouts. -/
private theorem appendLinearRow {r : ℕ} (p : Program K I r) (t : Finset T) (c : T → K)
    (v : T → (I → K) → K) (hv : ∀ i, Available p (v i)) :
    ∃ n ≤ r + t.card, ∃ q : Program K I n, (∀ u, Available p u → Available q u) ∧
      Available q (fun x => ∑ i ∈ t, c i * v i x) := by
  classical
  induction t using Finset.induction with
  | empty =>
    exact ⟨r, by simp, p, fun _ h => h, .zero, fun x => by simp [Readout.eval]⟩
  | @insert i t hi ih =>
    obtain ⟨m, hm, q, hkeep, hsum⟩ := ih
    obtain ⟨n, hn, q', hk', hnew⟩ :=
      available_combine q (c i) 1 (hkeep _ (hv i)) hsum
    refine ⟨n, ?_, q', fun u hu => hk' u (hkeep u hu), ?_⟩
    · rw [Finset.card_insert_of_notMem hi]
      omega
    · simpa [Finset.sum_insert hi] using hnew

private theorem appendLinearRows [Fintype T] {r : ℕ} (p : Program K I r) (s : Finset O)
    (c : O → T → K) (v : O → T → (I → K) → K) (hv : ∀ o i, Available p (v o i)) :
    ∃ n ≤ r + s.card * Fintype.card T, ∃ q : Program K I n,
      (∀ u, Available p u → Available q u) ∧
      ∀ o ∈ s, Available q (fun x => ∑ i, c o i * v o i x) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨r, by simp, p, fun _ h => h, by simp⟩
  | @insert o s ho ih =>
    obtain ⟨m, hm, q, hkeep, hrows⟩ := ih
    obtain ⟨n, hn, q', hk', hnew⟩ :=
      appendLinearRow q Finset.univ (c o) (v o) (fun i => hkeep _ (hv o i))
    refine ⟨n, ?_, q', fun u hu => hk' u (hkeep u hu), ?_⟩
    · rw [Finset.card_insert_of_notMem ho, Nat.succ_mul]
      rw [Finset.card_univ] at hn
      omega
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hnew
      · exact hk' _ (hrows u hu)

private theorem repr_mul_coord (b : Module.Basis D K E) (a v : E) (d : D) :
    b.repr (a * v) d = ∑ t, b.repr (a * b t) d * b.repr v t := by
  calc
    _ = b.repr (a * (∑ t, b.repr v t • b t)) d := by rw [b.sum_repr]
    _ = _ := by
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
        Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      exact fun t _ => mul_comm _ _

private def liftedInput (b : Module.Basis D K E) (d₀ : D) (x : I → K) (i : I) : E :=
  x i • b d₀

private def wireValue (b : Module.Basis D K E) (d₀ : D) {r : ℕ}
    (p : Program E I r) (w : I ⊕ Fin r) (x : I → K) : E :=
  Sum.elim (liftedInput b d₀ x) (p.value (liftedInput b d₀ x)) w

private theorem simulateExtension (b : Module.Basis D K E) (d₀ : D) {r : ℕ}
    (p : Program E I r) :
    ∃ n ≤ 2 * (Fintype.card D)^2 * r, ∃ q : Program K I n,
      ∀ w d, Available q (fun x => b.repr (wireValue b d₀ p w x) d) := by
  classical
  induction p with
  | nil =>
    refine ⟨0, by simp, .nil, ?_⟩
    rintro (i | j) d
    · refine ⟨.scaled (b.repr (b d₀) d) (.inl i), fun x => ?_⟩
      by_cases hd : d₀ = d <;> simp [Readout.eval, wireValue, liftedInput, hd]
    · exact j.elim0
  | @step r p g ih =>
    obtain ⟨m, hm, q, hw⟩ := ih
    let c (d : D) : D ⊕ D → K :=
      Sum.elim (fun t => b.repr (g.leftCoeff * b t) d) (fun t => b.repr (g.rightCoeff * b t) d)
    let v : D ⊕ D → (I → K) → K := Sum.elim
      (fun t x => b.repr (wireValue b d₀ p g.left x) t)
      (fun t x => b.repr (wireValue b d₀ p g.right x) t)
    have hv (t : D ⊕ D) : Available q (v t) := by cases t <;> apply hw
    obtain ⟨n, hn, q', hk, hnew⟩ := appendLinearRows q Finset.univ c (fun _ => v) (fun _ => hv)
    refine ⟨n, ?_, q', ?_⟩
    · simp only [Finset.card_univ, Fintype.card_sum] at hn
      calc n ≤ m + Fintype.card D * (Fintype.card D + Fintype.card D) := hn
           _ ≤ 2 * (Fintype.card D)^2 * r + Fintype.card D * (Fintype.card D + Fintype.card D) :=
              Nat.add_le_add_right hm _
           _ = _ := by ring
    · rintro (i | j) d
      · exact hk _ (hw (.inl i) d)
      · refine Fin.cases ?_ (fun t => hk _ (hw (.inr t) d)) j
        convert hnew d (Finset.mem_univ d) using 1
        funext x
        change b.repr (g.leftCoeff * wireValue b d₀ p g.left x +
          g.rightCoeff * wireValue b d₀ p g.right x) d = _
        rw [map_add, Finsupp.add_apply, repr_mul_coord b g.leftCoeff, repr_mul_coord b g.rightCoeff]
        rw [Fintype.sum_sum_type]
        rfl

/-- Restrict an extension circuit to one basis input component, then read that
component at every output. A gate computes `d` linear combinations of `2d` ground
wires; each output scaling requires one linear combination of `d` ground wires. -/
theorem circuit_of_extensionBasis [Fintype I] [Fintype O]
    (b : Module.Basis D K E) (d₀ : D) (M : Matrix O I K) {s : ℕ}
    (p : Circuit E I O s) (hp : p.matrix = M.map (algebraMap K E)) :
    ∃ n ≤ 2 * (Fintype.card D)^2 * s + Fintype.card D * Fintype.card O,
      ∃ q : Circuit K I O n, q.matrix = M := by
  classical
  obtain ⟨m, hm, q, hw⟩ := simulateExtension b d₀ p.program
  let c (o : O) (t : D) := match p.output o with
    | .zero => 0
    | .scaled a _ => b.repr (a * b t) d₀
  let v (o : O) (t : D) (x : I → K) := match p.output o with
    | .zero => 0
    | .scaled _ w => b.repr (wireValue b d₀ p.program w x) t
  have hv (o : O) (t : D) : Available q (v o t) := by
    cases he : p.output o with
    | zero => exact ⟨.zero, fun x => by simp [v, he, Readout.eval]⟩
    | scaled a w => simpa [v, he] using hw w t
  obtain ⟨n, hn, q', _, hrows⟩ := appendLinearRows q Finset.univ c v hv
  have hav (o : O) : Available q' (fun x => (b.repr (p.eval (liftedInput b d₀ x) o)) d₀) := by
    convert hrows o (Finset.mem_univ o) using 1
    funext x
    cases he : p.output o with
    | zero => simp [c, v, he, Circuit.eval, Readout.eval]
    | scaled a w =>
      simp only [Circuit.eval, he, Readout.eval, c, v]
      exact repr_mul_coord b _ _ _
  choose out hout using hav
  refine ⟨n, ?_, ⟨q', out⟩, ?_⟩
  · rw [Finset.card_univ] at hn
    calc n ≤ m + Fintype.card O * Fintype.card D := hn
         _ ≤ 2 * (Fintype.card D)^2 * s + Fintype.card O * Fintype.card D :=
            Nat.add_le_add_right hm _
         _ = _ := by rw [mul_comm (Fintype.card O)]
  · ext o i
    rw [Circuit.matrix_apply]
    change (out o).eval _ = _
    rw [hout]
    change b.repr (p.eval (liftedInput b d₀ (Pi.single i 1)) o) d₀ = M o i
    rw [p.eval_eq_mulVec, hp]
    simp only [Matrix.mulVec, dotProduct, liftedInput, Matrix.map_apply, ← Algebra.smul_def,
      smul_smul, ← Finset.sum_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    simp [Pi.single_apply, mul_ite]

/-- Complexity over the base ring from a chosen nonempty finite extension basis. -/
theorem complexity_le_of_extensionBasis [Fintype I] [Fintype O]
    (b : Module.Basis D K E) (d₀ : D) (M : Matrix O I K) :
    complexity M ≤ 2 * (Fintype.card D)^2 * complexity (M.map (algebraMap K E)) +
      Fintype.card D * Fintype.card O := by
  obtain ⟨s, hs, p, hp⟩ := realizableAtMost_complexity (M.map (algebraMap K E))
  obtain ⟨n, hn, q, hq⟩ := circuit_of_extensionBasis b d₀ M p hp
  exact (complexity_le_iff ..).mpr ⟨n,
    hn.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) _), q, hq⟩

end Ring

variable {K E I O : Type*} [Field K] [Field E] [Algebra K E]

/-- A degree-`d` extension improves binary linear circuit size by at most the
quadratic simulation factor, with `d` ground gates per output for its free scaling. -/
theorem complexity_le_of_finiteExtension [FiniteDimensional K E] [Fintype I] [Fintype O]
    (M : Matrix O I K) :
    complexity M ≤ 2 * (Module.finrank K E)^2 * complexity (M.map (algebraMap K E)) +
      Module.finrank K E * Fintype.card O := by
  simpa using complexity_le_of_extensionBasis (Module.finBasis K E)
    (⟨0, Module.finrank_pos⟩ : Fin (Module.finrank K E)) M

end

end FiniteFourier
end LinearAlgebra
end OAI
