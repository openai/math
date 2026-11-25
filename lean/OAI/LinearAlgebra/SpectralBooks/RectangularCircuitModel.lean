import OAI.LinearAlgebra.MatrixExponent.Integral.Model
import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent

/-! # Cost-preserving translation between two division-free circuit models

The integral model records a set of available polynomials, while the formal
model names registers. Both allow free loads of inputs and field constants. -/

namespace OAI.LinearAlgebra.SpectralBooks

open OAI.MatrixMultiplication.Arithmetic
open MatrixExponent

variable {F : Type*} [Field F] {i j k : ℕ}

private abbrev Inputs (i j k : ℕ) := MatrixInput i k j
private abbrev Poly (F : Type*) [Field F] (i j k : ℕ) := Integral.Poly F i j k

/-- Reading the registers in order builds their polynomials at the same cost. -/
private theorem program_build {r : ℕ} (p : Program F (Inputs i j k) r) :
    ∃ T, Integral.Build (Integral.initial F i j k) p.cost T ∧
      Integral.initial F i j k ⊆ T ∧ ∀ t, registerPolynomial p t ∈ T := by
  induction p with
  | nil => exact ⟨_, .nil, Set.Subset.rfl, fun t => t.elim0⟩
  | step p g ih =>
    obtain ⟨T, build, initial, values⟩ := ih
    have step (g : Gate F (Inputs i j k) _) {U : Set (Poly F i j k)}
        (h : Integral.Build (Integral.initial F i j k) (p.cost + g.cost) U)
        (old : T ⊆ U) (new : gatePolynomial g (registerPolynomial p) ∈ U) :
        ∃ V, Integral.Build (Integral.initial F i j k) (p.step g).cost V ∧
          Integral.initial F i j k ⊆ V ∧ ∀ t, registerPolynomial (p.step g) t ∈ V :=
      ⟨U, h, initial.trans old, Fin.cases new (fun t => old (values t))⟩
    cases g with
    | constant c => exact step _ build Set.Subset.rfl (initial (.inl ⟨c, rfl⟩))
    | input x => exact step _ build Set.Subset.rfl (initial (.inr ⟨x, rfl⟩))
    | add x y =>
      exact step _ (build.add (values x) (values y)) (Set.subset_insert ..) (Set.mem_insert ..)
    | sub x y =>
      exact step _ (build.sub (values x) (values y)) (Set.subset_insert ..) (Set.mem_insert ..)
    | mul x y =>
      exact step _ (build.mul (values x) (values y)) (Set.subset_insert ..) (Set.mem_insert ..)

/-- A finite selection suffices even when the initially available constants form an infinite set. -/
private def CanRead (T : Set (Poly F i j k)) (cost : ℕ) : Prop :=
  ∀ s : Finset (Poly F i j k), (↑s : Set _) ⊆ T →
    ∃ (r : ℕ) (p : Program F (Inputs i j k) r), p.cost = cost ∧
      ∀ v ∈ s, ∃ t, registerPolynomial p t = v

private theorem read_initial : CanRead (Integral.initial F i j k) 0 := by
  classical
  intro s hs
  have load (v : s) : ∃ e : Expression F (Inputs i j k),
      e.cost = 0 ∧ expressionPolynomial e = v.val := by
    rcases hs v.property with ⟨c, hc⟩ | ⟨x, hx⟩
    · exact ⟨.constant c, rfl, hc⟩
    · exact ⟨.input x, rfl, hx⟩
  choose e cost value using load
  let p := Expression.compileFamily e
  refine ⟨_, p.program, p.cost_eq.trans (by simp [cost]), ?_⟩
  intro v hv
  exact ⟨p.output ⟨v, hv⟩, (registerPolynomial_compileFamily e ⟨v, hv⟩).trans (value ⟨v, hv⟩)⟩

private theorem read_binary {T : Set (Poly F i j k)} {m : ℕ} (h : CanRead T m)
    {x y : Poly F i j k} (hx : x ∈ T) (hy : y ∈ T)
    (op : Poly F i j k → Poly F i j k → Poly F i j k)
    (gate : ∀ {r : ℕ}, Fin r → Fin r → Gate F (Inputs i j k) (Fin r))
    (cost : ∀ {r} (a b : Fin r), (gate a b).cost = 1)
    (value : ∀ {r} (a b : Fin r) (v : Fin r → Poly F i j k),
      gatePolynomial (gate a b) v = op (v a) (v b)) :
    CanRead (insert (op x y) T) (m + 1) := by
  classical
  intro s hs
  let need := insert x (insert y (s.erase (op x y)))
  have old : (↑need : Set _) ⊆ T := by
    intro v hv
    simp only [need, Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hv
    rcases hv with rfl | rfl | ⟨hne, hin⟩
    · exact hx
    · exact hy
    · exact (hs hin).resolve_left hne
  obtain ⟨r, p, hp, read⟩ := h need old
  obtain ⟨a, ha⟩ := read x (by simp [need])
  obtain ⟨b, hb⟩ := read y (by simp [need])
  refine ⟨_, p.step (gate a b), by simp [hp, cost], ?_⟩
  intro v hv
  by_cases he : v = op x y
  · exact ⟨0, by rw [registerPolynomial_zero, value, ha, hb, he]⟩
  · obtain ⟨t, ht⟩ := read v (by simp [need, he, hv])
    exact ⟨t.succ, ht⟩

private theorem read_build {T : Set (Poly F i j k)} {m : ℕ}
    (h : Integral.Build (Integral.initial F i j k) m T) : CanRead T m := by
  induction h with
  | nil => exact read_initial
  | add _ hx hy ih =>
    exact read_binary ih hx hy (· + ·) Gate.add (fun _ _ => rfl) (fun _ _ _ => rfl)
  | sub _ hx hy ih =>
    exact read_binary ih hx hy (· - ·) Gate.sub (fun _ _ => rfl) (fun _ _ _ => rfl)
  | mul _ hx hy ih =>
    exact read_binary ih hx hy (· * ·) Gate.mul (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- Integral circuits order dimensions as rows, columns, inner dimension. -/
private theorem computes_iff {m : ℕ} : Integral.Computes F i j k m ↔
    ∃ p : MatrixAlgorithm F i k j, FormalCorrect p ∧ p.cost = m := by
  classical
  constructor
  · rintro ⟨T, h, out⟩
    let s := Finset.univ.image (Integral.output F (i := i) (j := j) (k := k))
    obtain ⟨r, p, hp, read⟩ := read_build h s (by
      rintro v hv
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hv
      exact out q)
    have entry (q : Integral.Pos i j) :=
      read (Integral.output F q) (Finset.mem_image_of_mem _ (Finset.mem_univ q))
    choose idx hidx using entry
    exact ⟨⟨r, p, fun a b => idx (a, b)⟩, fun a b => hidx (a, b), hp⟩
  · rintro ⟨p, correct, rfl⟩
    obtain ⟨T, build, _, read⟩ := program_build p.program
    refine ⟨T, build, fun q => ?_⟩
    have eq : registerPolynomial p.program (p.output q.1 q.2) = Integral.output F q :=
      correct q.1 q.2
    rw [← eq]
    exact read (p.output q.1 q.2)

/-- The admissible exponents agree after translating wire order to matrix dimensions. -/
theorem formalOmega_eq_integral (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c = Integral.exponent F c b a := by
  unfold formalOmega Integral.exponent
  congr 1
  ext τ
  change FormalAdmissibleExponent F a b c τ ↔ Integral.Admissible F c b a τ
  constructor
  · intro h ε hε
    obtain ⟨C, hC, bound⟩ := h ε hε
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨p, correct, cost⟩ := bound n hn
    exact ⟨p.cost, computes_iff.mpr ⟨p, correct, rfl⟩, cost⟩
  · intro h ε hε
    obtain ⟨C, hC, bound⟩ := h ε hε
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨m, hm, cost⟩ := bound n hn
    obtain ⟨p, correct, rfl⟩ := computes_iff.mp hm
    exact ⟨p, correct, cost⟩

private theorem wireDimension_max_zero {n : ℕ} (hn : 1 ≤ n) (w : ℝ) :
    wireDimension n (max w 0) = wireDimension n w := by
  rcases le_total 0 w with hw | hw
  · rw [max_eq_left hw]
  rw [max_eq_right hw]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [wireDimension, Real.rpow_zero, Nat.ceil_one]
  apply Nat.le_antisymm (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _))
  apply Nat.ceil_le.mpr
  simpa using Real.rpow_le_rpow_of_exponent_le hn' hw

/-- Negative weights and zero give the same rounded dimension at every admissible scale. -/
theorem formalOmega_max_zero (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c = formalOmega F (max a 0) (max b 0) (max c 0) := by
  unfold formalOmega
  congr 1
  ext τ
  change FormalAdmissibleExponent F a b c τ ↔
    FormalAdmissibleExponent F (max a 0) (max b 0) (max c 0) τ
  constructor <;> intro h ε hε <;> obtain ⟨C, hC, bound⟩ := h ε hε <;>
    refine ⟨C, hC, fun n hn => ?_⟩
  · rw [wireDimension_max_zero hn a, wireDimension_max_zero hn b, wireDimension_max_zero hn c]
    exact bound n hn
  · have hp := bound n hn
    rw [wireDimension_max_zero hn a, wireDimension_max_zero hn b, wireDimension_max_zero hn c] at hp
    exact hp

end OAI.LinearAlgebra.SpectralBooks
