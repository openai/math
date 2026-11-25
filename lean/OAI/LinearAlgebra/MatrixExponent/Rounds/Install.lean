import OAI.LinearAlgebra.MatrixExponent.Rounds.Costs
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Shaving.FieldStage

/-!
# Installing the expansion as one network

An installation consists of an initialization map, a sequence of
weighted transitions and a terminal evaluator. The inequalities
separate the short-control cost per allocated seat from the cost
of handling the terminal payload and the original exterior.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Filter Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ}
variable {K : Type} [Field K] {x y : Wire}

structure Installation (k : Val x → Val y → K) (d : ℕ) where
  u : ℕ
  hu : 3 ≤ u
  labels : Finset (Table K)
  start : Snapshot.{1} K (copies x d) (copies y d)
  stop : Snapshot.{1} K (copies x d) (copies y d)
  first : start.state
  scalar : K
  exactPower : (fun x y => scalar * start.eval first x y) = power k d
  m₁ : ℕ
  m₂ : ℕ
  m₃ : ℕ
  init : Map K u labels (.wire (.pair (copies x d) (copies y d))) start.port
    (fun q => start.encode first q.1 q.2) m₁
  run : Transforms K u labels start stop m₂
  finish : Finishes K u labels stop m₃

def Installation.cost {k : Val x → Val y → K} {d : ℕ} (A : Installation k d) :=
  A.m₁ + (A.m₂ + A.m₃) + 4 * (d * wd y) + 1

theorem Installation.labeled {k : Val x → Val y → K} {d : ℕ} (A : Installation k d)
    {B : ℕ} (h : A.labels.card ≤ B) :
    ∃ s ≤ A.cost, Labeled (power k d) B s A.u := by
  obtain ⟨s, hs, hw⟩ := Finishes.start A.hu A.first A.init (A.run.finish A.finish)
  have sc : Wide K A.u A.labels .unit .unit (fun _ _ => A.scalar) 1 :=
    .table _ _ _ (Nat.zero_le _) (.inl (by decide))
  have net := ((hw.par sc).pre (.unit' _)).post (.unit' _)
  rw [wd_copies] at hs
  refine ⟨s + 1, Nat.add_le_add_right hs _, A.labels, h, ?_⟩
  rw [← A.exactPower]
  simpa only [mul_comm] using net

variable (v : Levels p M)

def Levels.work (m e : ℕ) (h a : ℝ) (c : ℕ) : ℝ :=
  (p.overhead ^ v.j * v.allocation m : ℕ) * h ^ (c * a) + v.finalBudget m + (v.batch * e : ℕ)

/-- Cost and arity required of the explicit implementation. The
logarithmic slack must also pay for reading the input and closing
the output of the sequence of transformations. -/
def Levels.Installed (n m c : ℕ) (a : ℝ) (k : Val x → Val y → K) : Prop :=
  let h : ℝ := Nat.clog 2 n
  let τ := a * δ / 6
  ∃ I : Installation k v.batch, I.labels.card ≤ Shaving.dictionary n ∧
    (I.cost : ℝ) ≤ h ^ τ * v.work m (wd x + wd y) h a c ∧
    (I.u : ℝ) ≤ h ^ τ * (p.D * (v.finalWidth : ℝ))

private theorem costs {n m c T₀ : ℕ} {a b ξ : ℝ} (ha : 0 < a) (hd : 0 < δ)
    (small : (p.groupRate + c + 1 : ℕ) * a ≤ b)
    (hv : v.Suits n T₀ a b ξ) (hcost : v.Costs n m a b (a * δ / 6))
    (large : 3 ≤ (Nat.clog 2 n : ℝ) ^ (a * δ / 6))
    {e : ℕ} (he : (e : ℝ) ≤ m * (Nat.clog 2 n : ℝ) ^ (-(2 * a))) :
    let h : ℝ := Nat.clog 2 n
    h ^ (a * δ / 6) * v.work m e h a c ≤ m * (v.batch : ℝ) * h ^ (-((1 - δ) * a)) ∧
      h ^ (a * δ / 6) * (p.D * (v.finalWidth : ℝ)) ≤ h ^ (b + (1 + δ) * a) := by
  let h : ℝ := Nat.clog 2 n
  let τ := a * δ / 6
  have hτ : 0 < τ := by unfold τ; positivity
  have hh : 1 ≤ h := hv.2.1.le
  have hh' : 0 < h := zero_lt_one.trans_le hh
  let X := (m : ℝ) * (v.batch : ℝ) * h ^ (-a + τ)
  have hx : 0 ≤ X := by unfold X; positivity
  have hS : (2 : ℝ) ^ v.blocks * h ^ b ≤ v.batch := by
    unfold Levels.batch
    push_cast
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hv.2.2.2.2.1 (by positivity)
  obtain ⟨_, hctrl, hterm, hwidth⟩ := hcost
  have control : (p.overhead ^ v.j * v.allocation m : ℕ) * h ^ (c * a) ≤ X := calc
    _ ≤ (m : ℝ) * (2 : ℝ) ^ v.blocks * h ^ (p.groupRate * a + τ) * h ^ (c * a) := by gcongr
    _ = (m : ℝ) * (2 : ℝ) ^ v.blocks * h ^ (p.groupRate * a + τ + c * a) := by rw [Real.rpow_add hh' _ (c * a)]; ring
    _ ≤ (m : ℝ) * (2 : ℝ) ^ v.blocks * h ^ (b + (-a + τ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hh
      push_cast at small; linarith
    _ = m * ((2 : ℝ) ^ v.blocks * h ^ b) * h ^ (-a + τ) := by rw [Real.rpow_add hh']; ring
    _ ≤ X := by unfold X; gcongr
  have ext : (v.batch * e : ℕ) ≤ X := calc
    _ = (v.batch : ℝ) * e := Nat.cast_mul _ _
    _ ≤ v.batch * ((m : ℝ) * h ^ (-(2 * a))) := by gcongr
    _ = (m : ℝ) * v.batch * h ^ (-(2 * a)) := by ring
    _ ≤ X := by unfold X; gcongr; linarith
  have work : v.work m e h a c ≤ 3 * X := by
    unfold Levels.work
    change v.finalBudget m ≤ X at hterm
    linarith only [control, hterm, ext]
  constructor
  · calc
      _ ≤ h ^ τ * (h ^ τ * X) := mul_le_mul_of_nonneg_left
        (work.trans (mul_le_mul_of_nonneg_right large hx)) (by positivity)
      _ = (m : ℝ) * v.batch * h ^ (τ + (τ + (-a + τ))) := by
        rw [Real.rpow_add hh' τ, Real.rpow_add hh' τ]; unfold X; ring
      _ ≤ _ := by gcongr; dsimp [τ]; nlinarith
  · calc
      _ ≤ h ^ τ * h ^ (b + (1 + δ / 3) * a + τ) := mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = h ^ (τ + (b + (1 + δ / 3) * a + τ)) := (Real.rpow_add hh' _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hh (by unfold τ; nlinarith)

/-- One stage can accept any input dictionary for which installations
are supplied. Its output uses the fixed smaller dictionary bound. -/
theorem Levels.stage_of_installations {n c T₀ S : ℕ} {a b ξ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (small : (p.groupRate + c + 1 : ℕ) * a ≤ b)
    (hv : v.Suits n T₀ a b ξ) (hc : ∀ m, v.Costs n m a b (a * δ / 6))
    (hg : 3 ≤ (Nat.clog 2 n : ℝ) ^ (a * δ / 6))
    (h : ∀ (x y : Wire) (G : Diagram K x y) (m u : ℕ) (labels : Finset (Table K)),
      n ≤ m → (m : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ) → G.cost ≤ m →
      G.Admits u labels → labels.card ≤ S → (u : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ b →
      ((wd x + wd y : ℕ) : ℝ) ≤ m * (Nat.clog 2 n : ℝ) ^ (-(2 * a)) → v.Installed n m c a G.eval) :
    ArityStep K n S (Shaving.dictionary n) b δ a ξ := by
  intro x y k s u m hnet hu hs hl hm he
  obtain ⟨labels, hlabels, hnet⟩ := hnet
  obtain ⟨G, rfl, had, hsc⟩ := hnet.diagram
  obtain ⟨I, hfew, hsize, hwidth⟩ := h x y G m u labels hl hm (hsc.le.trans hs) had hlabels hu he
  obtain ⟨t, ht, hnet⟩ := I.labeled hfew
  obtain ⟨hc, hw⟩ := costs v ha hδ small hv (hc m) hg he
  have hpos : 1 ≤ v.batch := by unfold Levels.batch; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hbatch : (v.batch : ℝ) ≤ (n : ℝ) ^ ξ := by
    rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩
    exact h
  exact ⟨v.batch, t, I.u, hpos, hbatch, hnet, (Nat.cast_le.mpr ht).trans (hsize.trans hc), hwidth.trans hw⟩

/-- An encoding must supply *one* diagram after summing all branches.
The bound on short labels is shared with the next compression stage. -/
def Installable (F : Type) [Field F] : Prop :=
  ∀ δ β : ℝ, 0 < δ → δ ≤ 1 / 10 → 0 < β → β ≤ 1 / 2 →
    ∃ (p : Design δ) (A T₀ c : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra F L),
      ∀ a b ξ : ℝ, 0 < a → (p.groupRate + c + 1 : ℕ) * a < β → β ≤ b → b ≤ 1 / 2 → 0 < ξ →
      ∃ M : ℕ, ∀ᶠ n : ℕ in atTop, ∃ v : Levels p M, v.Suits n T₀ a b ξ ∧
        ∀ (K : Type) [Field K] [Fintype K] [Algebra L K] [Algebra F K] [IsScalarTower F L K],
          let h := Nat.clog 2 n
          A * (1 + h ^ 4) ^ A ≤ Fintype.card K → Fintype.card K ≤ h ^ (5 * A + 2) →
          ∀ (x y : Wire) (G : Diagram K x y) (m u : ℕ) (labels : Finset (Table K)),
            n ≤ m → (m : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ) → G.cost ≤ m →
            G.Admits u labels → labels.card ≤ Shaving.dictionary n → (u : ℝ) ≤ (h : ℝ) ^ b →
            ((wd x + wd y : ℕ) : ℝ) ≤ m * (h : ℝ) ^ (-(2 * a)) → v.Installed n m c a G.eval

theorem Installable.reduction {F : Type} [Field F] (install : Installable F) : ArityReduction F := by
  apply Shaving.UniformStage.reduction
  intro δ β hδ hδ' hβ hβ'
  obtain ⟨p, A, T₀, c, L, _, _, _, go⟩ := install δ β hδ hδ' hβ hβ'
  let q := p.groupRate + c + 1
  have hq : 1 ≤ (q : ℝ) := by unfold q; push_cast; linarith
  refine ⟨β / q, A, L, inferInstance, inferInstance, inferInstance, by positivity, ?_⟩
  intro a b ξ ha ha' hb hb' hξ
  have small : (q : ℝ) * a < β := by rwa [lt_div_iff₀ (by positivity), mul_comm] at ha'
  have ha1 : a ≤ 1 := by nlinarith
  have hτ : 0 < a * δ / 6 := by positivity
  obtain ⟨M, hm⟩ := go a b ξ ha small hb hb' hξ
  have hc := p.costs (M := M) (T₀ := T₀) (ξ := ξ) (b := b) hτ ha1 (by linarith)
  have grow := (tendsto_rpow_atTop hτ).comp Shaving.tendsto_height
  filter_upwards [hm, hc, grow.eventually_ge_atTop 3] with n hn hc hg K _ _ _ _ _
  dsimp only
  intro hlo hhi x y k s u m hnet hu hs hl hm he
  obtain ⟨v, hv, h⟩ := hn
  exact v.stage_of_installations ha hδ (small.le.trans hb) hv (hc v hv) hg (h K hlo hhi)
    x y k s u m hnet hu hs hl hm he

end OAI.LinearAlgebra.MatrixExponent.Rounds
