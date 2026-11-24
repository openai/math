import OAI.Computability.VPVNP.DeterminantQueryBounds

/-!
# Continuation stack for scalar coefficient queries

A nonterminal query adds a sequence of products. The machine scans the sequence
in reverse index order and evaluates the two children of each product in turn.
Only one return frame is live per active level. The execution bound counts
push, pop and scalar-update transitions, and bounds the depth at every
intermediate configuration.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

/-- A terminal query supplies a scalar. A composite query supplies the number
of products in its sum and computes the two subqueries from the product index. -/
structure Program (Q R : Type*) where
  /-- Return the value of a leaf query or the number of product terms to evaluate for a branch. -/
  describe : Q → Sum R ℕ
  /-- Select the left factor query of the indexed product term. -/
  left : Q → ℕ → Q
  /-- Select the right factor query of the indexed product term. -/
  right : Q → ℕ → Q

variable {Q R : Type*} [Semiring R]

/-- Saved parent query, remaining scan count and partial sum, with the left factor value
retained while the right factor runs. -/
inductive Frame (Q R : Type*) where
  | left (q : Q) (remaining : ℕ) (accumulator : R)
  | right (q : Q) (remaining : ℕ) (accumulator leftValue : R)

/-- Current evaluator action, entering a query, scanning its sum, or returning a computed
value. -/
inductive Control (Q R : Type*) where
  | enter (q : Q)
  | scan (q : Q) (remaining : ℕ) (accumulator : R)
  | returned (value : R)

/-- Evaluator configuration consisting of the current control and the stack of suspended parent
frames. -/
abbrev Config (Q R : Type*) := Control Q R × List (Frame Q R)

namespace Program

variable (p : Program Q R)

/-- One call, return, or loop transition. At a terminal result the state is fixed. -/
def step : Config Q R → Config Q R
  | (.enter q, s) =>
    match p.describe q with
    | .inl r => (.returned r, s)
    | .inr t => (.scan q t 0, s)
  | (.scan _ 0 a, s) => (.returned a, s)
  | (.scan q (k + 1) a, s) => (.enter (p.left q k), .left q k a :: s)
  | (.returned v, .left q k a :: s) => (.enter (p.right q k), .right q k a v :: s)
  | (.returned v, .right q k a l :: s) => (.scan q k (a + l * v), s)
  | (.returned v, []) => (.returned v, [])

/-- A run of exactly `t` transitions, with at most `cap` saved frames
throughout. The endpoint also satisfies the cap. -/
inductive Runs (cap : ℕ) : ℕ → Config Q R → Config Q R → Prop
  | done (c : Config Q R) (hc : c.2.length ≤ cap) : Runs cap 0 c c
  | next {c d : Config Q R} {t : ℕ} (hc : c.2.length ≤ cap)
      (h : Runs cap t (p.step c) d) : Runs cap (t + 1) c d

theorem Runs.one {cap : ℕ} {c : Config Q R} (hc : c.2.length ≤ cap)
    (hn : (p.step c).2.length ≤ cap) : p.Runs cap 1 c (p.step c) :=
  .next hc (.done _ hn)

theorem Runs.join {cap m n : ℕ} {a b c : Config Q R}
    (hab : p.Runs cap m a b) (hbc : p.Runs cap n b c) : p.Runs cap (m + n) a c := by
  induction hab with
  | done => simpa using hbc
  | next hc _ ih => simpa only [Nat.succ_add] using Runs.next hc (ih hbc)

theorem Runs.iterate {cap t : ℕ} {a b : Config Q R} (h : p.Runs cap t a b) :
    p.step^[t] a = b := by
  induction h with
  | done => rfl
  | next _ _ ih => exact ih

/-- Scalar recurrence to be realized by the machine. -/
def Realizes (v : Q → R) : Prop := ∀ q, v q = match p.describe q with
  | .inl r => r
  | .inr t => ∑ k ∈ Finset.range t, v (p.left q k) * v (p.right q k)

/-- Both children of every actual call decrease the same depth bound. -/
def Descends (depth : Q → ℕ) : Prop :=
  ∀ q t, p.describe q = .inr t → ∀ k < t,
    depth (p.left q k) < depth q ∧ depth (p.right q k) < depth q

/-- Every branch described by the program has at most `b` product terms. -/
def ArityLE (b : ℕ) : Prop := ∀ q t, p.describe q = .inr t → t ≤ b

private theorem runScan (v : Q → R) (q : Q) (t childCost cap : ℕ)
    (s : List (Frame Q R)) (hs : s.length ≤ cap)
    (hl : ∀ k < t, ∀ a, ∃ n ≤ childCost, p.Runs cap n
      (.enter (p.left q k), .left q k a :: s)
      (.returned (v (p.left q k)), .left q k a :: s))
    (hr : ∀ k < t, ∀ a l, ∃ n ≤ childCost, p.Runs cap n
      (.enter (p.right q k), .right q k a l :: s)
      (.returned (v (p.right q k)), .right q k a l :: s))
    (hpush : 0 < t → s.length + 1 ≤ cap) (acc : R) :
    ∃ n ≤ 1 + t * (3 + 2 * childCost), p.Runs cap n (.scan q t acc, s)
      (.returned (acc + ∑ k ∈ Finset.range t, v (p.left q k) * v (p.right q k)), s) := by
  induction t generalizing acc with
  | zero =>
    exact ⟨1, by simp, by simpa [step] using Runs.one p (c := (.scan q 0 acc, s)) hs hs⟩
  | succ k ih =>
    let l := v (p.left q k)
    let r := v (p.right q k)
    have hcap := hpush (Nat.zero_lt_succ k)
    obtain ⟨x, hx, hrunL⟩ := hl k (Nat.lt_succ_self _) acc
    obtain ⟨y, hy, hrunR⟩ := hr k (Nat.lt_succ_self _) acc l
    obtain ⟨z, hz, hrunS⟩ := ih (fun j hj => hl j (Nat.lt_succ_of_lt hj))
      (fun j hj => hr j (Nat.lt_succ_of_lt hj)) (fun _ => hcap) (acc + l * r)
    have push := Runs.one p (c := (.scan q (k + 1) acc, s)) hs hcap
    have switch := Runs.one p (c := (.returned l, .left q k acc :: s)) hcap hcap
    have pop := Runs.one p (c := (.returned r, .right q k acc l :: s)) hcap hs
    refine ⟨1 + x + 1 + y + 1 + z, ?_, ?_⟩
    · exact show 1 + x + 1 + y + 1 + z ≤ _ by rw [Nat.succ_mul]; omega
    · have joined := ((((push.join p hrunL).join p switch).join p hrunR).join p pop).join p hrunS
      rw [Finset.sum_range_succ, add_comm _ (v (p.left q k) * v (p.right q k)), ← add_assoc]
      exact joined

/-- A clock and a simultaneous space bound for every invocation in any
continuation. The clock charges all control transitions. -/
theorem run_bounded (v : Q → R) (depth : Q → ℕ) (b : ℕ)
    (hv : p.Realizes v) (hd : p.Descends depth) (hb : p.ArityLE b)
    (d : ℕ) (q : Q) (hq : depth q ≤ d) (s : List (Frame Q R)) :
    ∃ t ≤ (5 + 6 * b) ^ (d + 1), p.Runs (s.length + d) t (.enter q, s) (.returned (v q), s) := by
  induction d generalizing q s with
  | zero =>
    have hcap : s.length ≤ s.length + 0 := by omega
    cases hdes : p.describe q with
    | inl r =>
      have he : v q = r := by simpa [hdes] using hv q
      exact ⟨1, by simp; omega, by simpa [step, hdes, he] using Runs.one p (c := (.enter q, s)) hcap (by simp [step, hdes])⟩
    | inr t =>
      have ht : t = 0 := by
        by_contra hn
        have := (hd q t hdes 0 (Nat.pos_of_ne_zero hn)).1
        omega
      subst t
      have he : v q = 0 := by simpa [hdes] using hv q
      have start := Runs.one p (c := (.enter q, s)) hcap (by simp [step, hdes])
      have finish := Runs.one p (c := (.scan q 0 0, s)) hcap hcap
      refine ⟨2, by simp; omega, ?_⟩
      simpa [step, hdes, he] using (start.join p (by simpa [step, hdes] using finish) : p.Runs _ (1+1) _ (.returned 0, s))
  | succ d ih =>
    have hcap : s.length ≤ s.length + (d + 1) := by omega
    cases hdes : p.describe q with
    | inl r =>
      have he : v q = r := by simpa [hdes] using hv q
      exact ⟨1, Nat.one_le_pow _ _ (by omega), by simpa [step, hdes, he] using Runs.one p (c := (.enter q, s)) hcap (by simp [step, hdes])⟩
    | inr t =>
      let w := (5 + 6 * b) ^ (d + 1)
      have hdepth : ∀ k < t, depth (p.left q k) ≤ d ∧ depth (p.right q k) ≤ d := by
        intro k hk
        have := hd q t hdes k hk
        omega
      have hs' (f : Frame Q R) : (f :: s).length + d = s.length + (d + 1) := by simp; omega
      obtain ⟨n, hn, rest⟩ := runScan p v q t w (s.length + (d+1)) s hcap
        (fun k hk a => by simpa only [hs'] using ih _ (hdepth k hk).1 (.left q k a :: s))
        (fun k hk a l => by simpa only [hs'] using ih _ (hdepth k hk).2 (.right q k a l :: s))
        (fun _ => by omega) 0
      have htb := hb q t hdes
      have hw : 1 ≤ w := Nat.one_le_pow _ _ (by omega)
      have hbw := Nat.mul_le_mul_left b hw
      have ht' := Nat.mul_le_mul_right (3 + 2 * w) htb
      have clock : 1 + n ≤ (5 + 6 * b) ^ (d + 1 + 1) := by
        rw [pow_succ]
        change 1 + n ≤ w * (5 + 6 * b)
        simp only [Nat.mul_add, Nat.mul_one] at hn ht' hbw
        nlinarith
      refine ⟨1 + n, clock, ?_⟩
      have he : v q = ∑ k ∈ Finset.range t, v (p.left q k) * v (p.right q k) := by
        simpa [hdes] using hv q
      have start := Runs.one p (c := (.enter q, s)) hcap (by simp [step, hdes])
      exact start.join p (by simpa [step, hdes, he] using rest)

end Program

end RankQuery.Stack

end VPVNP
end Computability
end OAI
