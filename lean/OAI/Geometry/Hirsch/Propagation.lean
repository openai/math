import OAI.Geometry.Hirsch.Route

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {I : Type} {L V h B : ℕ} {code : Bundles L V}

def Parameters.allow (par : Parameters code) := par.eps * par.lam / 4

theorem Parameters.allow_pos (par : Parameters code) : 0 < par.allow :=
  div_pos (mul_pos par.epos par.lpos) (by norm_num)

theorem Parameters.dpos (par : Parameters code) : 0 < par.delta := by linarith [par.lpos,par.lsmall]

structure Network (tree : Forest I (Fin V) h) (code : Bundles L V) where
  par : I → Parameters code
  cost : I → Values V
  size : I → ℝ
  positive : ∀ i, 0 < size i
  internal : ∀ i, tree.depth i < h → size i = (par i).allow
  margin : ∀ i j l, tree.path i = (j,l) :: tree.path j → 10 * (par j).delta < size i

namespace Network

variable {tree : Forest I (Fin V) h} (net : Network tree code)

def Good (path : List (I × Fin V)) : Prop :=
  ∀ e ∈ path, -(net.par e.1).delta ≤ net.cost e.1 e.2 ∧ net.cost e.1 e.2 < 0

theorem good_cons (j l tail) : net.Good ((j,l) :: tail) ↔
    (-(net.par j).delta ≤ net.cost j l ∧ net.cost j l < 0) ∧ net.Good tail := by
  simp [Good]

theorem parent_bound {i j l} (he : tree.path i = (j,l) :: tree.path j) : tree.depth j < h := by
  simpa [Forest.depth,he] using tree.bounded i

structure Track (i : I) (B : ℕ) where
  val : ℕ → Fin B → ℝ
  gap : ℕ → ℝ
  red : Fin B → ℝ
  raised : ∀ b, red b ≤ net.size (tree.node i (tree.depth i))
  floor : ∀ k ≤ tree.depth i, ∀ b, 0 ≤ val k b
  pair : ∀ k ≤ tree.depth i, ∀ b d, b ≠ d → gap k ≤ val k b + val k d
  gapLow : ∀ k ≤ tree.depth i, net.size (tree.node i k) ≤ gap k
  step : ∀ k (hk : k < tree.depth i) b,
    let j := tree.node i (k+1)
    val (k+1) b = (net.par j).eps * (net.cost j (tree.path i)[k].2 + val k b)
  stepGap : ∀ k < tree.depth i, gap (k+1) =
    (net.par (tree.node i (k+1))).eps * (net.par (tree.node i (k+1))).delta

namespace Track

variable {net} {i : I} (out : net.Track i B)

def Hit (b : Fin B) := out.val (tree.depth i) b = out.red b

theorem good_pos {k} (hk : k < tree.depth i) (hg : net.Good (tree.path (tree.node i k))) (b : Fin B) :
    0 < out.val k b := by
  rw [tree.step_node i hk,net.good_cons] at hg
  have hh := out.floor (k+1) hk b
  rw [out.step k hk] at hh
  have := nonneg_of_mul_nonneg_right hh (net.par _).epos
  linarith [hg.1.2]

theorem quick_pos (hg : net.Good (tree.path i)) {b : Fin B} (hr : 0 ≤ out.red b)
    (hf : out.red b ≤ out.val (tree.depth i) b) (hn : ¬out.Hit b) : 0 < out.val 0 b := by
  by_cases hh : 0 < tree.depth i
  · exact out.good_pos hh hg b
  · have he : tree.depth i = 0 := by omega
    rw [← he]
    exact hr.trans_lt (lt_of_le_of_ne hf (Ne.symm hn))

def Safe (k : ℕ) (b : Fin B) : Prop :=
  net.Good (tree.path (tree.node i k)) ∧
  (net.size (tree.node i k) < out.val k b ∨ ¬out.Hit b) ∧
  ∀ d, b ≠ d → out.gap k < out.val k b + out.val k d

theorem next_safe {k : ℕ} (hk : k < tree.depth i) (b : Fin B)
    (hh : out.Safe k b ∨
      (net.Good (tree.path (tree.node i (k+1))) ∧
        (net.par (tree.node i (k+1))).lam/4 < net.cost (tree.node i (k+1)) (tree.path i)[k].2)) :
    out.Safe (k+1) b := by
  let j := tree.node i (k+1)
  let par := net.par j
  let cost := net.cost j (tree.path i)[k].2
  have edge := tree.step_node i hk
  have margin : 10 * par.delta < net.size (tree.node i k) := net.margin _ _ _ edge
  have size : net.size j = par.allow := net.internal _ (parent_bound edge)
  have step : ∀ b, out.val (k+1) b = par.eps * (cost + out.val k b) := out.step k hk
  have both : net.Good (tree.path j) ∧ -par.delta ≤ cost ∧
      (par.lam/4 < cost + out.val k b ∨ ¬out.Hit b) := by
    rcases hh with ⟨hg,hl,_⟩ | ⟨hg,hc⟩
    · rw [edge,net.good_cons] at hg
      have hc : -par.delta ≤ cost := hg.1.1
      exact ⟨hg.2,hc,hl.imp_left (fun hv => by linarith [par.lsmall,par.dpos])⟩
    · change par.lam/4 < cost at hc
      exact ⟨hg,by linarith [par.lpos,par.dpos],Or.inl (by linarith [out.floor k hk.le b])⟩
  refine ⟨both.1,both.2.2.imp_left (fun hv => ?_),fun d hbd => ?_⟩
  · rw [size,step,Parameters.allow,mul_div_assoc]
    exact mul_lt_mul_of_pos_left hv par.epos
  · rw [out.stepGap k hk,step,step,← mul_add]
    apply mul_lt_mul_of_pos_left _ par.epos
    change par.delta < _
    linarith [out.pair k hk.le b d hbd,out.gapLow k hk.le,both.2.1,par.dpos]

theorem safe_run (speed : ℕ → Fin B → ℝ) (price : I → Values V)
    (start : ∀ b, speed 0 b ≠ 0 → out.Safe 0 b)
    (moving : ∀ j l, price j l ≠ 0 → net.Good (tree.path j) ∧ (net.par j).lam/4 < net.cost j l)
    (step : ∀ k (hk : k < tree.depth i) b,
      let j := tree.node i (k+1)
      speed (k+1) b = price j (tree.path i)[k].2 + (net.par j).eps * speed k b) :
    ∀ k ≤ tree.depth i, ∀ b, speed k b ≠ 0 → out.Safe k b := by
  intro k
  induction k with
  | zero => exact fun _ => start
  | succ k ih =>
    intro hk b hn
    apply out.next_safe hk b
    by_cases he : speed k b = 0
    · rw [step k hk,he,mul_zero,add_zero] at hn
      exact .inr (moving _ _ hn)
    · exact .inl (ih (by omega) b he)

theorem safe_floor {k b} (hk : k ≤ tree.depth i) (hs : out.Safe k b) :
    out.val k b ≠ if k = tree.depth i then out.red b else 0 := by
  split
  · rename_i he
    subst k
    exact hs.2.1.elim (fun hl => ((out.raised b).trans_lt hl).ne') id
  · exact (out.good_pos (by omega) hs.1 b).ne'

end Track
end Network
end OAI.Geometry.Hirsch.Layer
