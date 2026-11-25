import OAI.Geometry.Hirsch.Foil

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

def depths (K cycles : ℕ) (hc : 0 < cycles) : ℕ → Board.Depths K
  | 0 => ⟨1,le_rfl⟩
  | k+1 => ⟨cycles*(2+(depths K cycles hc k).max),Nat.mul_pos hc (by omega)⟩

structure Dials where
  K : ℕ
  a : ℕ
  h : ℕ
  J : ℕ
  cycles : ℕ
  run : 0 < cycles
  tests : Thresholds K
  p : ℝ
  z : ℝ
  t : ℝ
  L : ℝ
  M : ℝ
  A : ℝ
  theta : ℝ
  gamma : ℝ

namespace Dials

variable (u : Dials)

def D := depths u.K u.cycles u.run
def rate (k : ℕ) := u.p*u.z^k
def margin (k : ℕ) := Real.exp (-8*u.L)^k
def cost (k : ℕ) := (k : ℝ)*((1+4^u.K)*u.tests.value u.K)
def err := Board.Ledger.factor u.a u.h ^ u.K * u.theta
def U := u.a*u.t
def loss := (u.K+1)*u.A*u.M
def key := (1+u.A)*u.p
def beta := 2*u.M*(u.K*(u.key+u.loss))
def capacity (k : ℕ) := Trial.Tests.capacity u.K (u.D k).max (u.D k).step
def error (k : ℕ) := u.capacity k*u.U*u.z^u.K + (u.K+1)*u.loss

structure Valid : Prop where
  keys : 2 ≤ u.K
  base : 2 ≤ u.a
  initial : 0 < u.p
  initial_le : u.p ≤ u.t
  target : u.t ≤ 1
  thin : 0 < u.z
  thin_le : u.z ≤ 1
  lambda : 0 ≤ u.L
  mass : 0 ≤ u.M
  link : 0 ≤ u.A
  scale : 0 < u.theta
  passage : 0 < u.gamma
  crude : u.U ≤ u.tests.value 0
  reliable : ∀ k ≤ u.h, u.gamma ≤ u.margin k ^ u.K - 2*u.K*u.cost (k+1)
  bounds : ∀ k < u.h, u.capacity k*u.U ≤ u.gamma*u.M ∧
    u.capacity k*(u.tests.value u.K+(u.K*(u.D k).max+(u.D k).step+1)*u.p) ≤ u.gamma*u.A
  compare : 3*u.beta < u.theta^2
  discard : u.key+u.loss ≤ u.theta
  rare : u.err ≤ u.t/32
  bins : u.M < price u.t u.J
  small : ∀ k < u.h, 2*u.p + u.error k + u.err + u.K*u.p*u.M ≤ u.t/4
  contraction : u.K*Real.exp (-u.L) ≤ 1/2
  stop : (u.K*Real.exp (-u.L))^u.cycles ≤ u.t/2

namespace Valid

variable {u} (v : u.Valid)
include v

theorem tpos : 0 < u.t := v.initial.trans_le v.initial_le
theorem crude_pos : 0 < u.U := mul_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) v.base) v.tpos
theorem rate_pos (k : ℕ) : 0 < u.rate k := mul_pos v.initial (pow_pos v.thin _)
theorem rate_le (k : ℕ) : u.rate k ≤ u.p := mul_le_of_le_one_right v.initial.le (pow_le_one₀ v.thin.le v.thin_le)
theorem loss_pos : 0 ≤ u.loss := mul_nonneg (mul_nonneg (by positivity) v.link) v.mass
theorem err_pos : u.theta ≤ u.err :=
  le_mul_of_one_le_left v.scale.le (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))
theorem error_pos (k : ℕ) : 0 ≤ u.error k := by
  have := v.crude_pos
  have := v.thin
  have := v.loss_pos
  unfold error; positivity

end Valid

theorem cost_succ (k : ℕ) : u.cost (k+1) = u.cost k + (1+4^u.K)*u.tests.value u.K := by
  unfold cost; push_cast; ring

abbrev Scale := Fin u.h → Bool
abbrev Bin := Option (Fin u.J)

def dir (east : Bool) (bin : u.Bin) := if bin.isSome then east else !east

end Dials

namespace Board

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw : coin.Raw I} {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k : ℕ} {u : Dials}

structure Stage (tag : Stamp Bit I) (u : Dials) (k : ℕ) (rule : Rules raw) (old : w.Round) (d : Bool) : Prop where
  rate : raw.rate = u.rate k
  visible : tag.Visible w rule k (u.a^k)
  capped : tag.Capped rule old (!d) (u.a^k) (u.D k).step u.t
  reliable : rule.Reliable w.place u.K (u.margin k) (u.cost k)

namespace Stage

variable {rule : Rules raw} {old : w.Round} {d : Bool}
  (G : Stage tag u k rule old d) (v : u.Valid)

def bad (u : Dials) (k : ℕ) (rule : Rules raw) (old : w.Round) (d : Bool) :=
  Stamp.bad rule old (!d) (u.a^(k+1)) (u.D k).step

def screened (u : Dials) (k : ℕ) (rule : Rules raw) (old : w.Round) (d : Bool) :=
  rule.screen u.tests (bad u k rule old d)

include G v in
theorem merge : tag.Capped rule old (!d) (u.a^(k+1)) (u.D k).step u.U := by
  rw [pow_succ]; exact G.capped.merge (by have := v.base; omega)

include G in
theorem view : tag.Visible w (screened u k rule old d) k (u.a^(k+1)) := by
  apply Stamp.Visible.screen
  rw [pow_succ]; exact G.visible.enlarge _

include G v in
theorem checked : (screened u k rule old d).Reliable w.place u.K (u.margin k) (u.cost (k+1)) := by
  rw [u.cost_succ]
  exact rule.reliable_screen _ _ G.reliable (fun g s _ hs => ((G.merge v).given g s hs).trans v.crude)

def gate (hk : k ≤ u.h) := (G.checked v).gates (v.reliable k hk) u.tests (bad u k rule old d)
  (fun _ _ h => h.2)

include G v in
theorem crude (hide s : Finset I) (hs : s ⊆ hide) (j : ℕ) (i : I) (hi : w.place i ∈ piece (u.a^(k+1)) j) :
    coin.law.prob (old.Cover (piece (u.a^(k+1)) j) (!d) (u.D k).step
      ((screened u k rule old d).watch hide s) i) ≤ u.U := by
  apply le_trans _ (((G.merge v) hide s hs j).bound i hi)
  apply coin.law.mono
  intro x hc
  exact hc.mono (Finset.sdiff_subset_sdiff (rule.screen_pass ..) Finset.Subset.rfl)

theorem ledger (hk : k < u.h) (j : ℕ) :
    Ledger (G.gate v hk.le) old (piece (u.a^(k+1)) j) d (u.D k) u.M u.A := by
  have h := v.bounds k hk
  have hr : raw.pins.rate ≤ u.p := G.rate.le.trans (v.rate_le k)
  apply Ledger.make v.passage (u.tests.positive _).le v.mass v.link
    ((G.checked v).resample _ _ _ _) h.1 ?_ ?_ ?_
  · apply le_trans _ h.2
    unfold Dials.capacity
    gcongr
  · intro x g hg hn
    rw [← w.home_eq hg]
    exact Stamp.available rule u.tests hn
  · intro i hi
    have hh := G.crude v ∅ ∅ Finset.Subset.rfl j i hi
    apply le_trans _ hh
    apply coin.law.mono
    intro x hc
    simp only [Round.Cover,Rules.watch,Raw.force_empty,Finset.sdiff_empty]
    exact hc

end Stage
end Board
end OAI.Geometry.Hirsch.Layer
