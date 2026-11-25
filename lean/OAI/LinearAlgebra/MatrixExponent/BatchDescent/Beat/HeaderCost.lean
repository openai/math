import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Issue
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Length
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.ResetRate
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.TraceNet
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.One
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Network
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transform

/-! # A common description for all branches of one wire-saving step -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly Assembly.History
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} (P : Gadget F)
  (S : Setup F x y) (T : Template F) (z : ℕ) (hz : 0 < z) (Δ : ℕ) (R : Budget) (a : ℕ)

def k := Nat.clog 2 (256 * (coreBins Δ + 1))
def b := Nat.clog 2 (Fintype.card (Branches.Tag P))
def gain := 10 * (4 * Δ) ^ 300 * 2 ^ (k Δ)
def e := Nat.clog 2 (gain Δ * R.load)
def c := Nat.clog 2 (2 ^ S.discount * (gain Δ * R.load) * S.U + 1)

abbrev meter := Template.Meter.bounded (c S Δ R) 1 (1 / (2 : ℝ) ^ S.discount)
abbrev book := Book.make T.scheme P z hz T.order {S.U}
abbrev cap := (book P S T z hz).overhead (e Δ R) + R.tag * (2 ^ S.discount * (gain Δ * R.load))
abbrev next := T.after a Δ (degreeBound S T Δ) (book P S T z hz) (e Δ R)
  (cap P S T z hz Δ R) (meter S Δ R)
abbrev added := (Post.headerFmt (T.degree a Δ (degreeBound S T Δ)) (e Δ R)
  (book P S T z hz).d).width + (book P S T z hz).overhead (e Δ R)

theorem choices : Fintype.card (Branches.Tag P) ≤ 2 ^ (b P) := Nat.le_pow_clog (by decide) _

theorem bins : 256 * (coreBins Δ + 1) ≤ 2 ^ (k Δ) := Nat.le_pow_clog (by decide) _

theorem positive : 1 ≤ k Δ := by
  have := bins Δ
  by_contra! h
  rw [show k Δ = 0 by omega, pow_zero] at this
  omega

omit [Field F] in
theorem degree_le : Δ ≤ degreeBound S T Δ :=
  (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Format widths and hardware costs for one batch step -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly Coloring
variable {F : Type} [Field F] {x y : Wire} (P : Gadget F)
  (S : Setup F x y) (T : Template F) (z : ℕ) (hz : 0 < z) (Δ : ℕ) (R : Budget) (r : ℕ)

local notation "a" => (T.scheme.h - r)
local notation "n" => (T.scheme.h - a)
local notation "C" => degreeBound S T Δ
local notation "m" => T.scheme.m
local notation "d" => T.scheme.d
local notation "q" => ((d + 1) * n)
local notation "Y" => next P S T z hz Δ R a
local notation "M" => book P S T z hz
local notation "𝓔" => e Δ R
local notation "𝓒" => cap P S T z hz Δ R
local notation "𝓚" => meter S Δ R

abbrev In := (S.format T).pair (T.Candidate a (b P))
abbrev Saved := Trail.source T.scheme S.h S.d S.e
abbrev Mid := (T.Headed a (b P) Δ C).pair (Saved S T)

def accessCost (j v : ℕ) := 1000000 * 2 ^ j * (j + v + 1)
def parcel := (Group.Parcel d a n T.count).width
def labels := (Window.LabelSet a n).width
def walk := 2 ^ a * (Window.Walks 8 d (T.WithCount a (b P))).width
def origin := (Trail.rowFormat T.scheme S.h S.d S.e).width
def precision := T.size a + 2 ^ (Window.Tile.radius d + (n + 1)) + 2 ^ (T.degree a Δ C)
def profile := 2 ^ (b P) + 4 * P.b

def prepareCost := T.prepareCost a (b P) (parcel T r) (accessCost (m + q) (parcel T r))
  (labels T r) (accessCost (m + d) (labels T r))
def headedCost := T.headedCost a (b P) Δ C (profile P)
def issueCost := T.issueCost a (b P) Δ C M 𝓔 𝓒 𝓚 (T.Pointers 𝓔)
  (walk P T r) (accessCost (m + d) (walk P T r)) (precision S T Δ r)

def markWidth := (T.PollRow a (b P)).width + (Side.Input (n + T.scheme.e) (b P)).width
def issueWidth := T.issueWidth a (b P) Δ C M 𝓔 𝓒 𝓚 (T.Pointers 𝓔)
def arity := T.arity a (b P) + markWidth P T r + issueWidth P S T z hz Δ R r + 2 * (Y).scheme.ℓ

def firstCost := 100 * (In P S T r).width + prepareCost P T r + headedCost P S T Δ r
def secondCost := 100 * (Mid P S T Δ r).width + issueCost P S T z hz Δ R r +
  Trail.gatherBound T.scheme (Y).scheme S.h S.d S.e (origin S T) (accessCost (m + d) (origin S T)) +
  Trail.carryCost T.scheme (Y).scheme (d + 1) S.h S.d S.d S.e (Mid P S T Δ r) (Y).format
def totalCost := firstCost P S T Δ r + secondCost P S T z hz Δ R r +
  4 * (T.Candidate a (b P)).width + Snapshot.sweepCost S Y

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Numerical bounds for exchanges with dynamically addressed neighbors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Assembly Packing Phase Phase.Case

variable {F : Type} [Field F] (b d : ℕ)
  {j v : Case F b d → ℕ} (hj : Short (fun i => 2 ^ (j i))) (hv : Case.Row v)
local notation "I" => Case F b d

include hj hv

private theorem packet_bound : Cost (fun i : I => 2 ^ (i.m + j i) * (i.m + j i + v i + 1)) :=
  Row.expand (((Long.row (hosts.add hj.long.of_exp)).add hv).add (long_const 1).row) hj

theorem access_bound : Cost (fun i : I => accessCost (i.m + j i) (v i)) := by
  refine ((packet_bound b d hj hv).scale 1000000).mono fun i => ?_
  rw [accessCost, mul_assoc]

theorem gather_bound : Cost (fun i : I => gatherCost i.m (j i) (v i) (accessCost (i.m + j i) (v i))) := by
  have hi : Long (fun i : I => (100 + (i.m + j i + 3 * i.m + 1)) ^ 200) :=
    ((long_const 100).add (((hosts.add hj.long.of_exp).add ((long_const 3).mul hosts)).add (long_const 1))).pow _
  refine ((((access_bound b d hj hv).scale 4).add ((hi.row.expand hj).scale 4)).add
    ((packet_bound b d hj hv).scale 1100)).mono fun i => ?_
  rw [gatherCost, mul_assoc 1100]

theorem read_bound : Cost (fun i : I => Window.readCost i.m (j i) (v i) (accessCost (i.m + j i) (v i))) :=
  (gather_bound b d hj hv).add ((Row.hosts (((hosts.row.add hv).left hj).add hv)).scale 1000)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Electing the common layout and matching in an encoded batch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ)

local notation "a" => (T.scheme.h - r)
local notation "C" => degreeBound S T Δ
local notation "cost" => ((R.load : ℝ) * S.z)

include h in
theorem scale_le : S.z ≤ z := Nat.le_of_dvd h.vpos h.divides

include h in
theorem reserve : 0 < S.U := (Nat.mul_pos P.pos h.vpos).trans_le h.ceiling

include h in
theorem slack_pos : 0 ≤ σ :=
  nonneg_of_mul_nonneg_left (le_trans (by positivity) h.slack) (by positivity)

include h in
theorem enough (hK : 2 ^ (k Δ) ≤ K) : k Δ ≤ T.scheme.h - a := by
  rw [Nat.sub_sub_self h.group]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hK.trans h.room)

include h in
theorem slack (hK : 2 ^ (k Δ) ≤ K) (v : ℕ) (hv : v ≤ 2 ^ T.scheme.m) :
    (2 : ℝ) ^ (k Δ) * cost * (v * 2 ^ a : ℕ) ≤ σ := by
  apply le_of_mul_le_mul_right _ (show (0 : ℝ) < 2 ^ r by positivity)
  apply le_trans _ h.slack
  push_cast
  rw [mul_assoc, mul_assoc (v : ℝ), ← pow_add, Nat.sub_add_cancel h.group, pow_add]
  gcongr
  · exact_mod_cast hK
  · exact_mod_cast hv

include h in
theorem delayed : T.scheme.h - a ≤ 32 * Nat.clog 2 (2 * C) := by
  have hh : 2 ^ S.h ≤ 2 * C := by
    unfold degreeBound
    have := Nat.two_pow_pos T.scheme.m
    have := Nat.two_pow_pos S.h
    omega
  have ht := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hh.trans (Nat.le_pow_clog (by decide : 1 < 2) _))
  have := h.height
  omega

variable (q : (frame S T (P.b * z) Δ R).state)

abbrev Poll := T.Selection a (Nat.sub_le _ _) (b P) (k Δ) cost Δ C q.val.encodes σ
  (Nat.mul_pos P.pos h.vpos)

theorem elect (hd : 0 < Δ) (hk : 2 ^ (k Δ) ≤ K) : Nonempty (Poll h q) := by
  have hv : Fintype.card q.val.G.V ≤ 2 ^ T.scheme.m := by
    simpa using Fintype.card_le_of_injective _ q.val.encodes.post.host.injective
  have hl : 0 < cost := by exact_mod_cast (Nat.mul_pos P.pos h.vpos).trans_le h.load
  exact T.selection a (Nat.sub_le _ _) (b P) (k Δ) cost Δ C q.val.encodes σ _
    hd (hd.trans_le (degree_le S T Δ)) (positive Δ) (enough h hk) hl q.property.bounded
    (bins Δ) (slack h hk _ hv) (fun _ => delayed h)

abbrev Ticket := T.Branch P a (Nat.sub_le _ _) (b P) (k Δ) cost Δ C z σ (Nat.mul_pos P.pos h.vpos)

def ticket (s : Poll h q) (i : s.choices) : Ticket (Δ := Δ) h where
  T := Stack.Outer S.input S.output
  x := S.input
  y := S.output
  L := S.fringe
  G := q.val.G
  r := q.val.rows
  p := q.val.encodes
  s := s
  i := i
  v := ((Classical.choice q.property.live, 0), ⟨0, 0⟩)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Validation and permutation ranges for a batch of wire-saving gadgets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ)

local notation "a" => (T.scheme.h - r)
local notation "C" => degreeBound S T Δ
local notation "Y" => next P S T z h.vpos Δ R a
local notation "n" => (T.scheme.h - a)
local notation "j" => (T.scheme.m + T.scheme.d)
local notation "q" => (T.scheme.m + (T.scheme.d + 1) * n)
local notation "cost" => ((R.load : ℝ) * S.z)

def scale (Δ : ℕ) := 3 + arity P S T z h.vpos Δ R r + 2 * 2 ^ (2 * w) * (4 * w)

def tables (Δ : ℕ) (gate : Table F) :=
  insert gate (insert (Snapshot.sweepTable (next P S T z h.vpos Δ R a))
    (insert (T.markTable a (b P)) (T.keys a (b P) (k Δ) cost Δ (degreeBound S T Δ))))

abbrev allowed (Δ : ℕ) (gate : Table F) := Allowed F w ∪ (tables h Δ gate : Set (Table F))

theorem three : 3 ≤ scale h Δ := (Nat.le_add_right ..).trans (Nat.le_add_right ..)

theorem fits : arity P S T z h.vpos Δ R r ≤ scale h Δ :=
  (Nat.le_add_left ..).trans (Nat.le_add_right ..)

variable (gate : Table F) (hk : 2 ^ (k Δ) ≤ K) (hd : d + 1 ≤ K)

include hk hd in
theorem access (v : ℕ) : Access F (scale h Δ) (allowed h Δ gate) j v (accessCost j v) ∧
    Access F (scale h Δ) (allowed h Δ gate) q v (accessCost q v) := by
  have hh : q ≤ 2 * w := by
    refine le_trans ?_ h.upper
    exact Nat.add_le_add_left (Nat.mul_le_mul ((Nat.add_le_add_right h.degree 1).trans hd)
      ((Nat.sub_le ..).trans (h.height.trans (Nat.le_add_right ..)))) _
  have hpos := (positive Δ).trans (enough h hk)
  have hj : j ≤ q := Nat.add_le_add_left
    ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hpos)) _
  have hw : 0 < w := by
    have hq : 0 < q := Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) hpos) (Nat.le_add_left ..)
    omega
  have read (i : ℕ) (hl : w ≤ i) (hr : i ≤ 2 * w) :
      Access F (scale h Δ) (allowed h Δ gate) i v (accessCost i v) := by
    have size : 2 * 2 ^ i * (4 * w) ≤ scale h Δ := by
      refine le_trans ?_ (Nat.le_add_left ..)
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr))
    exact (exchange F v hw hl hr size).widen le_rfl (fun _ ht => Or.inl (sort_allowed ht))
  exact ⟨read _ (h.lower.trans (Nat.le_add_right ..)) (hj.trans hh), read _ (h.lower.trans (Nat.le_add_right ..)) hh⟩

variable (s : ∀ t : (frame S T (P.b * z) Δ R).state, Poll h t)

def start (i : (frame S T (P.b * z) Δ R).state) (l : (T.Candidate a (b P)).obj) : (Mid P S T Δ r).obj :=
  T.start P a (Nat.sub_le ..) (b P) (k Δ) cost Δ C (Trail.format T.scheme S.h S.d S.e) (i.val.code, l)

include hk hd in
theorem first : Computes F (scale h Δ) (allowed h Δ gate) (In P S T r) (Mid P S T Δ r)
    (fun t : (frame S T (P.b * z) Δ R).state × (T.Candidate a (b P)).obj => (t.1.val.code, t.2))
    (fun t => start (P := P) (r := r) t.1 t.2)
    (fun t => if (((s t.1).selector (choices P)).read t.2).isSome then 1 else 0)
    (firstCost P S T Δ r) := by
  have fit := fits (Δ := Δ) h
  unfold arity at fit
  let X (t : (frame S T (P.b * z) Δ R).state × (T.Candidate a (b P)).obj) : (In P S T r).obj :=
    (t.1.val.code, t.2)
  have allow : (T.keys a (b P) (k Δ) cost Δ C : Set _) ⊆ allowed h Δ gate :=
    fun _ ht => Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht)))
  have ar : markWidth P T r ≤ scale h Δ := by omega
  have hp : 4 * P.b ≤ 2 ^ (profile P) := (Nat.le_add_left ..).trans (Nat.lt_two_pow_self.le)
  have all := T.start_net P a (Nat.sub_le ..) (b P) (k Δ) cost Δ C (Trail.format T.scheme S.h S.d S.e)
    (three h) ((positive Δ).trans (enough h hk)) (access h gate hk hd (parcel T r)).2 le_rfl
    (access h gate hk hd (labels T r)).1 le_rfl (by omega) allow ar
    (Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))))
    (profile P) (Nat.le_add_right ..) hp X (fun t => t.1.val.encodes.reciprocal)
  obtain ⟨f, hf, he⟩ := all
  refine ⟨f, hf, fun t v => ?_⟩
  refine (he t v).trans ?_
  have hw := (s t.1).valid_eq (choices P) t.2
  change (if start (P := P) (r := r) t.1 t.2 = v then T.valid a (b P) P
    (T.prepared a (Nat.sub_le ..) (b P) (k Δ) cost Δ C (t.1.val.rows, t.2)) else 0) = _
  rw [hw]
  dsimp only
  cases ((s t.1).selector (choices P)).read t.2 <;> rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Polynomial description lengths for one wire-saving step -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Assembly History Packing Phase Phase.Case Coloring
open scoped Classical

variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

private theorem log_bound (x y z : ℕ) (h : z ≤ (x + 1) * (1 + y)) :
    Nat.clog 2 z ≤ x + Nat.clog 2 (1 + y) := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  exact h.trans (Nat.mul_le_mul Nat.lt_two_pow_self (Nat.le_pow_clog (by decide) _))

theorem spans_bound : Base (fun i : I => 2 ^ e Δ i.R) :=
  ((base_const (gain Δ)).mul load).exp_clog

theorem history_factor : Base (fun i : I => 2 ^ i.S.discount * (gain Δ * i.R.load)) :=
  discount.mul ((base_const (gain Δ)).mul load)

theorem meter_bound : Base (fun i : I => (meter i.S Δ i.R).count) := by
  refine (base_const 3).mul (((history_factor P Δ d).add Case.units).mono fun i => ?_)
  exact log_bound _ _ _ (by simp only [add_mul, mul_add, one_mul, mul_one]; omega)

def maxDegree := (d + Nat.clog 2 ((4 * Δ) ^ 300) + 1) * 3

theorem child_degree (i : I) :
    i.T.degree i.a Δ (degreeBound i.S i.T Δ) ≤ maxDegree Δ d := by
  simp only [Template.degree, Template.bound, i.h.core, Bool.false_eq_true, ↓reduceIte]
  exact Nat.mul_le_mul_right 3 (Nat.add_le_add_right (Nat.add_le_add i.h.degree (min_le_right ..)) 1)

theorem child_slots : Base (fun i : I => 2 ^ i.T.degree i.a Δ (degreeBound i.S i.T Δ)) :=
  (base_const (2 ^ maxDegree Δ d)).mono fun i => Nat.pow_le_pow_right (by decide) (child_degree P Δ d i)

private theorem role_bound : Rate (fun i : I => Kind.width i.T.scheme P (i.T.scheme.e + 2)) := by
  have h : Rate (fun i : I => 1 + (Fintype.card (Role P) + 2 ^ (i.T.scheme.e + 2))) :=
    (rate_const 1).add ((rate_const _).add (spans.exp_add (rate_const (2 ^ 2))))
  refine ((h.add (rate_const 1)).clog).mono fun i => ?_
  simp only [Kind.width, Kind.Small, Fintype.card_sum, Fintype.card_fin, Dense.used, i.h.single, pow_zero]
  rfl

theorem overhead_bound : Rate (fun i : I => (book P i.S i.T i.v i.h.vpos).overhead (e Δ i.R)) := by
  have he := (spans_bound P Δ d).rate
  have hs : Rate (fun i : I => 2 ^ (book P i.S i.T i.v i.h.vpos).s) :=
    (spans.exp_add (rate_const (2 ^ 2))).exp_add (rate_const (2 ^ Nat.clog 2 (P.b + 1)))
  have hd : Rate (fun i : I => (book P i.S i.T i.v i.h.vpos).d) := by
    simpa only [book, Book.make, Book.lenBits, Finset.card_singleton] using
      (rate_const (Nat.clog 2 (1 + 3)) : Rate (fun _ : I => _))
  have hr := role_bound P d
  have hl : Rate (fun i : I => Dense.used (i.T.scheme.ℓ + Kind.width i.T.scheme P (i.T.scheme.e + 2))) :=
    (hr.add lengths).mono fun i => log_bound _ _ _ (by simp only [add_mul, mul_add, one_mul, mul_one]; omega)
  have hw := (he.mul hd).add (he.mul ((rate_const 1).add
    ((rate_const 0).add (hs.mul ((rate_const 1).add (he.of_exp.add hd))))))
  refine ((hw.add (he.mul hl)).add (he.mul hr)).mono fun i => ?_
  rw [Book.overhead, Post.bookkeeping, Dense.overhead, width_code]

theorem added_bound : Rate (fun i : I => added P i.S i.T i.v i.h.vpos Δ i.R i.a) := by
  have he := (spans_bound P Δ d).rate
  have hq := (child_slots P Δ d).rate.of_exp
  have hd : Rate (fun i : I => (book P i.S i.T i.v i.h.vpos).d) := by
    simpa only [book, Book.make, Book.lenBits, Finset.card_singleton] using
      (rate_const (Nat.clog 2 (1 + 3)) : Rate (fun _ : I => _))
  have h := (rate_const 1).add (he.mul (hd.add ((rate_const 1).add ((rate_const 1).add (hq.add he.of_exp)))))
  refine (h.add (overhead_bound P Δ d)).mono fun i => ?_
  simp only [added, Post.headerFmt, Post.field, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]

theorem bits_bound : ∃ k : ℕ, ∀ i : I,
    (next P i.S i.T i.v i.h.vpos Δ i.R i.a).scheme.ℓ ≤ (1 + i.R.tag) * i.rate ^ k := by
  obtain ⟨k, h⟩ := ((added_bound P Δ d).add (history_factor P Δ d).rate).bound
  refine ⟨k, fun i => ?_⟩
  let t := added P i.S i.T i.v i.h.vpos Δ i.R i.a
  let f := 2 ^ i.S.discount * (gain Δ * i.R.load)
  calc
    _ = t + i.R.tag * f := by
      change (Post.record _ _ _ (.addr _)).width = _
      simp only [t, f, added, cap, Post.record, Post.headerFmt, Format.width_pair, Format.width_addr, add_assoc]
    _ ≤ (1 + i.R.tag) * (t + f) := by simp only [add_mul, mul_add, one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (h i)

theorem next_bits : Short (fun i : I => (next P i.S i.T i.v i.h.vpos Δ i.R i.a).scheme.ℓ) := by
  obtain ⟨k, h⟩ := bits_bound P Δ d
  exact (((short_const 1).add tags).mul ((Poly.of_le short_two rate_short).pow k)).mono h

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Widths of the local lookup tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Assembly History Packing Phase Phase.Case Coloring Window

variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

theorem child_factor : Short (fun i : I => 2 ^ (i.n + 1)) :=
  tiles.rate.short.exp_add (short_const (2 ^ 1))

theorem seat_factor : Short (fun i : I => 2 ^ (i.n + i.T.scheme.e)) :=
  tiles.rate.short.exp_add spans.short

theorem radius_factor : Short (fun i : I => 2 ^ (Tile.radius i.T.scheme.d)) :=
  (short_const (2 ^ (Tile.radius d))).mono fun i =>
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.add_le_add_right i.h.degree 1))

theorem mask_factor : Short (fun i : I => 2 ^ (Tile.radius i.T.scheme.d + (i.n + 1))) :=
  (radius_factor P d).exp_add (child_factor P d)

theorem source_bound : Short (fun i : I => (i.T.Source i.a (b P)).width) := by
  have hn : Short (fun i : I => 2 ^ i.n) := tiles.rate.short
  have he : Short (fun i : I => 2 ^ i.T.scheme.e) := spans.short
  have hd : Short (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.rate.short
  have hw := (child_factor P d).of_exp
  have occ := hw.add (he.mul ((short_const 1).add (hd.of_exp.add he.of_exp)))
  have mat := (hn.mul (short_const 1)).add ((hn.mul occ).add (hn.mul (hd.mul hw)))
  refine ((hn.mul Case.bits).add (((seat_factor P d).mul (short_const (b P))).add mat)).mono fun i => ?_
  simp only [Template.Source, Window.Source, Match.Input, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit, Format.width_addr (i.T.scheme.h - i.a + 1)]

theorem count_bound : Short (fun i : I => (i.T.WithCount i.a (b P)).width) := by
  refine ((source_bound P d).add (tiles.rate.short.mul counters)).mono fun i => ?_
  rw [Template.WithCount, Format.width_pair, Format.width_vec, Format.width_addr]

theorem pollRow_bound : Short (fun i : I => (i.T.PollRow i.a (b P)).width) := by
  refine ((short_const 1).add (source_bound P d)).mono fun i => ?_
  rw [Template.PollRow, Format.width_pair, Format.width_bit]

theorem side_bound : Short (fun i : I => (Side.Input (i.n + i.T.scheme.e) (b P)).width) := by
  refine ((seat_factor P d).mul (short_const (Side.Entry (b P)).width)).mono fun i => ?_
  rw [Side.Input, Format.width_vec]

theorem markWidth_bound : Short (fun i : I => markWidth P i.T i.r) :=
  (pollRow_bound P d).add (side_bound P d)

theorem pointers_bound : Short (fun i : I => (i.T.Pointers (e Δ i.R)).width) := by
  have hh : Short (fun i : I => i.height) := levels.rate.short.mono fun i => i.h.height
  have hd : Short (fun i : I => i.T.scheme.d + 1) := Case.slots.rate.short.of_exp.add (short_const 1)
  have hp := (short_const 1).add (hd.add (hh.add ((short_const 0).add spans.short.of_exp)))
  refine ((spans_bound P Δ d).rate.short.mul hp).mono fun i => ?_
  simp only [Template.Pointers, Trail.pointer, Format.width_pair, Format.width_vec, Format.width_addr, pow_zero, one_mul]
  rw [i.h.single, Format.width_bit, Format.width_addr (i.T.scheme.d + 1)]

theorem label_bound : Short (fun i : I => (i.T.Label i.a Δ (degreeBound i.S i.T Δ)
    (book P i.S i.T i.v i.h.vpos) (e Δ i.R) (cap P i.S i.T i.v i.h.vpos Δ i.R)
    (meter i.S Δ i.R) (i.T.Pointers (e Δ i.R))).width) := by
  refine ((next_bits P Δ d).add ((meter_bound P Δ d).rate.short.add (pointers_bound P Δ d))).mono fun i => ?_
  rw [Template.Label, Format.width_pair, Format.width_pair, Format.width_addr, Format.width_addr]

theorem mask_bound : Short (fun i : I => (Tile.mask i.T.scheme.d i.n
    (i.T.degree i.a Δ (degreeBound i.S i.T Δ))).width) := by
  have h := mask_factor P d
  refine (h.mul ((child_slots P Δ d).rate.short.mul h)).mono fun i => ?_
  simp only [Tile.mask, Format.width_vec]
  rw [Format.width_bit, mul_one]

theorem word_bound : Short (fun i : I => (Tile.word i.T.scheme.d i.a i.n
    (i.T.degree i.a Δ (degreeBound i.S i.T Δ)) (i.T.WithCount i.a (b P))).width) := by
  have h := mask_factor P d
  have hw := (short_const 2).add (groups.rate.short : Short (fun i : I => i.a))
  refine (((hw.add (child_factor P d).of_exp).add (h.mul ((child_slots P Δ d).rate.short.mul h))).add
    ((radius_factor P d).mul (count_bound P d))).mono fun i => ?_
  rw [Tile.width]

theorem issueWidth_bound : Short (fun i : I => issueWidth P i.S i.T i.v i.h.vpos Δ i.R i.r) :=
  (word_bound P Δ d).add (label_bound P Δ d)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # The next frame of a contraction satisfies the host and block bounds -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Phase Phase.Case
variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

theorem child_bound : Child (fun i : I => next P i.S i.T i.v i.h.vpos Δ i.R i.a)
    (fun i => i.n + 1) :=
  ⟨fun _ => Nat.sub_le .., fun _ => le_rfl, child_factor P d, fun _ => rfl,
    (spans_bound P Δ d).rate.short, (child_slots P Δ d).rate.short,
    next_bits P Δ d, (meter_bound P Δ d).rate.short⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Arity of a grouping and voting table -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat

open Assembly Packing Phase Phase.Case Coloring

variable {F : Type} [Field F] (P : Gadget F) (d : ℕ)
local notation "I" => Case F P.b d

theorem path_factor : Short (fun i : I => 2 ^ ((i.T.scheme.d + 1) * i.n)) := by
  have h : Short (fun i : I => 2 ^ i.n) := tiles.rate.short
  refine (h.pow (d + 1)).mono fun i => ?_
  rw [← pow_mul, mul_comm i.n]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.succ_le_succ i.h.degree))

theorem tableWidth_bound : Short (fun i : I => i.T.tableWidth) := by
  have he : Short (fun i : I => 2 ^ i.T.scheme.e) := spans.short
  have hd : Short (fun i : I => i.T.scheme.d) := Case.slots.rate.short.of_exp
  refine (Case.bits.add (he.mul ((short_const 1).add (hd.add he.of_exp)))).mono fun i => ?_
  simp only [Template.tableWidth, Window.Outgoing, Format.width_vec, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

theorem patch_bound : Short (fun i : I => (Group.Patch ((i.T.scheme.d + 1) * i.n) i.n i.T.count).width) := by
  have hp := path_factor P d
  refine ((short_const 1).add (hp.mul ((hp.mul (short_const 2)).add
    (tiles.rate.short.mul counters)))).mono fun i => ?_
  rw [Group.width_patch]

theorem groupLabels_bound : Short (fun i : I => (Group.Labels i.n).width) := by
  refine (tiles.rate.short.mul (child_factor P d).of_exp).mono fun i => ?_
  rw [Group.Labels, Format.width_vec, Format.width_addr]

theorem groupArity_bound : Short (fun i : I => Group.arity ((i.T.scheme.d + 1) * i.n) i.n i.T.count) := by
  have ht : Short (fun i : I => 2 ^ i.n) := tiles.rate.short
  have hw := (child_factor P d).of_exp
  have hs : Short (fun i : I => (Group.Summary i.n).width) :=
    (ht.mul (ht.of_exp.add (ht.mul hw))).mono fun i => by rw [Group.width_summary]
  exact (((patch_bound P d).add hs).add ht.of_exp).add (groupLabels_bound P d)

theorem colors_bound : Short (fun i : I => (i.T.Colors i.a).width) := by
  refine tiles.rate.short.mono fun i => ?_
  rw [Template.Colors, Format.width_vec, Format.width_bit, mul_one]

theorem vote_bound : Short (fun i : I => (i.T.Vote i.a).width) := by
  refine ((child_factor P d).mul ((seat_factor P d).of_exp.add (short_const 1))).mono fun i => ?_
  rw [Template.Vote, Format.width_vec, Format.width_addr]

theorem prepareWidth_bound : Short (fun i : I => i.T.arity i.a (b P)) :=
  (((tableWidth_bound P d).add (groupArity_bound P d)).add
    ((child_factor P d).of_exp.add (colors_bound P d))).add ((pollRow_bound P d).add (vote_bound P d))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Common graph widths and charge per occupied block -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Assembly History Packing Phase Phase.Case Coloring Window

variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

theorem size_bound : Long (fun i : I => i.T.size i.a) :=
  hosts.add (child_factor P d).long.of_exp

theorem expanded {f : I → ℕ} (h : Case.Row f) : Cost (fun i : I => 2 ^ (i.T.size i.a) * f i) :=
  h.expand (child_factor P d)

theorem format_bound : Cost (fun i : I => i.T.format.width) := Case.Child.parent.format

theorem next_bound : Cost (fun i : I => (next P i.S i.T i.v i.h.vpos Δ i.R i.a).format.width) :=
  (child_bound P Δ d).format

theorem grouped {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Fmt.groups i.m i.T.scheme.d i.a (A i)).width) := by
  have hc : Long (fun i : I => 2 ^ i.T.scheme.d * i.m) := Case.slots.rate.short.long.mul hosts
  refine (Row.hosts (hc.row.add h.groups)).mono fun i => ?_
  exact le_of_eq (Fmt.width_rows _ _ _ _)

theorem counted_bound : Cost (fun i : I => (i.T.Counted i.a (b P)).width) :=
  grouped P d (count_bound P d)

theorem poll_bound : Cost (fun i : I => (i.T.Poll i.a (b P)).width) := by
  refine ((format_bound P d).add (grouped P d (source_bound P d))).mono fun i => ?_
  rw [Template.Poll, Format.width_pair]

theorem seats_bound : Cost (fun i : I => Fintype.card (i.T.Slots i.a)) := by
  refine (seat_factor P d).groups.hosts.mono fun i => ?_
  rw [Fintype.card_congr (i.T.seatIndex i.a).symm, Fintype.card_fin, pow_add, pow_add, mul_assoc]

theorem candidate_bound : Cost (fun i : I => (i.T.Candidate i.a (b P)).width) := by
  refine ((seats_bound P d).mul (short_const (b P))).mono fun i => ?_
  simp only [Template.Candidate, Branches.format, Fmt.width_pi, Format.width_addr, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  rfl

theorem status_bound : Cost (fun i : I => (i.T.Status i.a).width) := by
  refine (expanded P d (long_const 1).row).mono fun i => ?_
  rw [Template.Status, Format.width_vec, Format.width_bit]

theorem graph_bound : Cost (fun i : I => (i.T.Graph i.a Δ (degreeBound i.S i.T Δ)).width) := by
  have h := (child_slots P Δ d).rate.short.long.mul (size_bound P d)
  refine (expanded P d (Long.row h)).mono fun i => ?_
  rw [Template.Graph, Neighborhood.Rows, Format.width_vec, Format.width_vec, Format.width_addr]

theorem header_bound : Cost (fun i : I => (i.T.ChildHeader i.a Δ (degreeBound i.S i.T Δ)).width) := by
  have h := (long_const 2).add ((child_slots P Δ d).rate.short.long.mul (long_const 2))
  refine (expanded P d (Long.row h)).mono fun i => ?_
  simp only [Template.ChildHeader, Group.Flags, Format.width_vec, Format.width_pair]
  rw [Format.width_bit]

theorem raw_bound : Cost (fun i : I => (i.T.Raw i.a (b P) Δ (degreeBound i.S i.T Δ)).width) := by
  have hb : Cost (fun _ : I => Format.bit.width) := (long_const _).row.cost
  refine ((status_bound P d).add (hb.add ((graph_bound P Δ d).add (counted_bound P d)))).mono fun i => ?_
  rw [Template.Raw, Tile.raw, Format.width_pair, Format.width_pair, Format.width_pair]

theorem headed_bound : Cost (fun i : I => (i.T.Headed i.a (b P) Δ (degreeBound i.S i.T Δ)).width) := by
  refine ((raw_bound P Δ d).add (header_bound P Δ d)).mono fun i => ?_
  rw [Template.Headed, Format.width_pair]

theorem output_bound {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Tile.output i.m i.a i.n (A i)).width) := by
  refine (expanded P d h.groups).mono fun i => ?_
  rw [Tile.output, Format.width_vec, Format.width_vec]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Cost of simultaneous history updates with long host addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Assembly Packing Phase Phase.Case Coloring Window

variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

private abbrev slot (i : I) := i.T.degree i.a Δ (degreeBound i.S i.T Δ)
private abbrev label (i : I) := i.T.Label i.a Δ (degreeBound i.S i.T Δ)
  (book P i.S i.T i.v i.h.vpos) (e Δ i.R) (cap P i.S i.T i.v i.h.vpos Δ i.R)
  (meter i.S Δ i.R) (i.T.Pointers (e Δ i.R))

theorem pair_cost {A B : I → Format} (h : Cost (fun i => (A i).width)) (k : Cost (fun i => (B i).width)) :
    Cost (fun i => ((A i).pair (B i)).width) :=
  (h.add k).mono fun _ => (Format.width_pair ..).le

private theorem walk_bound : Short (fun i : I => (Walks 8 i.T.scheme.d (i.T.WithCount i.a (b P))).width) := by
  refine ((radius_factor P d).mul (count_bound P d)).mono fun i => ?_
  rw [Walks, Format.width_vec]

private theorem incoming_bound : Cost (fun i : I =>
    (Tile.incoming i.m i.T.scheme.d i.a i.n (slot P Δ d i) (i.T.WithCount i.a (b P))).width) := by
  have masks : Cost (fun i : I => (Format.vec i.m (Tile.mask i.T.scheme.d i.n (slot P Δ d i))).width) := by
    refine (mask_bound P Δ d).long.row.hosts.mono fun i => ?_
    rw [Format.width_vec]
  have h := pair_cost P d masks (grouped P d (walk_bound P d))
  have hb : Cost (fun _ : I => Format.bit.width) := (long_const _).row.cost
  exact pair_cost P d (status_bound P d) (pair_cost P d hb h)

private theorem tile_bound : Cost (fun i : I =>
    Tile.cost i.m i.T.scheme.d i.a i.n (slot P Δ d i) (i.T.WithCount i.a (b P)) (label P Δ d i)) := by
  have h := ((short_const 1).add ((short_const 137).mul (word_bound P Δ d))).add (label_bound P Δ d)
  refine (((incoming_bound P Δ d).scale 4).add (expanded P d (Short.groups h))).mono fun i => ?_
  rw [Tile.cost, mul_assoc]

private theorem bank_bound : Cost (fun i : I => Tile.bankCost i.m i.T.scheme.d i.a i.n (slot P Δ d i)
    (i.T.WithCount i.a (b P)) (walk P i.T i.r) (accessCost (i.m + i.T.scheme.d) (walk P i.T i.r))
    (precision i.S i.T Δ i.r)) := by
  have hp : Long (fun i : I => precision i.S i.T Δ i.r) :=
    ((size_bound P d).add (mask_factor P d).long).add (child_slots P Δ d).rate.short.long
  have hv : Case.Row (fun i : I => walk P i.T i.r) := (walk_bound P d).groups
  have h := Mixed.long Case.m (((long_const 100).add (hosts.add (radius_factor P d).long)).pow 20)
  have k := expanded P d (Long.row (((long_const 100).add hp).pow 40))
  exact (((raw_bound P Δ d).scale 24).add ((h.add k).scale 4)).add
    ((read_bound P.b d Case.slots.rate.short hv).scale 9)

theorem issueCost_bound : Cost (fun i : I => issueCost P i.S i.T i.v i.h.vpos Δ i.R i.r) := by
  have h₀ := headed_bound P Δ d
  have h₁ := pair_cost P d (graph_bound P Δ d) (header_bound P Δ d)
  have h₂ := raw_bound P Δ d
  have h₃ := output_bound P d (label_bound P Δ d)
  have h₄ := pair_cost P d (next_bound P Δ d) (output_bound P d (pointers_bound P Δ d))
  have N := (bank_bound P Δ d).add (tile_bound P Δ d)
  have keep := (h₀.add (h₁.scale 2)).scale 4
  have run := ((h₀.add (h₂.scale 2)).scale 4).add N
  exact ((h₀.scale 20).add (keep.add run)).add (((pair_cost P d h₁ h₃).add (h₄.scale 2)).scale 4)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Cost of choosing a layout and constructing the common graph masks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Assembly Packing Phase Phase.Case Coloring

variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

theorem groupInput_bound : Cost (fun i : I => (i.T.groupInput i.a).width) := by
  have hd : Long (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.rate.short.long
  have hn := Long.row (hd.mul hosts)
  have hf := Long.row (hd.mul (long_const 2))
  have hv : Case.Row (fun i : I => 2 ^ i.a * (2 ^ i.n * i.T.count)) :=
    Short.groups (tiles.rate.short.mul counters)
  refine (Row.hosts (hn.add ((long_const 1).row.add (hf.add hv)))).mono fun i => ?_
  simp only [Template.groupInput, Group.Input, Fmt.bank, Group.Parcel, Group.Flags, Format.width_vec,
    Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

private theorem childInput_bound : Cost (fun i : I => (Child.Input i.m i.T.scheme.d).width) := by
  have hd : Long (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.rate.short.long
  refine (Mixed.long Case.m (hd.mul ((long_const 1).add hosts))).mono fun i => ?_
  simp only [Child.Input, Format.width_vec, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

private theorem nav_bound {q : I → ℕ} (h : Short (fun i => 2 ^ (q i))) :
    Cost (fun i : I => i.T.navCost i.a (q i)) := by
  have bits := ((long_const 100).add ((size_bound P d).add h.long)).pow 201
  exact (((format_bound P d).add ((groupInput_bound P d).scale 3)).add
    ((childInput_bound P d).scale 68)).add (expanded P d (Long.row bits))

private theorem childCost_bound : Cost (fun i : I => i.T.childCost i.a Δ (degreeBound i.S i.T Δ)) := by
  have h := format_bound P d
  have s := h.add ((status_bound P d).scale 34)
  exact (((h.scale 5).add s).add (nav_bound P d (child_slots P Δ d).rate.short)).scale 4

private theorem headerCost_bound : Cost (fun i : I => i.T.headerCost i.a Δ (degreeBound i.S i.T Δ)) := by
  have h := format_bound P d
  have s := status_bound P d
  have p := (child_slots P Δ d).rate.short
  have q : Short (fun i : I => 2 ^ (Child.nextWidth i.n Δ i.T.scheme.d)) := by
    refine p.mono fun i => ?_
    simp only [Template.degree, Template.bound, i.h.core, Bool.false_eq_true, ↓reduceIte]
    rfl
  have bits := ((long_const 100).add (((size_bound P d).add p.long).add q.long)).pow 16
  have flags : Cost (fun i : I => (Format.vec (i.T.size i.a)
      (.vec (i.T.degree i.a Δ (degreeBound i.S i.T Δ)) .bit)).width) := by
    refine (expanded P d p.long.row).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_bit, mul_one]
  have h₁ := ((h.scale 5).add (h.add (s.scale 34))).add (h.add (s.scale 2))
  have h₂ := (((h.scale 5).add (nav_bound P d p)).add (nav_bound P d q)).add (expanded P d (Long.row bits))
  have h₃ := (pair_cost P d (pair_cost P d s s) flags).add ((header_bound P Δ d).scale 34)
  exact (((h.scale 5).add h₁).add h₂).add h₃

theorem groups_cost {f : I → ℕ} (hf : Short f) : Cost (fun i : I => 2 ^ (i.m + i.a) * f i) := by
  simpa only [pow_add, mul_assoc] using hf.groups.hosts

private theorem groups_width {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Format.vec (i.m + i.a) (A i)).width) :=
  (groups_cost P d h).mono fun _ => (Format.width_vec ..).le

private theorem entries_bound : Cost (fun i : I => (i.T.Entries i.a (b P)).width) := by
  refine ((seats_bound P d).mul (short_const (Side.Entry (b P)).width)).mono fun i => ?_
  simp only [Template.Entries, Branches.Marked, Fmt.width_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

private theorem markCost_bound : Cost (fun i : I => i.T.markCost i.a (b P)) := by
  have p := pollRow_bound P d
  have s := side_bound P d
  have x := ((poll_bound P d).add ((groups_width P d p).scale 2)).scale 4
  have y := groups_cost P d (((short_const 1).add p).add s)
  have z := ((groups_width P d s).add ((entries_bound P d).scale 2)).scale 4
  exact (x.add y).add z

private theorem layoutCost_bound : Cost (fun i : I => i.T.layoutCost i.a (b P) (profile P)) := by
  have hc := seats_bound P d
  have h : Cost (fun i : I => 2 ^ (i.m + i.a + (i.n + i.T.scheme.e))) := by
    refine hc.mono fun i => ?_
    rw [Fintype.card_congr (i.T.seatIndex i.a).symm, Fintype.card_fin]
  have g : Cost (fun i : I => (Side.Input (i.m + i.a + (i.n + i.T.scheme.e)) (b P)).width) :=
    (h.mul (short_const (Side.Entry (b P)).width)).mono fun _ => (Format.width_vec ..).le
  have mark := (markCost_bound P d).add (hc.mul (short_const (Branches.charge (b P))))
  exact (mark.add (((entries_bound P d).add (g.scale 2)).scale 4)).add
    ((h.mul (short_const ((100 + profile P) ^ 8))).scale 4)

private theorem rawCost_bound : Cost (fun i : I =>
    i.T.rawCost i.a (b P) Δ (degreeBound i.S i.T Δ) (profile P)) := by
  have p := poll_bound P d
  have c := counted_bound P d
  have hb : Cost (fun _ : I => Format.bit.width) := (long_const _).row.cost
  have copies := pair_cost P d (format_bound P d) (pair_cost P d p p)
  have fields := pair_cost P d (pair_cost P d (status_bound P d) (graph_bound P Δ d)) (pair_cost P d hb c)
  have x := (p.add (copies.scale 2)).scale 4
  have y := (childCost_bound P Δ d).add ((layoutCost_bound P d).add ((p.add (c.scale 2)).scale 4))
  exact (x.add y).add ((fields.add ((raw_bound P Δ d).scale 2)).scale 4)

theorem headedCost_bound : Cost (fun i : I => headedCost P i.S i.T Δ i.r) := by
  have p := poll_bound P d
  have x := (p.add ((pair_cost P d p (format_bound P d)).scale 2)).scale 4
  exact x.add ((rawCost_bound P Δ d).add ((headerCost_bound P Δ d).scale 4))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Costs of the input, exterior history and scalar sweep of a contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Phase Phase.Case
variable {F : Type} [Field F] (P : Gadget F) (Δ d : ℕ)
local notation "I" => Case F P.b d

theorem input_bound : Cost (fun i : I => (In P i.S i.T i.r).width) :=
  pair_cost P d Child.parent.full (candidate_bound P d)

theorem sweepCost_bound :
    Cost (fun i : I => Snapshot.sweepCost i.S (next P i.S i.T i.v i.h.vpos Δ i.R i.a)) :=
  (child_bound P Δ d).sweep

theorem secondCost_bound : Cost (fun i : I => secondCost P i.S i.T i.v i.h.vpos Δ i.R i.r) := by
  have hm : Cost (fun i : I => (Mid P i.S i.T Δ i.r).width) :=
    pair_cost P d (headed_bound P Δ d) Child.current
  have hg := gather_bound (F := F) P.b d Child.parent.neighbors Child.parent.row
  have H := child_bound P Δ d
  have hs := H.gather (c := fun i => accessCost (i.m + i.T.scheme.d) (origin i.S i.T)) hg
  have hk := H.carry (k := fun i => i.T.scheme.d + 1) (A := fun i => Mid P i.S i.T Δ i.r) Child.fan hm
  refine ((((hm.scale 100).add (issueCost_bound P Δ d)).add hs).add hk).mono fun i => ?_
  simp only [secondCost, origin, Case.a, Case.m, Case.height, le_refl]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end
