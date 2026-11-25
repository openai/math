import OAI.LinearAlgebra.MatrixExponent.Assembly.FreezeInput.Cost
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Pass
import OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery.Run

/-! # Admission fits the three boundary budgets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly

theorem admission (d : ℕ) : ∃ j, ∀ {F : Type} [Field F] (D : Template F) (s : Plan)
    (z payload : ℕ) (x y : Wire) (p : Prices F) (r : ℕ), D.scheme.d ≤ d → D.scheme.m ≤ p.w →
    3 + 2 * D.scheme.ℓ ≤ (BoundaryScale.short D z payload r p) ^ j ∧
    admitCost D s z payload x y ≤ BoundaryScale.cost (x := x) (y := y) D z payload r p j := by
  let b := 10000 + 2 ^ d
  let k := 2 + b + 1
  refine ⟨k * 14, ?_⟩
  intro F _ D s z payload x y p r hd hm
  let A := BoundaryScale.short D z payload r p
  let B := BoundaryScale.long D z payload r p
  let C := BoundaryScale.outer D z payload p
  let u := 10000 + 2 ^ D.scheme.d + D.scheme.ℓ + D.count + payload
  have hb : 3 ≤ b := by unfold b; generalize 2 ^ d = n; omega
  have ha : 100 + D.scheme.ℓ + D.count + payload ≤ A := by
    unfold A BoundaryScale.short BoundaryScale.metadata BoundaryScale.base
    generalize 2 ^ D.scheme.e = i, 2 ^ r = j
    omega
  have hB : A + D.scheme.m ≤ B := by unfold B BoundaryScale.long; change _ ≤ 100 + p.w + _ + A; omega
  have hC : 100 + payload ≤ C := by unfold C BoundaryScale.outer; omega
  have hu : u ≤ A + b := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    unfold u b
    omega
  have powbound (N t : ℕ) (hN : 2 ≤ N) (ht : t ≤ 2 * N + b) : t ^ 14 ≤ N ^ (k * 14) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (ht.trans (BoundaryScale.linear hN 2 b)) 14
  refine ⟨?_, (admit_cost D s z payload x y).trans ?_⟩
  · exact (Nat.le_self_pow (by decide : 14 ≠ 0) _).trans (powbound A _ (by omega) (by omega))
  · exact Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left _ (powbound B (u + D.scheme.m) (by omega) (by omega)))
      (Nat.mul_le_mul_left _ (powbound A u (by omega) (by omega))))
      (Nat.mul_le_mul_left _ (powbound C (100 + payload) (by omega) (by omega)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Room for the final recovery addresses after a fixed sequence of reductions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly

private theorem power_room {M K : ℕ} (hm : 2 ≤ M) (hk : 2 ≤ K) : M + K ≤ M ^ K := by
  have hp : 0 < M := by omega
  have ha : M ≤ M ^ (K - 1) := Nat.le_pow (by omega)
  have hb : K ≤ M ^ (K - 1) := by
    have := (Nat.lt_two_pow_self (n := K - 1)).trans_le (Nat.pow_le_pow_left hm _)
    omega
  calc
    _ ≤ M ^ (K - 1) * 2 := by omega
    _ ≤ M ^ (K - 1) * M := Nat.mul_le_mul_left _ hm
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]

private theorem capacity (l n m w : ℕ) (h : n + m + 2 * l + 1 ≤ w) :
    2 ^ l * (n * (2 ^ m + 2 ^ (m + l))) < 2 ^ w := by
  have hm : 2 ^ m ≤ 2 ^ (m + l) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ ≤ 2 ^ l * (n * (2 ^ (m + l) + 2 ^ (m + l))) := by gcongr
    _ = n * 2 ^ (l + (m + l) + 1) := by rw [pow_succ, pow_add 2 l]; ring
    _ < 2 ^ n * 2 ^ (l + (m + l) + 1) := Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
    _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)

variable {F : Type} [Field F] {x y : Wire} {D : Template F} {s : Plan} {T z payload r H d K l : ℕ}
  {p : Prices F} {L : ℝ}

theorem Result.address (q : Result (x := x) (y := y) (border D s z) s T L z payload p r H)
    (h : Requirements D s T L z payload p r d K) (hk : H + s.K + s.M + s.d + s.p + 2 * l + 10 ≤ K) :
    1 ≤ q.next.scheme.m ∧ q.next.scheme.m + q.next.scheme.d ≤ p.w ∧
    2 ^ l * ((max payload (q.next.scheme.h + Recovery.height s T) + 1)*
      (2 ^ q.next.scheme.m + 2 ^ (q.next.scheme.m + l))) < 2 ^ p.w := by
  have hv := (BoundaryScale.base_lower D z payload r).trans (BoundaryScale.lower D z payload r)
  have ht := (BoundaryScale.two D z payload r).trans (BoundaryScale.lower D z payload r)
  have hb := (power_room ht (show 2 ≤ K by omega)).trans h.small
  have hu := width_bits h.upper
  have hm : D.scheme.m ≤ q.next.scheme.m := q.growth.lower
  have hn : q.next.scheme.m ≤ D.scheme.m + s.n * r + s.K := q.growth.upper
  have hg : q.next.scheme.h + s.n * r = D.scheme.h := q.growth.height
  have hd := q.growth.degree
  have hw := h.address
  have := Nat.zero_le (2 ^ r)
  have := Nat.zero_le (2 ^ D.scheme.e)
  refine ⟨by omega, by omega, capacity _ _ _ _ ?_⟩
  unfold Recovery.height
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-!
# Label sizes after recovery

Each restored station references one attachment label. All further
metadata is polynomially bounded in the initial short dimensions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly
variable {F : Type} [Field F] {x y : Wire} {D : Template F} {s : Plan}
  {T z payload r H : ℕ} {L : ℝ} {p : Prices F}

private theorem restored_size (q : Result (x:=x) (y:=y) (border D s z) s T L z payload p r H)
    (hs : s.Fits) (hz : 0 < z) (ht : T ≤ z * s.M) (hl : 0 ≤ L) :
    let X := Recovery.restored x y q.pack payload hs hz ht hl
    X.template.scheme.ℓ + X.template.count =
      2 * q.pack.ℓ + 2 * q.pack.k + 4 * 2 ^ q.pack.e * (6 + q.pack.e) + 26 := by
  let E := (Recovery.layer x y q.pack payload hs hz ht hl).template
  change (Merge.scheme E.scheme).ℓ + E.count = _
  rw [Merge.label_width]
  change (Restore.script q.pack.scheme).width + 2 ^ 3 * 3 + (Restore.script q.pack.scheme).width = _
  rw [Restore.script_width]
  simp only [pow_add, pow_one]
  ring

theorem restored_labels (s : Plan) (hs : s.Fits) (d H : ℕ) :
    ∃ j : ℕ, ∀ {F : Type} [Field F] {x y : Wire} {D : Template F} {T z payload r K : ℕ}
      {L : ℝ} {p : Prices F} (q : Result (x:=x) (y:=y) (border D s z) s T L z payload p r H)
      (h : Requirements D s T L z payload p r d K),
      let X := Recovery.restored x y q.pack payload hs h.unit h.upper (zero_le_one.trans h.positive)
      X.template.scheme.ℓ + X.template.count ≤
        j * (D.scheme.ℓ + D.count) + (BoundaryScale.base D z payload r) ^ j := by
  let C := 4 * H * (1 + 2 ^ d) + 2 + 2 * (2 + s.K) + 4 * (1 + H) * (7 + H) + 26
  let k := (3 + d + 1) * H + 2
  let j := 4 * H + k + C
  refine ⟨j, ?_⟩
  intro F _ x y D T z payload r K L p q h
  let X := BoundaryScale.base D z payload r
  let Y := D.scheme.ℓ + D.count
  have h2 : 2 ≤ X := BoundaryScale.two ..
  have hp : 0 < X := by omega
  have hK : 2 ≤ k := Nat.le_add_left ..
  have hx : 1 ≤ X ^ k := Nat.one_le_pow _ _ hp
  have hh := BoundaryScale.base_lower D z payload r
  have he := Nat.zero_le (2 ^ D.scheme.e)
  have hr := Nat.zero_le (2 ^ r)
  have hscale : ∀ c : ℕ, c ≤ c * X := fun c => Nat.le_mul_of_pos_right _ hp
  have hslots : q.pack.k ≤ (2 + s.K) * X := calc
    _ ≤ 1 + s.n * r + s.K := q.growth.stations
    _ ≤ 1 + X + s.K := by have := h.height; omega
    _ ≤ _ := by rw [add_mul]; have := hscale s.K; omega
  have hext : 2 ^ q.pack.e ≤ (1 + H) * X := calc
    _ ≤ 2 ^ D.scheme.e + H := q.growth.outer
    _ ≤ _ := by rw [add_mul]; have := hscale H; omega
  have hband : 6 + q.pack.e ≤ (7 + H) * X := by
    have := Nat.lt_two_pow_self (n:=q.pack.e)
    rw [add_mul] at hext ⊢
    omega
  have hprev : q.pack.ℓ ≤ H * (2 * Y + 2 * (1 + 2 ^ d)) + X ^ k := by
    have hl := (Nat.le_add_left q.pack.ℓ q.next.scheme.ℓ).trans q.growth.labels
    have hc := cut_length D s z
    change q.pack.ℓ ≤ H * ((inside D s z).scheme.ℓ + (border D s z).ℓ) + _ at hl
    rw [hc.1, hc.2.1] at hl
    refine hl.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ?_) ?_)
    · have := Nat.pow_le_pow_right (by decide : 0 < 2) h.degree
      omega
    · have := Nat.pow_le_pow_left (BoundaryScale.origin (r:=r) (z:=z) (payload:=payload) (s:=s) h.degree) H
      rw [← pow_mul] at this
      exact this.trans (Nat.pow_le_pow_right hp (by omega))
  have hcost : C * X ^ k ≤ X ^ j := calc
    _ ≤ X ^ C * X ^ k := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left h2 _))
    _ = X ^ (C + k) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right hp (by omega)
  have hl : X ≤ X ^ k := Nat.le_pow (by omega)
  have hh' : X ^ 2 ≤ X ^ k := Nat.pow_le_pow_right hp hK
  dsimp only
  rw [restored_size q hs h.unit h.upper (zero_le_one.trans h.positive)]
  calc
    _ ≤ 2 * (H * (2 * Y + 2 * (1 + 2 ^ d)) + X ^ k) + 2 * ((2 + s.K) * X) + 4 * ((1 + H) * X) * ((7 + H) * X) + 26 := by gcongr
    _ = 4 * H * Y + (4 * H * (1 + 2 ^ d) * 1 + 2 * X ^ k + 2 * (2 + s.K) * X + 4 * (1 + H) * (7 + H) * X ^ 2 + 26 * 1) := by ring
    _ ≤ 4 * H * Y + (4 * H * (1 + 2 ^ d) * X ^ k + 2 * X ^ k + 2 * (2 + s.K) * X ^ k + 4 * (1 + H) * (7 + H) * X ^ k + 26 * X ^ k) := by gcongr
    _ = 4 * H * Y + C * X ^ k := by unfold C; ring
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) hcost

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-!
# Bounds on the three resources used by restoration

Span counts enter the cost per occurrence. Only their logarithms
enter the factor multiplying the number of exterior ports.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly BatchDescent.Phase

abbrev extra (s : Plan) := Restore.bits s.slots s.slots s.w

structure Sample (s : Plan) (d H : ℕ) where
  F : Type
  [field : Field F]
  x : Wire
  y : Wire
  D : Template F
  T : ℕ
  L : ℝ
  z : ℕ
  payload : ℕ
  p : Prices F
  r : ℕ
  K : ℕ
  h : Requirements D s T L z payload p r d K
  q : Result (x := x) (y := y) (border D s z) s T L z payload p r H

attribute [instance] Sample.field

namespace Sample
variable {s : Plan} {d H : ℕ}
local notation "I" => Sample s d H
variable (i : Sample s d H)

abbrev data := BoundaryScale.metadata i.D i.z i.payload i.r
abbrev fast := BoundaryScale.short i.D i.z i.payload i.r i.p
abbrev slow := BoundaryScale.long i.D i.z i.payload i.r i.p
abbrev outer := BoundaryScale.outer i.D i.z i.payload i.p
abbrev measure := Recovery.measure i.q.pack s i.T i.payload i.p
abbrev core := border i.D s i.z

theorem two : 2 ≤ i.outer := by unfold outer BoundaryScale.outer; omega
theorem small : i.outer ≤ i.fast := by
  have h := Nat.lt_two_pow_self (n := i.D.scheme.e)
  have := Nat.zero_le (2 ^ i.r)
  unfold outer BoundaryScale.outer fast BoundaryScale.short BoundaryScale.metadata BoundaryScale.base
  omega
theorem large : i.fast ≤ i.slow := Nat.le_add_left ..
theorem two_fast : 2 ≤ i.fast := i.two.trans i.small
theorem two_slow : 2 ≤ i.slow := i.two_fast.trans i.large

abbrev Fast (f : I → ℕ) := Poly fast f
abbrev Slow (f : I → ℕ) := Poly slow f
abbrev Outer (f : I → ℕ) := Poly outer f
variable {f : Sample s d H → ℕ}

theorem Fast.slow (h : Fast f) : Slow f := h.grow large
theorem Outer.fast (h : Outer f) : Fast f := h.grow small
theorem constant (j : ℕ) : Fast (fun _ : I => j) := Poly.const two_fast j
theorem body : Fast (fun i : I => i.fast) := Poly.of_le two_fast fun _ => le_rfl
theorem high : Slow (fun i : I => i.slow) := Poly.of_le two_slow fun _ => le_rfl
theorem fields : Fast (fun i : I => i.data) := body.mono fun _ => Nat.le_add_right ..

theorem old : Fast (fun i : I => short i.core i.r i.z i.payload) :=
  (fields.pow (BoundaryScale.charge d)).mono fun i => BoundaryScale.coded i.h.degree

private theorem oldBase : Fast (fun i : I => base i.core i.r i.z i.payload) :=
  old.mono fun i => by unfold short; omega

private theorem log_bound {a b c : ℕ} (h : 2 ^ a ≤ 2 ^ b + c) : a ≤ b + c := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [pow_add]
  refine h.trans ((Nat.add_le_add_left (Nat.le_mul_of_pos_left c (Nat.two_pow_pos b)) _).trans ?_)
  simpa only [mul_add, mul_one] using Nat.mul_le_mul_left (2 ^ b) (show 1 + c ≤ 2 ^ c by
    have := Nat.lt_two_pow_self (n := c)
    omega)

theorem exterior : Outer (fun i : I => i.measure.outer) := by
  let j := 1010 + 2 * s.d + 2 * s.p + 2 * s.M + extra s + s.K + H
  refine ⟨two, ⟨10 + j + 1, fun i => le_trans ?_ (BoundaryScale.linear i.two 10 j)⟩⟩
  have hh := i.q.growth.height
  have hw := width_bits i.h.upper
  have hk := i.q.growth.stations
  have he := log_bound i.q.growth.outer
  change i.q.next.scheme.h + s.n * i.r = i.D.scheme.h at hh
  change i.q.pack.k ≤ 1 + s.n * i.r + s.K at hk
  change i.q.pack.e ≤ i.D.scheme.e + H at he
  change 1000 + i.p.W + i.payload + (i.q.next.scheme.h + (s.d + s.p + Nat.clog 2 i.T)) + extra s +
    (max i.payload (i.q.next.scheme.h + (s.d + s.p + Nat.clog 2 i.T)) + 1) +
    (i.q.next.scheme.h + (i.q.pack.k + (1 + i.q.pack.e))) ≤ _
  unfold outer BoundaryScale.outer j
  omega

private theorem groups : Fast (fun i : I => 2 ^ i.r) := by
  refine fields.mono fun i => ?_
  have h := (BoundaryScale.base_lower i.D i.z i.payload i.r).trans (BoundaryScale.lower ..)
  have := Nat.zero_le (2 ^ i.D.scheme.e)
  unfold data
  omega

theorem copies : Fast (fun i : I => 2 ^ (s.n * i.r + s.K)) := by
  simpa only [pow_add, pow_mul'] using (groups.pow s.n).mul (constant (2 ^ s.K))

private theorem spans : Fast (fun i : I => 2 ^ i.q.pack.e) := by
  have h : Fast (fun i : I => 2 ^ i.D.scheme.e) := by
    refine fields.mono fun i => ?_
    have h := (BoundaryScale.base_lower i.D i.z i.payload i.r).trans (BoundaryScale.lower ..)
    have := Nat.zero_le (2 ^ i.r)
    unfold data
    omega
  exact (h.add (constant H)).mono (fun i => i.q.growth.outer)

private theorem stations : Fast (fun i : I => 2 ^ i.q.pack.k) := by
  refine ((constant (2 ^ 1)).exp_add copies).mono fun i => ?_
  rw [← add_assoc]
  exact Nat.pow_le_pow_right (by decide) i.q.growth.stations

private theorem labels : Fast (fun i : I => i.q.pack.ℓ + i.q.next.scheme.ℓ + i.q.next.count) := by
  have a : Fast (fun i : I => (inside i.D s i.z).scheme.ℓ + i.core.ℓ) := by
    refine old.mono fun i => ?_
    change _ ≤ base i.core i.r i.z i.payload + (inside i.D s i.z).scheme.ℓ + i.core.ℓ + _
    omega
  have b := (oldBase (s := s) (d := d) (H := H)).pow H
  refine ((((constant H).mul a).add b).add b).mono fun i => ?_
  rw [add_comm i.q.pack.ℓ]
  exact Nat.add_le_add i.q.growth.labels i.q.growth.counters

theorem controls : Fast (fun i : I => i.measure.short) := by
  have h : Fast (fun i : I => 2 ^ i.q.next.scheme.d) :=
    (constant (2 ^ H)).mono fun i => Nat.pow_le_pow_right (by decide) i.q.growth.degree
  have n : Fast (fun i : I => 2 ^ i.measure.n) := stations.exp_add ((constant (2 ^ 1)).exp_add spans)
  have c : Fast (fun i : I => Install.localCost (2 ^ i.measure.d + (2 + i.measure.d + i.measure.l))) := by
    refine (constant (Install.localCost (2 ^ H + (2 + H + extra s)))).mono fun i => ?_
    have e := i.q.growth.degree
    change Install.localCost (2 ^ i.q.next.scheme.d + (2 + i.q.next.scheme.d + extra s)) ≤ _
    unfold Install.localCost
    gcongr
  exact (((((exterior.fast.add labels).add h).add n).add (constant (2 ^ extra s))).add c)

theorem addresses : Slow (fun i : I => i.measure.long) := by
  have a : Slow (fun i : I => i.p.w + i.p.w ^ i.p.power) :=
    high.mono fun i => by unfold slow BoundaryScale.long; omega
  have b : Slow (fun i : I => i.measure.m) := by
    refine high.mono fun i => ?_
    have h := i.q.growth.upper
    change i.q.next.scheme.m ≤ i.D.scheme.m + s.n * i.r + s.K at h
    change i.q.next.scheme.m ≤ _
    have h₁ := i.h.address
    have h₂ := i.h.height
    have h₃ := i.h.room
    have h₄ := Nat.zero_le (i.p.w ^ i.p.power)
    unfold slow BoundaryScale.long BoundaryScale.short BoundaryScale.metadata BoundaryScale.base
    have h₅ := Nat.zero_le (2 ^ i.D.scheme.e)
    omega
  refine (((controls.slow.add b).add (b.add (constant (extra s)).slow)).add a).mono fun i => ?_
  unfold Restore.Measure.long
  rw [add_assoc _ i.measure.c.w]
  exact le_rfl

end Sample
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # One cost allowance for both the contractions and restoration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Sample
open Assembly BatchDescent.Phase
variable {s : Plan} {d H : ℕ}
local notation "I" => Sample s d H

private theorem addr : Slow (fun i : I => 100 + i.p.w + i.p.w ^ i.p.power + i.p.W + short i.core i.r i.z i.payload) := by
  refine (high.add old.slow).mono fun i => ?_
  unfold slow BoundaryScale.long BoundaryScale.short
  omega

private theorem volume : Fast (fun i : I => short i.core i.r i.z i.payload + i.p.W) := by
  refine (old.add body).mono fun i => ?_
  unfold fast BoundaryScale.short
  omega

private theorem ports : Outer (fun i : I => 100 + i.payload + i.p.W) :=
  Poly.of_le two fun i => by unfold outer BoundaryScale.outer; omega

/-- The growth of the host count can be paid from the grouping size. -/
private theorem hosts (i : I) :
    2 ^ i.measure.m ≤ 2 ^ i.D.scheme.m * 2 ^ (s.n * i.r + s.K) ∧
      2 ^ (i.measure.m + i.measure.h) ≤ 2 ^ (i.D.scheme.m + i.D.scheme.h) * 2 ^ (s.n * i.r + s.K) := by
  have ha := i.q.growth.upper
  have hb := i.q.growth.height
  change i.measure.m ≤ i.D.scheme.m + s.n * i.r + s.K at ha
  change i.measure.h + s.n * i.r = i.D.scheme.h at hb
  constructor <;> rw [← pow_add] <;> exact Nat.pow_le_pow_right (by decide) (by omega)

theorem bounds (s : Plan) (d H J : ℕ) :
    ∃ j, ∀ i : Sample s d H,
      5 + (short i.core i.r i.z i.payload) ^ H + i.measure.short ^ J ≤ i.fast ^ j ∧
      size (x := i.x) (y := i.y) i.core i.p i.r i.z i.payload H + i.measure.budget i.x i.y J ≤
        BoundaryScale.cost (x := i.x) (y := i.y) i.D i.z i.payload i.r i.p j := by
  let g := copies (s := s) (d := d) (H := H)
  have c := controls (s := s) (d := d) (H := H)
  obtain ⟨a, ha⟩ := ((addr.pow H).add (g.slow.mul (addresses.pow J))).bound
  obtain ⟨b, hb⟩ := ((volume.pow H).add (g.mul (c.pow J))).bound
  obtain ⟨l, hl⟩ := (((ports (s := s) (d := d) (H := H)).pow H).add (exterior.pow J)).bound
  obtain ⟨k, hk⟩ := (((constant 5).add (old.pow H)).add (c.pow J)).bound
  let j := a + b + l + k
  refine ⟨j, fun i => ?_⟩
  have rr {X Y t : ℕ} (h : 2 ≤ Y) (f : X ≤ Y ^ t) (ht : t ≤ j) : X ≤ Y ^ j :=
    f.trans (Nat.pow_le_pow_right (by omega) ht)
  refine ⟨rr i.two_fast (hk i) (by unfold j; omega), ?_⟩
  have x := Nat.mul_le_mul_left (2 ^ i.D.scheme.m) (rr i.two_slow (ha i) (by unfold j; omega))
  have y := Nat.mul_le_mul_left (2 ^ (i.D.scheme.m + i.D.scheme.h)) (rr i.two_fast (hb i) (by unfold j; omega))
  have z := Nat.mul_le_mul_left (wd i.x + wd i.y) (rr i.two (hl i) (by unfold j; omega))
  have m := Nat.mul_le_mul_right (i.measure.long ^ J) i.hosts.1
  have b := Nat.mul_le_mul_right (i.measure.short ^ J) i.hosts.2
  rw [mul_add, ← mul_assoc] at x y
  rw [mul_add] at z
  change 2 ^ i.D.scheme.m * (100 + i.p.w + i.p.w ^ i.p.power + i.p.W + short i.core i.r i.z i.payload) ^ H +
    2 ^ (i.D.scheme.m + i.D.scheme.h) * (short i.core i.r i.z i.payload + i.p.W) ^ H +
    (wd i.x + wd i.y) * (100 + i.payload + i.p.W) ^ H + _ ≤
    2 ^ i.D.scheme.m * i.slow ^ j + 2 ^ (i.D.scheme.m + i.D.scheme.h) * i.fast ^ j + (wd i.x + wd i.y) * i.outer ^ j
  unfold Restore.Measure.budget
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Sample
end

/-!
# Restarting after local concentration

Compose admission, reduction of the core, and reassembly of the frozen
border. This is a transformation of the complete weighted state space.
The dictionaries and capacity limits are shared by all summands.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly
open scoped Classical

theorem restarts {k : Type} [Field k] {s : Plan} (hs : s.Fits)
    (q : Block k s.c 3 s.b s.n s.e s.K s.ρ s.loss) (d : ℕ) : ∃ K, 0 < K ∧ Restarts k s d K := by
  obtain ⟨a, ha⟩ := admission d
  obtain ⟨H, _, red⟩ := reduce hs q d
  obtain ⟨J, hJ⟩ := Recovery.run
  obtain ⟨b, hb⟩ := Sample.bounds s d H J
  obtain ⟨c, hc⟩ := restored_labels s hs d H
  let K := a + b + c + BoundaryScale.charge d * H + H + s.K + s.M + s.d + s.p + 2 * extra s + 15
  refine ⟨K, by unfold K; omega, ?_⟩
  intro F _ _ _ x y D T L z payload p r h
  have hz : 0 < s.b * z := Nat.mul_pos q.unit h.unit
  have hT : 0 < T := (Nat.mul_pos hz (pow_pos (show 0 < s.D by have := s.two hs; omega) _)).trans_le h.lower
  have hL := zero_le_one.trans h.positive
  obtain ⟨hfour, hsmall, hupper⟩ := h.pass (H := H) (by unfold K; omega)
  let A := border D s z
  obtain ⟨v⟩ := red F (x := x) (y := y) A T L z payload p r
    h.positive h.unit h.lower h.upper h.height h.room h.slack h.degree rfl h.single h.alphabet hfour hsmall hupper
  obtain ⟨hpos, hdeg, hprice⟩ := v.address (l := extra s) h (by unfold K; omega)
  obtain ⟨E, he, endStage⟩ := hJ x y v.pack payload hs h.unit h.upper hL p hpos hdeg hprice
  let X := Recovery.restored x y v.pack payload hs h.unit h.upper hL
  let Y := Recovery.measure v.pack s T payload p
  let B := BoundaryScale.short D z payload r p
  let S := BoundaryScale.cost (x := x) (y := y) D z payload r p
  let M := short A r z payload
  let menu := insert (admitLabel D) (v.keys ∪ E)
  let i : Sample s d H := ⟨F, x, y, D, T, L, z, payload, p, r, K, h, v⟩
  have raised {j : ℕ} (hj : j ≤ K) : B ^ j ≤ B ^ K :=
    Nat.pow_le_pow_right ((by decide : 0 < 2).trans_le i.two_fast) hj
  have h₁ := ha D s z payload x y p r h.degree (by have := h.address; omega)
  have h₂ := hb i
  have u₁ : 3 + 2 * D.scheme.ℓ ≤ B ^ K := h₁.1.trans (raised (by unfold K; omega))
  have u₂ : 5 + M ^ H + Y.short ^ J ≤ B ^ K := h₂.1.trans (raised (by unfold K; omega))
  have few : menu.card ≤ B ^ K := by
    have hs := Finset.card_insert_le (admitLabel D) (v.keys ∪ E)
    have hu := Finset.card_union_le v.keys E
    have hv : v.keys.card ≤ M ^ H := v.few
    unfold menu
    omega
  have f := (admit_transfer (x := x) (y := y) (payload := payload) hs hz h.positive hT h.single).widen
    (L' := ↑menu) u₁ (Set.singleton_subset_iff.mpr (Finset.mem_insert_self ..))
  have g := v.transfer.widen (L' := ↑menu) (show M ^ H ≤ B ^ K by omega)
    (fun _ ht => Finset.mem_insert_of_mem (Finset.mem_union_left _ ht))
  have e := endStage (C := ↑menu) (show 3 ≤ B ^ K by omega)
    (fun _ ht => Finset.mem_insert_of_mem (Finset.mem_union_right _ ht))
    (show Y.short ^ J ≤ B ^ K by omega)
  have cost : S a + S b ≤ S K :=
    BoundaryScale.plus.trans (BoundaryScale.increasing (by unfold K; omega))
  have net := (f.comp (g.comp e)).mono ((Nat.add_le_add h₁.2 h₂.2).trans cost)
  have st := Recovery.stable x y v.pack payload hs h.unit h.upper hL
  have low : D.scheme.m ≤ v.next.scheme.m := v.growth.lower
  have high : v.next.scheme.m ≤ D.scheme.m + s.n * r + s.K := v.growth.upper
  have height : v.next.scheme.h + s.n * r = D.scheme.h := v.growth.height
  refine ⟨⟨X, st.1, st.2, low.trans (Nat.le_add_right ..), ?_, height, le_rfl, rfl, rfl, ?_, ?_, menu, few, net⟩⟩
  · change v.next.scheme.m + extra s + v.next.scheme.h ≤ _
    unfold K
    omega
  · change v.next.scheme.h + (s.d + s.p + Nat.clog 2 T) ≤ v.next.scheme.h + s.d + s.p + Nat.clog 2 T
    omega
  · refine (hc v h).trans ?_
    have hk : c ≤ K := by unfold K; omega
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hk)
      (Nat.pow_le_pow_right ((by decide : 0 < 2).trans_le (BoundaryScale.two ..)) hk)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end
