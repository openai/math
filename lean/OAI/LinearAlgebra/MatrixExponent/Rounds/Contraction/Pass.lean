import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Label
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.FreezeInput.Retain
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

/-! # Transferring the exterior after a change of host or station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case.Child
open Assembly Coloring Width
variable {κ : Type} [Field κ] {b d B : ℕ} {N : (i : Case κ b d B) → Template i.F}
  {δ j p z : Case κ b d B → ℕ} (h : Child N δ) (hj : Short (fun i => 2 ^ j i))
  (hp : Short (fun i => 2 ^ p i)) (hz : Short (fun i => 2 ^ z i))
local notation "I" => Case κ b d B

private theorem loadsShort : Short (fun i : I => i.payload) :=
  (Poly.of_le base_two (fun i : I => by
    unfold base Contraction.base
    have := Nat.zero_le (2 ^ i.r)
    have := Nat.zero_le (2 ^ i.A.k)
    have := Nat.zero_le (2 ^ i.A.e)
    have := Nat.zero_le (2 ^ i.T.scheme.e)
    omega)).grow base_short

include h hj in
private theorem rowLog : Short (fun i : I => i.A.carryRows (N i) (j i)) := by
  have a : Short (fun i : I => i.height + (i.A.k + i.A.e)) := levels.short.add (stations.short.of_exp.add ports.short.of_exp)
  have v := ((levels.short.mono h.extent).add (hj.of_exp.add (expMax ports.short h.spans).of_exp))
  exact (a.add v).mono (fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..))

include h hj in
private theorem rowCount : Row (fun i : I => 2 ^ i.A.carryRows (N i) (j i)) := by
  have a : Row (fun i : I => 2 ^ i.height * 2 ^ (i.A.k + i.A.e)) :=
    (Short.block (stations.short.exp_add ports.short)).blocks
  have v := h.layer (Short.block (hj.exp_add (expMax ports.short h.spans)))
  refine (a.add v).mono fun i => ?_
  unfold Attachment.carryRows
  rw [← pow_add, ← pow_add]
  rcases le_total (i.height + (i.A.k + i.A.e)) ((N i).scheme.h + (j i + i.A.spanBits (N i))) with a|a
  · rw [max_eq_right a]; exact Nat.le_add_left ..
  · rw [max_eq_left a]; exact Nat.le_add_right ..

include h hj hz in
theorem carryWidth : Short (fun i : I => i.A.carryWidth (N i) (j i) (z i) i.payload) := by
  have ptr : Short (fun i : I => i.A.pointer.width) := pair bit (pair (addr levels.short) (addr stations.short.of_exp))
  have req := pair (addr (h.transport hj)) (vec hj ptr)
  have rep := pair (addr hz.of_exp) (pair (addr (loadsShort.add (short_const 1))) (addr (h.rowLog hj)))
  exact req.add (vec hj (vec (expMax ports.short h.spans) rep))

include h in
private theorem bothHosts {f : I → ℕ} (hf : Row f) :
    Cost (fun i => (2 ^ i.m + 2 ^ (N i).scheme.m) * f i) := by
  simpa only [add_mul] using hf.hosts.add (h.cost hf)

include h hj hz in
private theorem emit : Cost (fun i : I => SpanPlan.emitCost i.m (N i).scheme.m (i.payload + 1) (z i)
    (i.A.carryRows (N i) (j i))) := by
  have w : Short (fun i : I => i.payload + 1) := loadsShort.add (short_const 1)
  have rows := h.rowCount hj
  have exp := rows.mul hz.block
  have size := ((short_const 100).add (((((short_const 2).mul (h.rowLog hj)).add hz.of_exp).add w))).pow 140
  have work := h.bothHosts (exp.mul (Short.block size))
  have entry := pair (addr hz.of_exp) (pair (addr w) (pair (addr w) (addr w)))
  have records : Row (fun i : I => (Format.vec (i.A.carryRows (N i) (j i))
      (Fragments.Entry (i.payload + 1) (z i))).width) :=
    (rows.mul (Short.block entry)).mono fun _ => (Format.width_vec ..).le
  have unit := (Short.long (addr w)).row
  have lengths := (Short.long (vec hz (addr w))).row
  have tab := pack unit (pack lengths records)
  have grid := pack (parent.vector tab) (h.vector tab)
  have ll := pack (parent.vector unit) (parent.vector lengths)
  have lr := pack (h.vector unit) (h.vector lengths)
  have keys : Cost (fun i : I => (Format.vec (i.m + z i) (.addr ((N i).scheme.m + z i))).width) :=
    ((Long.row (addr (h.address.add hz.long.of_exp))).expand hz.block).mono fun _ => (Format.width_vec ..).le
  have cols := pack (pack (pack ll lr) keys) (pack (parent.vector records) (h.vector records))
  refine (work.add (grid.add (cols.scale 34))).mono fun i => ?_
  rw [SpanPlan.emitCost, pow_add]

include h hj hp hz in
private theorem prep : Cost (fun i : I => i.A.carryPrep (N i) (j i) (z i) i.payload (p i)) := by
  have input := pack (h.requests hj hp) (h.attached (h.transport hj))
  have act := h.cost (h.layer (Short.block ((short_const 1).add (h.carryWidth hj hz))))
  have size := ((short_const 110).add ((short_const 4).mul ((hz.of_exp.add (h.rowLog hj)).add loadsShort))).pow 200
  have rows := (h.rowCount hj).mul (Short.block size)
  have data := (h.cost rows).add (Row.hosts (rows.left hz.block))
  refine (((((input.add act).add data).add (h.emit hj hz)).scale 1000)).mono fun i => ?_
  unfold Attachment.carryPrep
  simp only [add_mul, mul_assoc]
  rfl

include h in
private theorem volume : Total (fun i : I => Attachment.volume i.x i.y (N i).scheme.m) := by
  simpa only [Attachment.volume, add_assoc, mul_one] using
    (h.cost (long_const 1).row).total.add (outer_const 1).total

include h hj hp hz in
theorem carryCost : Total (fun i : I =>
    i.A.carryCost (N i) (j i) (p i) (z i) i.x i.y i.payload i.p) := by
  obtain ⟨K, hK⟩ := Prices.shipment_le
  have small : Outer (fun i : I => 1000 + i.p.W + i.payload + i.payload) :=
    (((outer_const 1000).add price).add loads).add loads
  have medium := ((small.block.add hz.block.of_exp).add (loads.block.add (block_const 1))).add (h.rowLog hj).block
  have big := ((((Block.long medium).add hosts).add h.address).add world).add power
  have row := (Long.row (big.pow K)).add ((h.rowCount hj).mul (medium.pow K))
  have work := h.bothHosts (row.left hz.block)
  have traffic := (parent.volume.add h.volume).mul (small.pow K)
  have costs := (Cost.total (((h.attached (h.transport hj)).scale 4).add work)).add traffic
  refine ((h.prep hj hp hz).total.add costs).mono fun i => ?_
  unfold Attachment.carryCost
  apply Nat.add_le_add_left
  simpa only [mul_assoc] using hK i.F i.p (i.A.transport (N i) (j i)).format.width
    i.m (Attachment.volume i.x i.y i.m) i.payload
    (N i).scheme.m (Attachment.volume i.x i.y (N i).scheme.m) i.payload
    (z i) (i.payload + 1) (i.A.carryRows (N i) (j i))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case.Child
end

/-! # The common state space after local concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire}
    (D : Template F) (s : Plan) (T : ℕ) (L : ℝ) (z payload : ℕ)

structure Publication where
  R : ℕ
  g : ℕ
  P : Rounds.Input F x y D.scheme.h s.D T R g (10000 * L)
  Q : LocalTerm F x y D.scheme.h (s.b * z)
  ready : Concentrated P Q s.C s.d 10
  live : Nonempty Q.V
  r : D.format.obj
  showing : D.Shows r Q
  fits : D.scheme.Fits r.1 (2 ^ D.scheme.m + wd x + wd y) payload

abbrev publicEncoding :
    Encoding (fun i : Publication (x := x) (y := y) D s T L z payload => i.Q.diagram) where
  scheme := D.scheme
  volume := 2 ^ D.scheme.m + wd x + wd y
  height := payload
  extra := .vec D.scheme.m D.header
  rows i := i.r.1
  data i := i.r.2
  presents i := i.showing.pres
  fits i := i.fits

abbrev publication : Snapshot.{1} F x y := (publicEncoding D s T L z payload).snapshot
abbrev border := D.sweep.border (s.b * z) (1 / (s.D : ℝ) ^ 4)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Resource limits from a published term to the next charged board -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly
variable {F : Type} [Field F] {x y : Wire}

namespace BoundaryScale
variable (D : Template F) (z payload r : ℕ) (p : Prices F)

def base := 100 + 2 ^ r + D.scheme.h + Nat.clog 2 (1 + z) + 2 ^ D.scheme.e + payload + Nat.clog 2 (1 + D.scheme.ℓ + D.count)
def metadata := base D z payload r + D.scheme.ℓ + D.count
def short := metadata D z payload r + p.W
def outer := 100 + p.W + D.scheme.h + payload + D.scheme.e + Nat.clog 2 (1 + z)
def long := 100 + p.w + p.w ^ p.power + short D z payload r p
def cost (K : ℕ) :=
    2 ^ D.scheme.m * (long D z payload r p) ^ K + 2 ^ (D.scheme.m + D.scheme.h) * (short D z payload r p) ^ K +
      (wd x + wd y) * (outer D z payload p) ^ K

end BoundaryScale

structure Requirements (D : Template F) (s : Plan) (T : ℕ) (L : ℝ) (z payload : ℕ) (p : Prices F)
    (r d K : ℕ) : Prop where
  positive : 1 ≤ L
  unit : 0 < z
  lower : (s.b * z) * s.D ^ s.c ≤ T
  upper : T ≤ z * s.M
  height : s.n * r ≤ D.scheme.h
  room : s.K ≤ 2 ^ r
  slack : (s.K : ℝ) * T * (2 ^ (D.scheme.m + D.scheme.h) : ℕ) ≤ L * (2 : ℝ) ^ r
  degree : D.scheme.d ≤ d
  single : D.scheme.k = 0
  alphabet : Nat.clog 2 (Nat.card F) ≤ 2 ^ r
  small : (BoundaryScale.metadata D z payload r) ^ K ≤ D.scheme.m
  address : 4 * D.scheme.m ≤ p.w

structure Restored (D : Template F) (s : Plan) (T : ℕ) (L : ℝ) (z payload : ℕ) (p : Prices F)
    (r K : ℕ) where
  next : Layer F x y
  ready : next.Ready s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor
  loopless : next.Loopless
  lower : D.scheme.m ≤ next.template.scheme.m
  seats : next.template.scheme.m + next.template.scheme.h ≤ D.scheme.m + D.scheme.h + K
  blocks : next.template.scheme.h + s.n * r = D.scheme.h
  ports : next.template.scheme.e ≤ 5
  degree : next.template.scheme.d = 3
  volume : next.volume = 2 ^ next.template.scheme.m + wd x + wd y
  height : next.height ≤ next.template.scheme.h + s.d + s.p + Nat.clog 2 T
  labels : next.template.scheme.ℓ + next.template.count ≤
    K * (D.scheme.ℓ + D.count) + (BoundaryScale.base D z payload r) ^ K
  keys : Finset (Table F)
  few : keys.card ≤ (BoundaryScale.short D z payload r p) ^ K
  transfer : Transforms F ((BoundaryScale.short D z payload r p) ^ K) keys
    (publication D s T L z payload) next.snapshot (BoundaryScale.cost (x := x) (y := y) D z payload r p K)

def Restarts (k : Type) [Field k] (s : Plan) (d K : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra k F] {x y : Wire} (D : Template F)
    (T : ℕ) (L : ℝ) (z payload : ℕ) (p : Prices F) (r : ℕ),
    Requirements D s T L z payload p r d K → Nonempty (Restored (x := x) (y := y) D s T L z payload p r K)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Metadata lengths immediately after cutting off the border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Coloring

variable {F : Type} [Field F] (D : Template F) (s : Plan) (z payload r : ℕ)

theorem width_bits {s : Plan} {T z : ℕ} (h : T ≤ z * s.M) : Nat.clog 2 T ≤ Nat.clog 2 (1 + z) + s.M := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  exact h.trans (Nat.mul_le_mul ((Nat.le_add_left ..).trans (Nat.le_pow_clog (by decide) _))
    Nat.lt_two_pow_self.le)

abbrev inside := D.sweep.cut (s.b * z) (1 / (s.D : ℝ) ^ 4)

theorem cut_length :
    (inside D s z).scheme.ℓ = D.scheme.ℓ + 1 + 2 ^ D.scheme.d ∧
    (border D s z).ℓ = D.scheme.ℓ + 1 + 2 ^ D.scheme.d + D.count ∧
    (inside D s z).count = 1 + D.count := by
  refine ⟨D.sweep.scheme.cut_length, D.sweep.border_length .., ?_⟩
  change (Format.pair .bit (.addr D.count)).width = _
  rw [Format.width_pair, Format.width_bit, Format.width_addr]

namespace BoundaryScale

omit [Field F] in
theorem base_lower : 100 + 2 ^ r + D.scheme.h + Nat.clog 2 (1 + z) + 2 ^ D.scheme.e + payload ≤ base D z payload r :=
  Nat.le_add_right ..

omit [Field F] in
theorem two : 2 ≤ base D z payload r := by
  have := base_lower D z payload r
  have := Nat.zero_le (2 ^ r)
  have := Nat.zero_le (2 ^ D.scheme.e)
  omega

omit [Field F] in
theorem lower : base D z payload r ≤ metadata D z payload r := by unfold metadata; omega

private theorem logarithm (a b c : ℕ) :
    Nat.clog 2 (1 + (a + 1 + 2 ^ b) + (a + 1 + 2 ^ b + c)) ≤ Nat.clog 2 (1 + a + c) + b + 3 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  have h := Nat.le_pow_clog (by decide : 1 < 2) (1 + a + c)
  have h₁ := Nat.le_mul_of_pos_right (2 ^ Nat.clog 2 (1 + a + c)) (Nat.two_pow_pos b)
  have h₂ := Nat.le_mul_of_pos_left (2 ^ b) (Nat.two_pow_pos (Nat.clog 2 (1 + a + c)))
  rw [pow_add, pow_add]
  omega

variable {d : ℕ} (hd : D.scheme.d ≤ d)
include hd

theorem cut_base : Contraction.base (border D s z) r z payload ≤ 3 * base D z payload r + d := by
  obtain ⟨h₁, h₂, _⟩ := cut_length D s z
  change 100 + 2 ^ r + D.scheme.h + Nat.clog 2 (1 + z) + 2 + 2 ^ D.scheme.e + 2 ^ D.scheme.e + payload+
    Nat.clog 2 (1 + (inside D s z).scheme.ℓ + (border D s z).ℓ) ≤ _
  rw [h₁, h₂]
  have h := logarithm D.scheme.ℓ D.scheme.d D.count
  have := Nat.zero_le (2 ^ r)
  have := Nat.zero_le (2 ^ D.scheme.e)
  unfold base
  omega

theorem cut_short : Contraction.short (border D s z) r z payload ≤
    4 * metadata D z payload r + (4 + d + 2 * 2 ^ d) := by
  have h := cut_base D s z payload r hd
  have hg := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  change Contraction.base (border D s z) r z payload + (inside D s z).scheme.ℓ +
    (border D s z).ℓ + (inside D s z).count ≤ _
  obtain ⟨h₁, h₂, h₃⟩ := cut_length D s z
  rw [h₁, h₂, h₃]
  unfold metadata
  omega

end BoundaryScale

variable {D s z payload r} {T d K K' : ℕ} {L : ℝ} {p : Prices F}

theorem Requirements.shrink (h : Requirements D s T L z payload p r d K) (hk : K' ≤ K) :
    Requirements D s T L z payload p r d K' :=
  { h with small := (Nat.pow_le_pow_right
      ((show 0 < 2 by decide).trans_le ((BoundaryScale.two ..).trans (BoundaryScale.lower ..))) hk).trans h.small }

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Capacity required to pass from a printed diagram to the core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly
variable {F : Type} [Field F] {x y : Wire} {D : Template F} {s : Plan} {p : Prices F}
  {r d z payload T H K : ℕ} {L : ℝ}

namespace BoundaryScale

theorem linear {N : ℕ} (hn : 2 ≤ N) (a b : ℕ) : a * N + b ≤ N ^ (a + b + 1) := by
  have hf := Nat.lt_two_pow_self (n := a + b)
  have hb := Nat.le_mul_of_pos_right b (show 0 < N by omega)
  calc
    _ ≤ (a + b) * N := by rw [add_mul]; omega
    _ ≤ N ^ (a + b) * N := Nat.mul_le_mul_right _ (hf.le.trans (Nat.pow_le_pow_left hn _))
    _ = _ := (pow_succ ..).symm

def charge (d : ℕ) := 4 + (4 + d + 2 * 2 ^ d) + 1

theorem coded (hd : D.scheme.d ≤ d) :
    Contraction.short (border D s z) r z payload ≤ (metadata D z payload r) ^ (charge d) :=
  (cut_short D s z payload r hd).trans (linear ((two ..).trans (lower ..)) _ _)

theorem origin (hd : D.scheme.d ≤ d) :
    Contraction.base (border D s z) r z payload ≤ (base D z payload r) ^ (3 + d + 1) :=
  (cut_base D s z payload r hd).trans (linear (two ..) _ _)

theorem increasing (hj : H ≤ K) : cost (x := x) (y := y) D z payload r p H ≤
    cost (x := x) (y := y) D z payload r p K := by
  have hm := (two D z payload r).trans (lower ..)
  have hS : 0 < short D z payload r p := by unfold short; omega
  have hO : 0 < outer D z payload p := by unfold outer; omega
  have hL : 0 < long D z payload r p := by unfold long; positivity
  unfold cost
  gcongr

theorem plus : cost (x := x) (y := y) D z payload r p H + cost (x := x) (y := y) D z payload r p K ≤
    cost (x := x) (y := y) D z payload r p (max H K + 1) := by
  have hm := (two D z payload r).trans (lower ..)
  have hs : 2 ≤ short D z payload r p := by unfold short; omega
  have ho : 2 ≤ outer D z payload p := by unfold outer; omega
  have hl : 2 ≤ long D z payload r p := hs.trans (Nat.le_add_left ..)
  unfold cost
  rw [add_add_add_comm, add_add_add_comm (2 ^ D.scheme.m * _ ^ H), ← mul_add, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (BatchDescent.Phase.Poly.pow_sum hl ..))
    (Nat.mul_le_mul_left _ (BatchDescent.Phase.Poly.pow_sum hs ..)))
    (Nat.mul_le_mul_left _ (BatchDescent.Phase.Poly.pow_sum ho ..))

end BoundaryScale

theorem Requirements.pass (h : Requirements D s T L z payload p r d K)
    (hk : BoundaryScale.charge d * H + 5 ≤ K) :
    4 * D.scheme.h ≤ D.scheme.m ∧ (short (border D s z) r z payload) ^ H ≤ D.scheme.m ∧
      2 * (D.scheme.m + s.n * r + s.K) ≤ p.w := by
  let a := BoundaryScale.metadata D z payload r
  have hm : 2 ≤ a := (BoundaryScale.two ..).trans (BoundaryScale.lower ..)
  have hb := (BoundaryScale.base_lower D z payload r).trans (BoundaryScale.lower ..)
  have hx : 4 * a ≤ D.scheme.m := calc
    _ ≤ a ^ 5 := BoundaryScale.linear hm 4 0
    _ ≤ a ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := h.small
  have height := h.height
  have room := h.room
  have address := h.address
  have := Nat.zero_le (2 ^ D.scheme.e)
  have := Nat.zero_le (2 ^ r)
  refine ⟨by omega, ?_, by omega⟩
  calc
    _ ≤ (a ^ BoundaryScale.charge d) ^ H := Nat.pow_le_pow_left (BoundaryScale.coded h.degree) H
    _ ≤ a ^ K := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := h.small

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end
