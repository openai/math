import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Pass
import OAI.LinearAlgebra.MatrixExponent.Assembly.FreezeInput.Retain
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels

/-! # Withdrawing arity-zero factors from a concentrated term -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Packing Rounds

variable {F : Type} [Field F] {x y : Wire} {h u : ℕ}

abbrev Rounds.LocalTerm.sweep (Q : LocalTerm F x y h u) : LocalTerm F x y h u :=
  { Q with diagram := Q.diagram.sweep
           freeze := ⟨Q.freeze.frozen, Q.freeze.exterior, Q.freeze.separate⟩
           frame := ⟨Q.frame.place, Q.frame.frozen, Q.frame.keep, Q.frame.N, Q.frame.C, Q.frame.ns,
             Q.frame.cs, Q.frame.sub, Q.frame.group, Q.frame.edge, Q.frame.full⟩ }

namespace Assembly.Template.Shows
variable {D : Template F} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u} (p : D.Shows r Q)

def sweep : D.sweep.Shows r Q.sweep where
  pres := p.pres.sweep
  host := p.host
  vertex := p.vertex
  directed t := by
    change D.scheme.direction r.1 (p.pres.sweepSeats.ends t).1 = _
    rw [p.pres.sweep_end]; exact p.directed t
  uniform t := by
    change D.scheme.width r.1 (p.pres.sweepSeats.ends (.inl (.inr t))).1 = _
    rw [p.pres.sweep_end]; exact p.uniform t
  index := p.index
  neighbor := p.neighbor
  live := p.live
  frozen := p.frozen
  closed := p.closed
  reciprocal := p.reciprocal
  edge := p.edge
  core := p.core
  charge := p.charge
  amount := p.amount

end Assembly.Template.Shows

namespace Rounds.Contraction.Publication
variable {D : Template F} {s : Plan} {T z payload : ℕ} {L : ℝ}
  (X : Publication (x := x) (y := y) D s T L z payload)

def sweep : Publication (x := x) (y := y) D.sweep s T L z payload where
  R := X.R
  g := X.g
  P := X.P
  Q := X.Q.sweep
  ready := ⟨X.ready.cells, X.ready.coreDegree, X.ready.fullDegree, X.ready.frozenCount,
    X.ready.frozenMax, X.ready.frozenSquare, X.ready.coreMax, X.ready.coreSum⟩
  live := X.live
  r := X.r
  showing := X.showing.sweep
  fits := X.fits

def Neutral : Prop :=
  ∀ v, X.Q.diagram.arity v = 0 → ∀ t, Transcript.sample (X.Q.diagram.table v) t = 1

theorem neutral : X.sweep.Neutral := X.Q.diagram.sweep_neutral

end Rounds.Contraction.Publication
end OAI.LinearAlgebra.MatrixExponent
end

/-! # Admission of a neutralized concentrated diagram -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Publication
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire} {D : Template F} {s : Plan} {T z payload : ℕ} {L : ℝ}
  (X : Publication (x := x) (y := y) D s T L z payload) (h : D.scheme.k = 0)
  (hs : s.Fits) (hz : 0 < s.b * z) (hL : 1 ≤ L) (hT : 0 < T)

local notation "u" => s.b * z
local notation "A" => D.border u (1 / (s.D : ℝ) ^ 4)
local notation "Z" => frozen hs L X.Q

abbrev packet := X.showing.encloses h hz Z rfl rfl

abbrev entry : Attachment.Data (A) x y u :=
  incoming hs L X.Q hz X.showing.packets (X.packet h hs hz)

include hL hT in
theorem ready_entry (hn : X.Neutral) :
    Ready (A) (fringe s T L) z s.c (s.D ^ s.c) (origin s T L) (X.entry h hs hz) := by
  refine incoming_ready hs (X.packet h hs hz) X.ready hL hT X.live (fun i => hn i.val) ?_ ?_
  · intro j
    exact (X.showing.span hz Z rfl rfl j).ge
  · intro i
    exact ⟨_, (X.showing.charge i.val).trans (Nat.cast_add ..).symm⟩

theorem fit_entry : (X.entry h hs hz).Fits payload := (X.showing.retag h Z).fits X.fits

theorem eval_entry : (X.entry h hs hz).diagram.eval = X.Q.diagram.eval :=
  funext fun i => funext fun j => X.Q.freeze.reconstruct i j

theorem store_entry (i : Val x) (j : Val y) :
    (X.entry h hs hz).data (X.fit_entry h hs hz) i j = D.scheme.store X.r.1 X.fits (X.showing.pres.exterior i j) :=
  eq_of_heq ((X.showing.retag h Z).store X.fits i j)

def out : (initial (x := x) (y := y) (border D s z) s T L z payload).state :=
  ⟨X.sweep.entry h hs hz, X.sweep.ready_entry h hs hz hL hT X.neutral, X.sweep.fit_entry h hs hz⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Publication
end

/-! # Converting concentrated terms into attached cores -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} (D : Template F) (s : Plan) (z payload : ℕ)

abbrev admitLabel := weightTable (A := .addr D.scheme.ℓ) (D := .addr D.scheme.ℓ) id D.scheme.scalar

theorem admitLabel_arity : Processor.arity (admitLabel D) = 2 * D.scheme.ℓ := by
  simp only [admitLabel, weightTable, Processor.arity, lookup, wd_word, Format.width_addr, two_mul]

def admitCost (x y : Wire) : ℕ :=
  let width := (Attachment.payload x y payload D.scheme.m).width
  updateCost D.scheme.m D.scheme.d D.scheme.h (.addr D.scheme.ℓ) (.addr D.scheme.ℓ) +
    4 * (Format.vec D.scheme.m D.header).width + 4 * width +
    (D.sweep.encloseCost (s.b * z) (1 / (s.D : ℝ) ^ 4) + 4 * width)

variable {D s z payload} {L : ℝ} {T : ℕ}
local notation "E" => publicEncoding (x := x) (y := y) D s T L z payload
local notation "A" => border D s z

theorem admit_transfer (hs : s.Fits) (hz : 0 < s.b * z) (hL : 1 ≤ L) (hT : 0 < T)
    (h : D.scheme.k = 0) : Transforms F (3 + 2 * D.scheme.ℓ) {admitLabel D}
      (publication (x := x) (y := y) D s T L z payload) (initial A s T L z payload)
      (admitCost D s z payload x y) := by
  let u := 3 + 2 * D.scheme.ℓ
  let G : Set (Table F) := {admitLabel D}
  have hu : 3 ≤ u := Nat.le_add_right ..
  have hE := (E).sweep_stage (L := G) hu (Nat.le_add_left ..) (Set.mem_singleton _)
  let f := D.sweep.enclose (s.b * z) (1 / (s.D : ℝ) ^ 4)
  have build := D.sweep.enclose_net (s.b * z) (1 / (s.D : ℝ) ^ 4) (L := G) hu
  have keep := Map.circuit (L := G) hu (Circuit.id F (E).payload)
  have net := build.par keep
  let out := fun i : Publication (x := x) (y := y) D s T L z payload => i.out h hs hz hL hT
  have after := Transforms.of_map (X := (E).sweep.snapshot) (Y := initial A s T L z payload)
    (Prod.map f id) out net
    (fun i => (Publication.eval_entry (Publication.sweep i) h hs hz).symm)
    (fun i a b => Prod.ext rfl (Publication.store_entry (Publication.sweep i) h hs hz a b).symm)
  exact hE.comp after

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Host, cell, and exterior-bit charges of the input stage -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Coloring

private theorem budget14 {n : ℕ} (hn : 100 ≤ n) :
    4 * n ^ 2 + 24 * n + 24 + n ^ 13 ≤ n ^ 14 := by
  have h₁ : n ≤ n ^ 13 := Nat.le_self_pow (by decide) n
  have h₂ : n ^ 2 ≤ n ^ 13 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ n ^ 13 * 100 := by omega
    _ ≤ n ^ 13 * n := Nat.mul_le_mul_left _ hn
    _ = _ := (pow_succ ..).symm

variable {F : Type} [Field F] (D : Template F) (s : Plan) (z payload : ℕ) (x y : Wire)
local notation "m" => D.scheme.m
local notation "h" => D.scheme.h
local notation "p" => (2 ^ D.scheme.d)
local notation "ℓ" => D.scheme.ℓ

theorem admit_cost :
    let short := 10000 + p + ℓ + D.count + payload
    admitCost D s z payload x y ≤ 2 ^ m * (short + m) ^ 14 + 2 ^ (m + h) * short ^ 14 +
      (wd x + wd y) * (100 + payload) ^ 14 := by
  intro short
  let t := short + m
  have hshort : 10000 + p + ℓ + D.count ≤ short := Nat.le_add_right ..
  have hp : p ≤ short := by unfold short; omega
  have hmin : 10000 ≤ short := by unfold short; generalize p = n; omega
  have hlong : short ≤ t := Nat.le_add_right ..
  have hw : payload ≤ short := Nat.le_add_left ..
  have hm : m ≤ t := Nat.le_add_left ..
  have hcost : D.sweep.encloseCost (s.b * z) (1 / (s.D : ℝ) ^ 4) ≤ 2 ^ m * t ^ 13 + 2 ^ (m + h) * short ^ 2 :=
    D.sweep.enclose_bound _ _ hshort
  have hh : (Format.vec D.scheme.m D.header).width = 2 ^ m * (2 + p * 2 + 2 ^ h * D.count) := by
    simp only [Template.header, Group.Flags, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [Format.width_bit]
    ring
  have hwidth : (Attachment.payload x y payload m).width ≤ (payload + 1) * (2 * (2 ^ m + wd x + wd y)) :=
    Fmt.width_payload ..
  have main : 4 * (p * m) + 8 * p + 16 * payload + 24 + t ^ 13 ≤ t ^ 14 := by
    have hu : p * m ≤ t ^ 2 := (Nat.mul_le_mul (hp.trans hlong) hm).trans_eq (pow_two t).symm
    have hb := budget14 (show 100 ≤ t by omega)
    omega
  have cell : 1 + 2 * ℓ + 4 * D.count + short ^ 2 ≤ short ^ 14 := by
    have hb := budget14 (show 100 ≤ short by omega)
    generalize p = n at hshort
    omega
  have bit : 16 * (payload + 1) ≤ (100 + payload) ^ 14 := by
    have hb := budget14 (show 100 ≤ 100 + payload by omega)
    omega
  unfold admitCost updateCost
  dsimp only
  rw [hh, Format.width_addr]
  calc
    _ ≤ 2 ^ m * (4 * (p * m) + 2 ^ h * (1 + ℓ + ℓ)) + 4 * (2 ^ m * (2 + p * 2 + 2 ^ h * D.count))
        + 4 * ((payload + 1) * (2 * (2 ^ m + wd x + wd y))) +
        (2 ^ m * t ^ 13 + 2 ^ (m + h) * short ^ 2 + 4 * ((payload + 1) * (2 * (2 ^ m + wd x + wd y)))) := by
      exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ hwidth) _)
        (Nat.add_le_add hcost (Nat.mul_le_mul_left _ hwidth))
    _ = 2 ^ m * (4 * (p * m) + 8 * p + 16 * payload + 24 + t ^ 13) +
        2 ^ (m + h) * (1 + 2 * ℓ + 4 * D.count + short ^ 2) + (wd x + wd y) * (16 * (payload + 1)) := by
      rw [pow_add]
      generalize t ^ 13 = T, short ^ 2 = S
      ring
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ main)
      (Nat.mul_le_mul_left _ cell)) (Nat.mul_le_mul_left _ bit)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end
