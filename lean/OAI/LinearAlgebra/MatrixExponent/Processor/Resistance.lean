import OAI.LinearAlgebra.MatrixExponent.Processor.Handle
import OAI.LinearAlgebra.MatrixExponent.Processor.WindowSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Broadcast

/-!
# Diagonal resistance over a finite field

One processor works for every replacement of the prescribed size.
Its literal codes can then be chosen independently at the different
sites. The controller and its size bound require no complexity assumptions.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Filter

variable {F : Type} [Field F] [Fintype F]

private theorem fit_window {N w W Q s : ℕ} (hs : W ≤ 2 * w) (hb : 2 ^ W ≤ N * w ^ (Q + 10))
    (hw : 200 ≤ w) : 2 ^ W * (100 + W) ^ (Q + s) ≤ N * w ^ ((Q + 10) + 2 * (Q + s)) := by
  rw [pow_add w, pow_mul, ← mul_assoc]
  exact Nat.mul_le_mul hb (Nat.pow_le_pow_left (by nlinarith : 100 + W ≤ w ^ 2) _)

theorem control (F : Type) [Field F] [Fintype F] : ControlBound F := by
  classical
  intro n h K Q hn hh hK A
  let t := (Q + 10) + 2 * (Q + 660)
  refine ⟨max t 5 + 1, ?_⟩
  filter_upwards [window n h K Q hn hh hK A, dispatch_scale A hn K t,
    eventually_ge_atTop 200] with w getW dispatch hw
  intro N r d l B fa hf _ P M hm hlabel hroom hex
  obtain ⟨W, H⟩ := getW fa M hm hex
  have hr : 0 < r := lt_of_lt_of_le (by decide) H.three
  let _ : NeZero r := ⟨hr.ne'⟩
  let _ : NeZero (3 * r) := ⟨by omega⟩
  have hn4 : 0 < N / 4 := by have := hex.some.links; have := Nat.le_pow (a := 3 * r) (by decide : 0 < 2); omega
  let _ : NeZero (N / 4) := ⟨hn4.ne'⟩
  let e := Fintype.equivFin (Name n r)
  let _ : LinearOrder (Name n r) := LinearOrder.lift' e e.injective
  have he : P.which = (Format.prescribed d h P.count P.colors).which := rfl
  have hg : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N := hf
  have hc (i) : Nonempty (Cells.Domain P ↪ Fin (2 ^ M.width i)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    apply (Nat.mul_le_mul_right_iff hr).mp
    exact (Cells.domain_size P hlabel (by omega) H.positions).trans (hroom i)
  let a : Cells.Address P M := fun i => (hc i).some
  let C := Cells.install hn he hg a hex.some
  have hwW : w ≤ W := by
    by_contra! hlt
    have hh := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    exact hh.not_ge H.limits.bits
  have hM : M.budget F ≤ 2 ^ W * (100 + W) ^ Q :=
    hm.trans (Nat.mul_le_mul H.limits.bits (Nat.pow_le_pow_left (by omega) _))
  refine ⟨C.numberInOrder, dispatch fa M C.numberInOrder ?_⟩
  intro i
  obtain ⟨f, hf, he⟩ := C.handles H he hg a rfl hM i
  exact ⟨f, hf.mono (fit_window H.small H.cost hw), he⟩

/-- A cheaply realizable family resists all sufficiently small
simultaneous implementations, even with quasilinear macro gates. -/
theorem resists (F : Type) [Field F] [Finite F] (K q : ℕ) :
    Diagonal.Resists F (Cheap F K q) := by
  let _ := Fintype.ofFinite F
  exact resists_of_programmable (programmable_of_control (control F) K q)

theorem hard_of_descent {F : Type} [Field F] [Finite F] {K q : ℕ}
    (h : Diagonal.Descent F (Cheap F K q)) : Tagged.Hard F :=
  hard_of_resists (resists F K q) h

end OAI.LinearAlgebra.MatrixExponent.Processor
