import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.IndexSpec
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.ReaderSpec
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.StringOrder

/-! # Correctness of gated writes and their single-gate realization -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Scatter.Upload

open Coloring

variable {X I : Type} {w d : ℕ} (u : Upload X I w)

theorem loaded [Fintype I] (x : X → Bool) (m : B w → Bool) (hm : u.Fits x m) :
    u.load x (Fintype.card I) = m := by
  funext z
  let e := Fintype.equivFin I
  let hit (i : I) := Sum.elim x id (u.enabled i) = true ∧ u.addr x i = z
  have progress (n : ℕ) (hn : n ≤ Fintype.card I)
      (h : m z = true → ∃ i, hit i ∧ (e i).val < n) : u.load x n z = m z := by
    induction n with
    | zero =>
      cases hz : m z
      · rfl
      · obtain ⟨_, _, hh⟩ := h hz
        omega
    | succ n ih =>
      have hl : n < Fintype.card I := by omega
      let i := e.symm ⟨n, hl⟩
      rw [load, dite_eq_left hl]
      change u.write x i (u.load x n) z = m z
      by_cases hi : hit i
      · rw [write, ite_eq_left hi.1, ← hi.2, Function.update_self]
        exact (hm.agrees i hi.1).symm
      · have prev : u.load x n z = m z := by
          apply ih hl.le
          intro hz
          obtain ⟨j, hj, hj'⟩ := h hz
          have ne : (e j).val ≠ n := by
            intro eq
            have eq' : j = i := e.injective ((Fin.ext eq).trans (e.apply_symm_apply _).symm)
            exact hi (eq' ▸ hj)
          exact ⟨j, hj, by omega⟩
        by_cases ha : Sum.elim x id (u.enabled i) = true
        · have neq : z ≠ u.addr x i := fun he => hi ⟨ha, he.symm⟩
          rw [write, ite_eq_left ha, Function.update_of_ne neq, prev]
        · rw [write, ite_eq_right ha, prev]
  apply progress _ le_rfl
  intro hz
  obtain ⟨i, hi⟩ := hm.covers z hz
  exact ⟨i, hi, (e i).isLt⟩

private def ref : X ⊕ Bool → BitRef X d := Sum.map id Sum.inl

private theorem read_ref (x : X → Bool) (s : Config w d) (a : X ⊕ Bool) :
    BitGate.read x s (ref a) = Sum.elim x id a := by
  cases a <;> rfl

def gate (i : I) : BitGate X w d where
  dst := none
  address := ref ∘ u.address i
  args := ![ref (u.enabled i), ref (u.source i), .inr (.inl false), .inr (.inl false)]
  op a old := (if a 0 then a 1 else old, old)

theorem gate_step (i : I) (x : X → Bool) (s : Config w d) :
    (u.gate i).step x s = ⟨s.reg, u.write x i s.mem⟩ := by
  have ha : (u.gate i).addr x s = u.addr x i :=
    congrArg (Control.decode w) (funext fun a => read_ref x s (u.address i a))
  simp only [BitGate.step, BitGate.result, ha]
  change Config.mk s.reg (Function.update s.mem (u.addr x i)
    (if BitGate.read x s (ref (u.enabled i)) then BitGate.read x s (ref (u.source i))
      else s.mem (u.addr x i))) = _
  rw [read_ref, read_ref, write]
  split <;> simp

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Scatter.Upload
end

/-!
# Adaptive continuation after a scatter upload

The static series uses one gate per upload, repeats the controller
circuit, then reads the outputs. Its length is independent of the
number of cells in the address space.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Scatter

open Coloring

variable {X I Z Y : Type} {w d : ℕ}

private def readout (a : B w) : BitGate X w d where
  dst := none
  address p := .inr (.inl ((Control.decode w).symm a p))
  args _ := .inr (.inl false)
  op _ old := (old, old)

private theorem readout_step (a : B w) (x : X → Bool) (s : Config w d) :
    (readout a).step x s = s ∧ ((readout a).result x s).2 = s.mem a := by
  have ha : (readout a).addr x s = a := (Control.decode w).apply_symm_apply a
  simp only [BitGate.step, BitGate.result, ha]
  simp [readout]

variable [Fintype I] [Fintype Y] (u : Upload X I w) (M : Controller Z Y w) (k : ℕ)

private def start (I : Type) [Fintype I] (M : Controller Z Y w) (t : ℕ) :=
  Fintype.card I + t * M.size

private def series : Series X w M.registers where
  initial := M.initial
  gate n :=
    if h : n < Fintype.card I then u.gate ((Fintype.equivFin I).symm ⟨n, h⟩)
    else if h' : n < start I M (2 ^ k) ∧ 0 < M.size then
      (M.circuit ⟨(n - Fintype.card I) % M.size, Nat.mod_lt _ h'.2⟩).gate M.halt
    else if ho : n - start I M (2 ^ k) < Fintype.card Y then
      readout (M.output ((Fintype.equivFin Y).symm ⟨n - start I M (2 ^ k), ho⟩))
    else readout 0

private theorem state_load (x : X → Bool) (n : ℕ) (hn : n ≤ Fintype.card I) :
    (series u M k).state x n = ⟨M.initial, u.load x n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : n < Fintype.card I := by omega
    rw [Series.state, ih hl.le, Upload.load, dite_eq_left hl]
    simp only [series, dite_eq_left hl, Upload.gate_step]

omit [Fintype Y] in
private theorem start_next (t : ℕ) : start I M (t + 1) = start I M t + M.size := by
  simp [start, Nat.add_mul, Nat.add_assoc]

private theorem gate_cycle (t n : ℕ) (ht : t < 2 ^ k) (hn : n < M.size) :
    (series u M k).gate (start I M t + n) = (M.circuit ⟨n, hn⟩).gate M.halt := by
  have ha : ¬start I M t + n < Fintype.card I := by unfold start; omega
  have hb : start I M t + n < start I M (2 ^ k) ∧ 0 < M.size := by
    have h := Nat.add_le_add_left (Nat.mul_le_mul_right M.size ht) (Fintype.card I)
    change start I M (t + 1) ≤ start I M (2 ^ k) at h
    rw [start_next] at h
    omega
  have hv : (start I M t + n - Fintype.card I) % M.size = n := by
    rw [start, Nat.add_assoc, Nat.add_sub_cancel_left]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hn]
  simp only [series, dite_eq_right ha, dite_eq_left hb, hv]

private theorem state_cycle (x : X → Bool) (t n : ℕ) (ht : t < 2 ^ k) (hn : n ≤ M.size) :
    (series u M k).state x (start I M t + n) =
      M.partialCycle ((series u M k).state x (start I M t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : n < M.size := by omega
    rw [← Nat.add_assoc, Series.state, gate_cycle u M k t n ht hl, Command.gate_step,
      ih hl.le, Controller.partialCycle, dite_eq_left hl]

private theorem state_run (x : X → Bool) (m : B w → Bool) (hm : u.Fits x m)
    (t : ℕ) (ht : t ≤ 2 ^ k) :
    (series u M k).state x (start I M t) = (M.cycle^[t]) ⟨M.initial, m⟩ := by
  induction t with
  | zero => simpa [start, u.loaded x m hm] using state_load u M k x _ le_rfl
  | succ t ih =>
    have hl : t < 2 ^ k := by omega
    rw [start_next, state_cycle u M k x _ _ hl le_rfl, ih hl.le, Function.iterate_succ_apply']
    rfl

private theorem gate_output (n : ℕ) (hn : n < Fintype.card Y) :
    (series u M k).gate (start I M (2 ^ k) + n) =
      readout (M.output ((Fintype.equivFin Y).symm ⟨n, hn⟩)) := by
  have ha : ¬start I M (2 ^ k) + n < Fintype.card I := by unfold start; omega
  have hb : ¬(start I M (2 ^ k) + n < start I M (2 ^ k) ∧ 0 < M.size) := by omega
  simp only [series, dite_eq_right ha, dite_eq_right hb, Nat.add_sub_cancel_left, dite_eq_left hn]

private theorem state_output (x : X → Bool) (n : ℕ) (hn : n ≤ Fintype.card Y) :
    (series u M k).state x (start I M (2 ^ k) + n) =
      (series u M k).state x (start I M (2 ^ k)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : n < Fintype.card Y := by omega
    rw [← Nat.add_assoc, Series.state, gate_output u M k n hl, (readout_step _ _ _).1, ih hl.le]

/-- One program and set of taps work for every input and compatible memory image. -/
theorem simulate :
    ∃ (p : RAM.Program X (clock (Fintype.card I) (Fintype.card Y) k M.size) w 4)
      (t : Y → RAM.Source X (clock (Fintype.card I) (Fintype.card Y) k M.size)),
      ∀ x m, u.Fits x m → ∀ y, p.eval x (t y) = ((M.cycle^[2 ^ k]) ⟨M.initial, m⟩).mem (M.output y) := by
  let j := clock (Fintype.card I) (Fintype.card Y) k M.size
  let pos (y : Y) : B j :=
    ⟨start I M (2 ^ k) + ((Fintype.equivFin Y) y).val,
      lt_of_lt_of_le (Nat.add_lt_add_left ((Fintype.equivFin Y) y).isLt _) (clock_ge _ _ _ _)⟩
  refine ⟨(series u M k).program j, fun y => .inr (.inr (pos y)), fun x m hm y => ?_⟩
  rw [Series.eval_wire]
  let a := (Fintype.equivFin Y) y
  change (((series u M k).gate (start I M (2 ^ k) + a.val)).result x
    ((series u M k).state x (start I M (2 ^ k) + a.val))).2 = _
  rw [gate_output u M k _ a.isLt, state_output u M k x _ a.isLt.le, (readout_step _ _ _).2,
    state_run u M k x m hm _ le_rfl]
  simp [a]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Scatter
end

/-! # Cost of restoring indexed messages and running a controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open Coloring

private theorem body_size (A : Format) (b : ℕ) : (Body A b).width ≤ 4 + A.width + 2 * 2 ^ b := by
  simp only [Body, Match.format, RAM.token, Format.width_pair, Format.width_vec]
  rw [Format.width_bit, Format.width_addr, mul_one]
  have := Nat.lt_two_pow_self (n := b)
  omega

/-- The fixed fields use the message count, and the strings use the total charge. -/
private theorem events_count (A : Format) (k M T : ℕ) :
    Fintype.card (Events A k M T) ≤ (k + 1) * (M * (4 + A.width) + 4 * T) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ s : Slot M T k, (4 + A.width + 2 * capacity s) :=
      Finset.sum_le_sum fun s _ => body_size A s.1.val
    _ = Fintype.card (Slot M T k) * (4 + A.width) + 2*∑ s : Slot M T k, capacity s := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ ≤ ((k + 1) * M) * (4 + A.width) + 2 * ((k + 1) * (2 * T)) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (card_slots M T k))
        (Nat.mul_le_mul_left _ (sum_capacity M T k))
    _ = _ := by ring

variable {h D k c j M g : ℕ}

private theorem log_size (hh : 2 ≤ h) (hD : 100 + k + c + Nat.clog 2 (h + 1) ≤ D) (hj : j ≤ k) :
    Nat.clog 2 (D ^ 2 * (2 ^ j + h ^ (c + 10))) ≤ 3 * D ^ 2 := by
  have hd : D ≤ D ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  let N := 2 ^ (D ^ 2)
  have hN : D ^ 2 ≤ N := Nat.lt_two_pow_self.le
  have hT : 2 ^ j ≤ N := Nat.pow_le_pow_right (by decide) (by omega)
  have hp : h ≤ 2 ^ D := (Nat.le_succ h).trans ((Nat.le_pow_clog (by decide) (h + 1)).trans
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have hG : h ^ (c + 10) ≤ N := calc
    _ ≤ h ^ D := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (2 ^ D) ^ D := Nat.pow_le_pow_left hp _
    _ = _ := by unfold N; rw [pow_two, pow_mul]
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ N * (2 * N) := Nat.mul_le_mul hN (by omega)
    _ ≤ N * (N * N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by unfold N; rw [← pow_add, ← pow_add]; congr 1; omega

private theorem scale {D a b : ℕ} (L : ℕ) (hd : 0 < D) (h : a ≤ b) :
    D ^ a * L ≤ D ^ b * L := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hd h)

private theorem scale_rows (x y : ℕ) (hxy : x ≤ y) (hy : 0 < y) :
    1 + (3 + 4 * x + 32 * 2 ^ (4 + 3)) ≤ 4104 * y := by omega

private theorem scale_bank (B x : ℕ) (hx : B ≤ x) (hpos : 0 < x) : B + x + 130 ≤ 132 * x := by omega

private theorem expense_bound {t w L B : ℕ} (hd : 100 ≤ D) (hl : 0 < L)
    (hb : B ≤ D ^ 5 * L) (ht : 2 ^ t ≤ D ^ 3 * L) (hw : 100 + t + w ≤ D ^ 3) :
    B + 2 ^ t + RAM.Program.expense t w 4 ≤ D ^ 10000 * L := by
  have hd' : 0 < D := by omega
  have hp : (100 + t + w) ^ 100 ≤ D ^ 300 := by
    have h := Nat.pow_le_pow_left hw 100
    rw [← pow_mul, show 3 * 100 = 300 from rfl] at h
    exact h
  have hs : 4104 ≤ D ^ 2 :=
    (show 4104 ≤ 100 ^ 2 by decide).trans (Nat.pow_le_pow_left hd _)
  have ha : 1 + (3 + 4 * (100 + t + w) ^ 100 + 32 * 2 ^ (4 + 3)) ≤ D ^ 302 := calc
    _ ≤ 4104 * D ^ 300 := scale_rows _ _ hp (pow_pos hd' _)
    _ ≤ D ^ 2 * D ^ 300 := Nat.mul_le_mul_right _ hs
    _ = _ := by rw [← pow_add]
  have hbig : 0 < D ^ 305 * L := Nat.mul_pos (pow_pos hd' _) hl
  have hb' : B ≤ D ^ 305 * L :=
    hb.trans (scale L hd' (by decide))
  calc
    _ = B + 2 ^ t * (1 + (3 + 4 * (100 + t + w) ^ 100 + 32 * 2 ^ (4 + 3))) + 130 := by
      unfold RAM.Program.expense
      rw [mul_add (2 ^ t) 1, mul_one]
      simp only [add_assoc]
    _ ≤ B + D ^ 3 * L * D ^ 302 + 130 := Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul ht ha) _) _
    _ = B + D ^ 305 * L + 130 := by rw [mul_right_comm (D ^ 3), ← pow_add]
    _ ≤ 132 * (D ^ 305 * L) := scale_bank _ _ hb' hbig
    _ ≤ D ^ 2 * (D ^ 305 * L) := Nat.mul_le_mul_right _ ((show 132 ≤ 4104 by decide).trans hs)
    _ = D ^ 307 * L := by rw [← mul_assoc, ← pow_add]
    _ ≤ _ := scale L hd' (by decide)

/-- Charge the message bank, ordinary input bits and the entire padded RAM verification. -/
theorem index_cost_with_inputs (A : Format) (Y : Type) [Fintype Y] (N : ℕ) (hh : 2 ≤ h)
    (hD : 100 + k + c + Nat.clog 2 (h + 1) ≤ D) (hj : j ≤ k) (hM : M ≤ h ^ c)
    (hA : A.width ≤ h ^ 2) (hY : Fintype.card Y ≤ D * 2 ^ j) (hg : g ≤ D)
    (hN : N ≤ D * (2 ^ j + h ^ (c + 10))) :
    let t := clock (Fintype.card (Events A k M (2 ^ j)) + N) (Fintype.card Y) j g
    let w := width A k M
    w ≤ D ^ 4 ∧ t ≤ D ^ 4 ∧
      Fintype.card (Bank A k M (2 ^ j)) + N + 2 ^ t + RAM.Program.expense t w 4 ≤
        D ^ 10000 * (2 ^ j + h ^ (c + 10)) := by
  let L := 2 ^ j + h ^ (c + 10)
  let I := Fintype.card (Events A k M (2 ^ j))
  let t := clock (I + N) (Fintype.card Y) j g
  let w := width A k M
  have hd : 100 ≤ D := by omega
  have hl : 0 < L := by unfold L; positivity
  have hsq : 10 * D ≤ D ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have hcube : 12 * D ^ 2 ≤ D ^ 3 := by rw [pow_succ' D 2]; exact Nat.mul_le_mul_right _ (by omega)
  have hten : 4 + A.width ≤ h ^ 10 := calc
    _ ≤ 2 * h ^ 2 := by have := Nat.pow_le_pow_left hh 2; omega
    _ ≤ h * h ^ 2 := Nat.mul_le_mul_right _ hh
    _ = h ^ 3 := (pow_succ' h 2).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hfields : M * (4 + A.width) ≤ h ^ (c + 10) := by
    rw [pow_add]
    exact Nat.mul_le_mul hM hten
  have hI : I ≤ 4 * (D * L) := calc
    _ ≤ (k + 1) * (M * (4 + A.width) + 4 * 2 ^ j) := events_count _ _ _ _
    _ ≤ D * (4 * L) := Nat.mul_le_mul (by omega) (by unfold L; omega)
    _ = _ := by ac_rfl
  have hT : 2 ^ j ≤ L := Nat.le_add_right _ _
  have hs : I + N + 2 ^ j * g + Fintype.card Y ≤ D ^ 2 * L := by
    have h₁ := hY.trans (Nat.mul_le_mul_left D hT)
    have h₂ : 2 ^ j * g ≤ D * L := by rw [mul_comm]; exact Nat.mul_le_mul hg hT
    have h₃ := Nat.mul_le_mul_right L hsq
    rw [mul_assoc] at h₃
    change N ≤ D * L at hN
    omega
  have hm : M ≤ L := by
    have he : h ^ c ≤ h ^ (c + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (hM.trans he).trans (Nat.le_add_left _ _)
  have ha : A.width ≤ L := by
    have he : h ^ 2 ≤ h ^ (c + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (hA.trans he).trans (Nat.le_add_left _ _)
  have small : D + L ≤ D ^ 2 * L := by
    have h₁ := Nat.le_mul_of_pos_left L (show 0 < D by omega)
    have h₂ := Nat.le_mul_of_pos_right D hl
    have h₃ := Nat.mul_le_mul_right L hsq
    rw [mul_assoc] at h₃
    omega
  have logs (a : ℕ) (h : a ≤ D ^ 2 * L) : Nat.clog 2 a ≤ 3 * D ^ 2 :=
    (Nat.clog_mono_right 2 h).trans (log_size hh hD hj)
  have hp := logs (1 + M) (by omega)
  have ha' := logs (8 + k + A.width) (by omega)
  have ht : t ≤ 3 * D ^ 2 := logs _ hs
  have hw : 100 + t + w ≤ D ^ 3 := by unfold w width; omega
  have hpw : 2 ^ t ≤ D ^ 3 * L := calc
    _ ≤ 2 ^ Nat.clog 2 (D ^ 2 * L) := Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 hs)
    _ ≤ 2 * (D ^ 2 * L) := pow_clog_le_twice (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  have hslot : Fintype.card (Slot M (2 ^ j) k) ≤ D * L :=
    (card_slots M (2 ^ j) k).trans (Nat.mul_le_mul (by omega) hm)
  have hb : Fintype.card (Bank A k M (2 ^ j)) + N ≤ D ^ 5 * L := by
    rw [Fintype.card_sum, Fintype.card_prod]
    change I + Fintype.card (Slot M (2 ^ j) k) * (Format.addr _).width + N ≤ _
    rw [Format.width_addr]
    calc
      _ = I + N + Fintype.card (Slot M (2 ^ j) k) * Nat.clog 2 (1 + M) := by ac_rfl
      _ ≤ D ^ 2 * L + (D * L) * (3 * D ^ 2) := Nat.add_le_add (by omega) (Nat.mul_le_mul hslot hp)
      _ = (1 + 3 * D) * (D ^ 2 * L) := by ring
      _ ≤ D ^ 3 * (D ^ 2 * L) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [← mul_assoc, ← pow_add]
  have hfour : D ^ 3 ≤ D ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  exact ⟨(show w ≤ D ^ 4 by omega), (show t ≤ D ^ 4 by omega), expense_bound hd hl hb hpw hw⟩

theorem index_cost (A : Format) (Y : Type) [Fintype Y] (hh : 2 ≤ h)
    (hD : 100 + k + c + Nat.clog 2 (h + 1) ≤ D) (hj : j ≤ k) (hM : M ≤ h ^ c)
    (hA : A.width ≤ h ^ 2) (hY : Fintype.card Y ≤ D * 2 ^ j) (hg : g ≤ D) :
    let t := clock (Fintype.card (Events A k M (2 ^ j))) (Fintype.card Y) j g
    let w := width A k M
    w ≤ D ^ 4 ∧ t ≤ D ^ 4 ∧
      Fintype.card (Bank A k M (2 ^ j)) + 2 ^ t + RAM.Program.expense t w 4 ≤
        D ^ 10000 * (2 ^ j + h ^ (c + 10)) := by
  simpa using index_cost_with_inputs A Y 0 hh hD hj hM hA hY hg (Nat.zero_le _)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-! # Zero extension of variable-length message records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open Coloring

/-- Keep the low-order bits of a little-endian word in place. -/
private def low : (b k : ℕ) → b ≤ k → slots (word b) ↪ slots (word k)
  | 0, _, _ => ⟨Empty.elim, fun i => i.elim⟩
  | _ + 1, 0, h => (Nat.not_succ_le_zero _ h).elim
  | b + 1, k + 1, h => (Function.Embedding.refl Unit).sumMap (low b k (Nat.le_of_succ_le_succ h))

private theorem zero_bits (k : ℕ) (y : Val (word k)) (hy : Lookup.value k y = 0) :
    ∀ i, bits (word k) y i = false := by
  induction k with
  | zero => exact fun i => i.elim
  | succ k ih =>
    obtain ⟨a, y⟩ := y
    have ha : a = false ∧ Lookup.value k y = 0 := by cases a <;> simp_all [Lookup.value]
    rintro (i|i)
    · exact ha.1
    · exact ih y ha.2 i

private theorem low_bits (b k : ℕ) (h : b ≤ k) (x : Val (word b)) (y : Val (word k))
    (he : Lookup.value b x = Lookup.value k y) :
    (∀ i, bits (word k) y (low b k h i) = bits (word b) x i) ∧
    (∀ i ∉ Set.range (low b k h), bits (word k) y i = false) := by
  induction b generalizing k with
  | zero => exact ⟨fun i => i.elim, fun i _ => zero_bits k y he.symm i⟩
  | succ b ih =>
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨a, x⟩ := x
      obtain ⟨c, y⟩ := y
      have hc : c = a ∧ Lookup.value b x = Lookup.value k y := by
        cases a <;> cases c <;> simp [Lookup.value] at he ⊢ <;> omega
      obtain ⟨h₀, h₁⟩ := ih k (Nat.le_of_succ_le_succ h) x y hc.2
      constructor
      · rintro (i|i)
        · exact hc.1
        · exact h₀ i
      · rintro (i|i) hi
        · exact (hi ⟨.inl i, rfl⟩).elim
        · exact h₁ i (fun ⟨z, hz⟩ => hi ⟨.inr z, congrArg Sum.inr hz⟩)

private theorem address_bits {b k : ℕ} (h : b ≤ k) (x : B b) (y : B k) (he : x.val = y.val) :
    (∀ i, (Format.addr k).code y (low b k h i) = (Format.addr b).code x i) ∧
    (∀ i ∉ Set.range (low b k h), (Format.addr k).code y i = false) :=
  low_bits b k h _ _ ((Lookup.value_bits x.isLt).trans (he.trans (Lookup.value_bits y.isLt).symm))

variable (A : Format) {b k : ℕ} (h : b ≤ k)

/-- Flags and keys stay fixed. Length bits and payload positions keep their indices. -/
def stretch : (Body A b).pins ↪ (Body A k).pins :=
  let same := Function.Embedding.refl Unit
  let payload := (Fin.castLEEmb (Nat.pow_le_pow_right (by decide : 0 < 2) h)).prodMap same
  let data := (low (b + 1) (k + 1) (Nat.succ_le_succ h)).sumMap payload
  same.sumMap (same.sumMap ((Function.Embedding.refl A.pins).sumMap (same.sumMap data)))

private theorem fits {n b : ℕ} (h : n ≤ 2 ^ b) : n < 2 ^ (b + 1) := by
  rw [pow_succ]
  have := Nat.two_pow_pos b
  omega

variable (row : Bool × A.obj × List Bool) (len : row.2.2.length ≤ 2 ^ b)

include len in
theorem stretch_eq (i : (Body A b).pins) :
    packet A k row (stretch A h i) = packet A b row i := by
  have hb := fits len
  have hk := fits (len.trans (Nat.pow_le_pow_right (by decide : 0 < 2) h))
  simp only [packet, RAM.encodeToken, dite_eq_left hb, dite_eq_left hk]
  rcases i with i|i|i|i|i|i <;> try rfl
  exact (address_bits (Nat.succ_le_succ h) ⟨_, hb⟩ ⟨_, hk⟩ rfl).1 i

include len in
theorem stretch_zero (i : (Body A k).pins) (hi : i ∉ Set.range (stretch A h)) :
    packet A k row i = false := by
  have hb := fits len
  have hk := fits (len.trans (Nat.pow_le_pow_right (by decide : 0 < 2) h))
  simp only [packet, RAM.encodeToken, dite_eq_left hk]
  rcases i with i|i|i|i|i|⟨i, t⟩
  · exact (hi ⟨.inl i, rfl⟩).elim
  · exact (hi ⟨.inr (.inl i), rfl⟩).elim
  · exact (hi ⟨.inr (.inr (.inl i)), rfl⟩).elim
  · exact (hi ⟨.inr (.inr (.inr (.inl i))), rfl⟩).elim
  · apply (address_bits (Nat.succ_le_succ h) ⟨_, hb⟩ ⟨_, hk⟩ rfl).2 i
    rintro ⟨l, rfl⟩
    exact hi ⟨.inr (.inr (.inr (.inr (.inl l)))), rfl⟩
  · have he : 2 ^ b ≤ i.val := by
      by_contra! small
      exact hi ⟨.inr (.inr (.inr (.inr (.inr (⟨i.val, small⟩, t))))), rfl⟩
    change row.2.2[i.val]?.getD false = false
    rw [List.getElem?_eq_none (len.trans he)]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-!
# Sparse initialization of ordered messages

Each available bit writes at its own column and the message's
binary ordinal. Length and payload have the same low-order
positions in every bucket. Unallocated higher positions are zero
by RAM initialization, even for an absent ordinal.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
open Coloring
open scoped Classical

variable {I : Type} {A : Format} {n T : I → ℕ} {k M : ℕ}

theorem memory_at (row : Rows A n) (i : I) (o : (Position M).obj) (a : (Body A k).pins) :
    memory k M row i (address A k M (o, a)) =
      if h : o.val < n i then packet A k (row i ⟨o.val, h⟩) a else false :=
  (address A k M).injective.extend_apply _ _ _

def targetPin {t : ℕ} (e : Events A k M t) : (Body A k).pins :=
  stretch A (Nat.le_of_lt_succ e.1.1.isLt) e.2

def upload (A : Format) (k M t : ℕ) : Scatter.Upload (Bank A k M t) (Events A k M t) (width A k M) where
  address e b := Sum.map (fun v => .inr (e.1, v)) id (wire A k M (targetPin e) b)
  enabled e := .inl (.inl ⟨e.1, .inl ()⟩)
  source e := .inl (.inl e)

variable (row : Rows A n) (p : Layout row M k T) (hm : ∀ i, n i ≤ M) (i : I)
local notation "U" => upload A k M (T i)
local notation "x" => bank row p hm i

private theorem write_at (e : Events A k M (T i)) :
    (U).addr x e = address A k M (order row p hm i e.1, targetPin e) := by
  rw [← addr]
  apply congrArg (Control.decode _)
  funext b
  unfold upload
  simp only [Function.comp_apply]
  cases wire A k M (targetPin e) b <;> rfl

theorem write_in_range (e : Events A k M (T i)) :
    (U).addr x e ∈ Set.range (address A k M) :=
  ⟨_, (write_at row p hm i e).symm⟩

private theorem length_bound (t : Fin (n i)) :
    (row i t).2.2.length ≤ 2 ^ ((p i).toSlot t).1.val := by
  rw [(p i).level]
  exact (le_max_right ..).trans (Nat.le_pow_clog (by decide) _)

theorem sparse : (U).Fits x (memory k M row i) where
  agrees := by
    rintro ⟨s, b⟩ h
    change (code row p s.1 ⟨i, s.2⟩).1 = true at h
    have hr : s ∈ Set.range (p i).toSlot := by
      by_contra hn
      rw [unused row p i s hn] at h
      contradiction
    obtain ⟨t, rfl⟩ := hr
    rw [write_at, memory_at]
    have ht : (order row p hm i ((p i).toSlot t)).val = t.val := by
      rw [order_val, (p i).atSlot]
      rfl
    simp only [ht, dite_eq_left t.isLt]
    let s := (p i).toSlot t
    change packet A k (row i t) (stretch A _ b) = (Body A s.1.val).code (code row p s.1 ⟨i, s.2⟩) b
    rw [atSlot row p i t]
    exact stretch_eq A _ _ (length_bound row p i t) b
  covers := by
    intro z hz
    have hr : z ∈ Set.range (address A k M) := by
      by_contra hn
      unfold memory at hz
      rw [Function.extend_apply' _ _ _ hn] at hz
      contradiction
    obtain ⟨⟨o, b⟩, rfl⟩ := hr
    rw [memory_at] at hz
    split at hz
    swap
    · contradiction
    rename_i hi
    let t : Fin (n i) := ⟨o.val, hi⟩
    let s := (p i).toSlot t
    have hle := Nat.le_of_lt_succ s.1.isLt
    have hv : b ∈ Set.range (stretch A hle) := by
      by_contra hn
      exact Bool.false_ne_true ((stretch_zero A hle (row i t) (length_bound row p i t) b hn).symm.trans hz)
    obtain ⟨a, ha⟩ := hv
    refine ⟨⟨s, a⟩, congrArg Prod.fst (atSlot row p i t), ?_⟩
    rw [write_at]
    have he : order row p hm i s = o := Fin.ext (by rw [order_val, (p i).atSlot]; rfl)
    exact congrArg (address A k M) (Prod.ext he ha)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-!
# An adaptive reader for ordered message tapes

The RAM starts with zeroed storage. A gated write for each reserved
bit places the fields at addresses indexed by the local ordinal.
The resulting program can run any clocked controller on this memory.
In particular, an arbitrary payload bit is available using one
addressed read, even when both indices are data-dependent.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring

namespace Spec
variable {X : Type} {k H : ℕ} (S : Spec X k H)
    {n : S.Who → ℕ} (j : S.Who → Level k) (row : Strings.Rows S.key n)
    (p : Strings.Layout row S.messages k (fun i => 2 ^ (j i).val)) (hm : ∀ i, n i ≤ S.messages)
    (f : (i : S.Who) → Fin (S.guesses i.1 (j i)) → Bool)

/-- Both the payload and the ordinal are taken from the charged local record. -/
theorem bank_at (i : S.Who) :
    (S.ordered j row p hm f i.1 i.2).2 ∘ S.source i.1 (j i) = Strings.bank row p hm i := by
  funext a
  cases a with
  | inl e => rfl
  | inr v =>
    let F : Fin (S.guesses i.1 (j i)) ⊕ S.OrderBits (j i) → Bool :=
      Sum.elim (f i) (fun a => (Strings.Position S.messages).code (Strings.order row p hm i a.1) a.2)
    exact congrArg F ((S.orderPins i.1 (j i)).symm_apply_apply (.inr v))

end Spec

namespace Strings

theorem payload_at {I : Type} {A : Format} {n : I → ℕ} {k M : ℕ}
    (row : Rows A n) (i : I) (bound : ∀ v, (row i v).2.2.length ≤ 2 ^ k)
    (o : (Position M).pins → Bool) (b : slots (word k) → Bool) :
    let u := ((Position M).code.symm o).val
    memory k M row i (Control.decode (width A k M) (Sum.elim o (Sum.elim b id) ∘ payloadWire A k M)) =
      if h : u < n i then (row i ⟨u, h⟩).2.2[(Control.decode k b).val]?.getD false else false := by
  intro u
  rw [payload_addr_bits, memory_at]
  split
  · exact packet_bit _ _ _ _ (bound _)
  · rfl

/-- The program and its output taps are independent of the number,
contents, order and actual lengths of the messages. -/
theorem simulate (A : Format) (k M : ℕ) {Z Y : Type} [Fintype Y]
    (C : Controller Z Y (width A k M)) (j : ℕ) :
    let t := fun T => clock (Fintype.card (Events A k M T)) (Fintype.card Y) j C.size
    ∃ (P : (T : ℕ) → RAM.Program (Bank A k M T) (t T) (width A k M) 4)
      (tap : (T : ℕ) → Y → RAM.Source (Bank A k M T) (t T)),
      ∀ (I : Type) (n T : I → ℕ) (row : Rows A n) (p : Layout row M k T) (hm : ∀ i, n i ≤ M)
        (i : I) (y : Y),
        (P (T i)).eval (bank row p hm i) (tap (T i) y) =
          ((C.cycle^[2 ^ j]) ⟨C.initial, memory k M row i⟩).mem (C.output y) := by
  intro t
  choose P tap good using fun T => Scatter.simulate (upload A k M T) C j
  exact ⟨P, tap, fun _ _ _ row p hm i y => good _ _ _ (sparse row p hm i) y⟩

end Strings
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end
