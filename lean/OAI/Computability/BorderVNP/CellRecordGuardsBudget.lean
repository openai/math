import OAI.Computability.BorderVNP.CellRecordGuards
import OAI.Computability.BorderVNP.CellProfileBudget

/-! # Private instruction budget for a sparse directory's public guards

The bound covers selector ranges, actual prefix-counter rows, compact route
comparisons, zero pins, equalities, box-presence tests, and the allocation and
disposal of local auxiliary bits. The dimension parameter bounds the public
record fields and number of records before expansion into private bytecode.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Numeric fields affecting work in one public record. A box presence test
only checks its directory index, independently of its eventual contents. -/
def Record.GuardBound (M : ℕ) : Record → Prop
  | .zero c l p => c ≤ M ∧ l ≤ M ∧ Profile.PortBound M p
  | .equal c l p q => c ≤ M ∧ l ≤ M ∧ Profile.PortBound M p ∧ Profile.PortBound M q
  | .box .. => True
  | .profile c s w h rs => c ≤ M ∧ w ≤ M ∧ h.length ≤ M ∧ rs.length ≤ M ∧ Profile.PortBound M s ∧
      ∀ r ∈ rs, r.term ≤ M ∧ r.lanes ≤ M ∧ Profile.PortBound M r.original ∧ Profile.PortBound M r.compact

private theorem port_read_le {M i k : ℕ} {p : CellSparse.Port} (hp : Profile.PortBound M p)
    (hi : i ≤ M) (hk : k ≤ M) : p.atBit i k ≤ M + M*M + M*M := by
  obtain ⟨_,_,_⟩ := hp
  unfold Port.atBit
  gcongr

/-- The length of the working binary stream is bounded by the physical
instruction clock, including every unary offset. -/
theorem work_le_budget (s : Stmt) (env : List ℕ) : work s env ≤ budget (s.expand env) := by
  have h (ops : List Op) : (stream ops).length ≤ (ops.map Op.ticks).sum := by
    induction ops with
    | nil => rfl
    | cons o ops ih =>
      have ho : o.bits.length ≤ o.ticks := by
        cases o <;> simp [Op.bits, Op.ticks]
        omega
      change (o.bits ++ stream ops).length ≤ o.ticks + (ops.map Op.ticks).sum
      rw [List.length_append]
      exact Nat.add_le_add ho ih
  exact (h _).trans (Nat.le_add_right _ _)

private theorem range_cost {M c l : ℕ} (hc : c ≤ M) (hl : l ≤ M) (t : Term) (env : List ℕ)
    (ht : t.nodes ≤ 9) (hread : ∀ i < c, ∀ k < l, t.Bounded (k::i::env) (M+M*M+M*M)) :
    work (.loop (.lit c) (.loop (.lit l) t.guard)) env ≤ 16000*(M+2)^9 := by
  let cost := 9*(M+M*M+M*M+9+20)+5
  have h := work_loop_le (.lit c) _ env (l*cost) (fun i hi =>
    work_loop_le (.lit l) _ (i::env) cost (fun k hk => Term.work_guard_le _ _ (hread i hi k hk) ht))
  change work _ env ≤ c*(l*cost) at h
  apply h.trans
  calc
    _ ≤ M*(M*cost) := by gcongr
    _ ≤ _ := by
      dsimp [cost]
      nlinarith only [Nat.zero_le M, Nat.zero_le (M^2), Nat.zero_le (M^3), Nat.zero_le (M^4),
        Nat.zero_le (M^5), Nat.zero_le (M^6), Nat.zero_le (M^7), Nat.zero_le (M^8), Nat.zero_le (M^9)]

/-- A single bounded record uses at most degree-nine expanded bytecode length. -/
theorem recordGuard_work_le {M : ℕ} (boxes : List (List Factor)) (r : Record) (env : List ℕ)
    (hr : r.GuardBound M) : work (recordGuard boxes r) env ≤ 16000*(M+2)^9 := by
  cases r with
  | zero c l p =>
    obtain ⟨hc,hl,hp⟩ := hr
    apply range_cost hc hl _ env (by simp [Term.nodes])
    intro i hi k hk
    exact port_read_le hp (hi.le.trans hc) (hk.le.trans hl)
  | equal c l p q =>
    obtain ⟨hc,hl,hp,hq⟩ := hr
    apply range_cost hc hl _ env (by simp [Term.nodes])
    intro i hi k hk
    apply (Term.bounded_equal ..).mpr
    exact ⟨port_read_le hp (hi.le.trans hc) (hk.le.trans hl),
      port_read_le hq (hi.le.trans hc) (hk.le.trans hl)⟩
  | box id base c stride =>
    have h : work (recordGuard boxes (.box id base c stride)) env = 7 := rfl
    rw [h]
    have := Nat.one_le_pow 9 (M+2) (by omega)
    omega
  | profile c s w hist routes =>
    obtain ⟨hc, hw, hh, hr, hs, hroutes⟩ := hr
    let len := Profile.auxSize c hist.length
    have hlen : len ≤ (M+1)^3 := by
      change hist.length * ((c+1)*(c+1)) ≤ _
      calc
        _ ≤ (M+1)*((M+1)*(M+1)) := by gcongr; omega
        _ = _ := by ring
    have hb := Profile.budget_polynomial (base := 0) (off := len) env (Nat.zero_le _) hlen
      hc hw hh hr hs hroutes
    have hc' := (work_le_budget _ _).trans hb
    have hpow : (M+1)^3 ≤ (M+2)^9 :=
      (Nat.pow_le_pow_left (by omega : M+1 ≤ M+2) 3).trans (Nat.pow_le_pow_right (by omega) (by decide))
    change work (localFlags len _) env ≤ _
    rw [work_localFlags]
    change work (Profile.profileGen 0 len c s w hist routes) env + 13*len ≤ _
    omega

/-- The sum of the expanded binary lengths of all public record guards. -/
theorem Directory.recordGuards_work_le (D : Directory) (env : List ℕ) (M : ℕ)
    (h : ∀ r ∈ D.records, r.GuardBound M) :
    work D.recordGuards env ≤ D.records.length * (16000*(M+2)^9) := by
  rw [Directory.recordGuards, work_sequence, List.map_map]
  exact sum_map_le D.records _ _ (fun r hr => recordGuard_work_le D.boxes r env (h r hr))

/-- The physical stack decoder's clock for all public record checks is polynomial
of degree ten in the bound on record count and fields. -/
theorem Directory.recordGuards_budget (D : Directory) (env : List ℕ) (M : ℕ) (hn : D.records.length ≤ M)
    (h : ∀ r ∈ D.records, r.GuardBound M) :
    budget (D.recordGuards.expand env) ≤ 80000*(M+2)^10 + 2 := by
  calc
    _ ≤ 5 * work D.recordGuards env + 2 := budget_le _
    _ ≤ 5 * ((M+2) * (16000*(M+2)^9)) + 2 := by
      have he := D.recordGuards_work_le env M h
      gcongr
      apply he.trans
      gcongr; omega
    _ = _ := by ring

end CellSparse

end BorderVNP
end Computability
end OAI
