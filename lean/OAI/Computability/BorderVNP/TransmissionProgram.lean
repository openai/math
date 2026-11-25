import OAI.Computability.BorderVNP.TransmissionModel

/-! # Execution of the complete physical transmission directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Memory obtained by processing the first rows in order. Guesses are indexed by
row and bit offset; an unrelated team's row has no memory effect. -/
def tableMemory (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) (bits : ℕ → ℕ → Bool) : ℕ → Memory w
  | 0 => m
  | i+1 => (rows i).apply self pub (tableMemory rows self pub m bits i) (bits i)

/-- Public directory address after consuming `i` rows with the indicated stride. -/
def cursorAt (base stride : Word w) (i : ℕ) : Word w :=
  base + i • stride

/-- Numeric conditions for executing a selected row. The sender's comparison and
all read-only arithmetic are checked against the memory after the preceding bits. -/
def Range.allowed (row : Range w) (self : Word w) (pub : Arg → Word w) (m : Memory w)
    (bits : ℕ → Bool) : Prop :=
  ∃ role, row.selected self = some role ∧
    ∀ mode, role = some mode → ∀ j < row.width.val, ∀ t : Bank w,
      rangeBank t = row → t 0 = self → t 1 = 1 → t 2 = 0 → t 16 = Fin.ofNat _ j →
      mode.permits pub t (rangeMemory mode pub (row.bank self) m bits j)

private theorem ready_of_allowed {row : Range w} {self : Word w} {pub : Arg → Word w}
    {m : Memory w} {bits : ℕ → Bool} {s : Bank w}
    (ok : row.allowed self pub m bits) (hr : rangeBank s = row)
    (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0) :
    ∃ role, row.selected self = some role ∧ Ready role pub s m bits := by
  obtain ⟨role, sel, allow⟩ := ok
  refine ⟨role, sel, ?_⟩
  intro mode hmode j hj t ht
  have eq (i : Reg) (hi : i.val < 16) : t i = s i := by
    rw [ht i hi.le, Function.update_of_ne (by intro e; subst i; omega)]
  have tr : rangeBank t = row := by
    rw [← hr]
    simp only [rangeBank, eq 8 (by decide), eq 9 (by decide), eq 10 (by decide), eq 11 (by decide),
      eq 12 (by decide), eq 13 (by decide), eq 14 (by decide), eq 15 (by decide)]
  rw [Range.memory_eq hr hself h1 h0]
  exact allow mode hmode j ((congrArg Range.width hr) ▸ hj) t tr
    ((eq 0 (by decide)).trans hself) ((eq 1 (by decide)).trans h1) ((eq 2 (by decide)).trans h0)
    ((ht 16 (by decide)).trans (Function.update_self ..))

/-- Register contents on arrival at row `i`, including the two independent directory cursors. -/
structure AtRow (teamId base count ord : Word w) (i : ℕ) (s : Bank w) : Prop where
  /-- The executing team. -/
  team : s 0 = teamId
  /-- Unit increment word. -/
  one : s 1 = 1
  /-- Word used for zero tag and offset. -/
  zero : s 2 = 0
  /-- Address of the next seven-word descriptor. -/
  baseAddr : s 3 = cursorAt base 7 i
  /-- Total number of rows loaded at startup. -/
  bound : s 4 = count
  /-- Number of completed descriptors. -/
  index : (s 5).val = i
  /-- Address of the next ordinal word. -/
  ordinal : s 6 = cursorAt ord 1 i

private theorem directory_step {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {m : Memory w} {s : Bank w} {self base count ord : Word w} {i : ℕ} {r : Range w}
    (hs : AtRow self base count ord i s) (hi : i < count.val)
    (table : rangeAt m (cursorAt base 7 i) (cursorAt ord 1 i) = r)
    (bits : ℕ → Bool) (ok : r.allowed self pub m bits) :
    ∃ es t, Runs pub macros step s m es t (r.apply self pub m bits) ∧
      AtRow self base count ord (i+1) t ∧ traceCost es ≤ 19 + decision.depth + r.teamCost self := by
  obtain ⟨es,a,load,hc,ha,ha3,ha6,hoff,hkeep⟩ := loadRange_runs pub macros s m hs.one hs.zero
  have hr : rangeBank a = r := by rwa [hs.baseAddr, hs.ordinal, table] at ha
  have ateam := (hkeep 0 (by decide) (by decide)).trans hs.team
  have aone := (hkeep 1 (by decide) (by decide)).trans hs.one
  have azero := (hkeep 2 (by decide) (by decide)).trans hs.zero
  obtain ⟨role,sel,hready⟩ := ready_of_allowed ok hr ateam aone azero
  obtain ⟨fs,b,dispatch,low,hf⟩ := Decision.run pub macros a m bits
    ((Range.role_eq hr ateam aone azero).trans sel) aone hoff hready
  rw [decision_code, Range.finished_eq hr ateam aone azero sel] at dispatch
  let t := Function.update b 5 (b 5 + b 1)
  have inc : Runs pub macros (.binary .add 5 5 1) b (r.apply self pub m bits) [tick w] t
      (r.apply self pub m bits) := Runs.localStep _ rfl rfl
  refine ⟨_,t,load.seq (dispatch.seq inc),?_,?_⟩
  · have same (j : Reg) (hj : j.val < 16) (h5 : j ≠ 5) : t j = a j :=
      (Function.update_of_ne h5 ..).trans (low j hj)
    refine ⟨(same 0 (by decide) (by decide)).trans ateam, (same 1 (by decide) (by decide)).trans aone,
      (same 2 (by decide) (by decide)).trans azero, ?_, ?_, ?_, ?_⟩
    · rw [same 3 (by decide) (by decide), ha3, hs.baseAddr]
      simp only [cursorAt, add_nsmul, one_nsmul, add_assoc]
    · exact (same 4 (by decide) (by decide)).trans ((hkeep 4 (by decide) (by decide)).trans hs.bound)
    · have h5 := hkeep 5 (by decide) (by decide)
      have hfit : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt count.isLt
      simp only [t,Function.update_self,low 5 (by decide),low 1 (by decide),aone,h5,
        Fin.val_add, hs.index]
      have hw : 1 < 2^w := by omega
      simp [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hfit]
    · rw [same 6 (by decide) (by decide), ha6, hs.ordinal]
      simp only [cursorAt, add_nsmul, one_nsmul, add_assoc]
  · have hp : r.teamCost self = payloadCost role (a 11).val := by
      rw [Range.teamCost, sel, ← congrArg Range.width hr]
      rfl
    rw [cost_append,cost_append,hc,hp]
    change 17 + (traceCost fs + 1) ≤ _
    omega

/-- The fixed program reads its two public directory cursors, executes each incident
range on the current team, and produces the ordered memory fold. Its charge is linear
in the number of rows plus payload work on this team alone. -/
theorem table_runs (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (bits : ℕ → ℕ → Bool)
    (table : ∀ i < (directoryFrame pub m 13).val,
      rangeAt (tableMemory rows (directoryFrame pub m 0) pub m bits i)
        (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = rows i)
    (allowed : ∀ i < (directoryFrame pub m 13).val,
      (rows i).allowed (directoryFrame pub m 0) pub
        (tableMemory rows (directoryFrame pub m 0) pub m bits i) (bits i)) :
    ∃ es t, Runs pub macros transmitRanges s m es t
        (tableMemory rows (directoryFrame pub m 0) pub m bits (directoryFrame pub m 13).val) ∧
      traceCost es ≤ setup.slots + (20 + decision.depth) * (directoryFrame pub m 13).val +
        (∑ i ∈ Finset.range (directoryFrame pub m 13).val, (rows i).teamCost (directoryFrame pub m 0)) + 1 := by
  let self := directoryFrame pub m 0
  let base := directoryFrame pub m 12
  let count := directoryFrame pub m 13
  let ord := directoryFrame pub m 20
  let M := tableMemory rows self pub m bits
  let Inv := fun i t mt => AtRow self base count ord i t ∧ mt = M i
  let cost := fun i => 19 + decision.depth + (rows i).teamCost self
  obtain ⟨es,a,rs,hc,hself,h1,h0,h5,h3,h4,h6⟩ := setup_runs pub macros s m
  have init : Inv 0 a m :=
    ⟨⟨hself,h1,h0,by simpa [cursorAt,base] using h3,h4,by simp [h5],by simpa [cursorAt,ord] using h6⟩,rfl⟩
  have oneStep i (hi : i < count.val) t mt (h : Inv i t mt) :
      ∃ es z mz, Runs pub macros step t mt es z mz ∧ Inv (i+1) z mz ∧ traceCost es ≤ cost i := by
    rcases h with ⟨h, rfl⟩
    obtain ⟨fs,z,r,hz,hf⟩ := directory_step (macros := macros) h hi (table i hi) (bits i) (allowed i hi)
    exact ⟨fs,z,_,r,⟨hz,rfl⟩,hf⟩
  obtain ⟨fs,z,mz,r,hz,hf⟩ := loop_runs 5 4 step count.val cost Inv
    (fun _ _ _ h => ⟨h.1.index, congrArg Fin.val h.1.bound⟩) oneStep 0 (Nat.zero_le _) a m init
  refine ⟨_,z,rs.seq (hz.2 ▸ r),?_⟩
  rw [cost_append]
  have he : (∑ i ∈ Finset.Ico 0 count.val, (cost i + 1)) =
      (20 + decision.depth) * count.val + ∑ i ∈ Finset.range count.val, (rows i).teamCost self := by
    rw [Nat.Ico_zero_eq_range]
    have eq (i : ℕ) : cost i + 1 = (20 + decision.depth) + (rows i).teamCost self := by
      dsimp [cost]; omega
    simp only [eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    ring
  rw [he] at hf
  exact (Nat.add_le_add hc hf).trans (by dsimp [count,self]; omega)

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
