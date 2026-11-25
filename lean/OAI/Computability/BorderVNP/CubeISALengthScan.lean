import OAI.Computability.BorderVNP.CubeISALengthCode

/-! # Executing the read-only scans at finite word width -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeLengths

open VPVNP.BurstRAM Finset

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Reflect a fitted read-only guard, using its real execution and exact register image. -/
theorem readTest (c : Code) (s : Bank w) (m : Memory w)
    (ok : Prop) (P : NatState → Prop) (det : c.deterministic = true)
    (fit : c.relaxReject.safeReadOnly w (readings pub) (readings m) (readings s))
    (guard : c.safeReadOnly w (readings pub) (readings m) (readings s) ↔ ok)
    (out : P ⟨c.evalNat (readings pub) (readings m) (readings s), readings m⟩) :
    TestRun pub mac c s m c.slots ok P := by
  have run (good : ok) : BoundedRun pub mac c s m c.slots P := by
    obtain ⟨es,t,r,cap,eq⟩ := c.runReadOnly pub mac m s (guard.mpr good)
    exact ⟨es,t,m,r,cap,show P ⟨readings t,readings m⟩ by rw [eq]; exact out⟩
  refine ⟨run,fun r => ?_⟩
  have pass := guard.mp (r.checked det fit)
  exact ⟨pass,((run pass).asTest det).sound r |>.2⟩

/-- The cursor, exclusive bound, two loop operands, increment and pivot, together with
the caller-visible values retained after each visited position. -/
structure ScanState (regs : Reg → ℕ) (mem : ℕ → ℕ) (N A B V i : ℕ) (z : NatState) : Prop where
  /-- All words and low registers survive. -/
  kept : Kept regs mem z
  /-- Current flat ordinal or coordinate. -/
  cursor : z.reg 56 = i
  /-- The loop's exclusive bound. -/
  limit : z.reg 57 = N
  /-- Computed row or column-total base. -/
  left : z.reg 58 = A
  /-- Declared row base or candidate coordinate. -/
  right : z.reg 59 = B
  /-- Increment operand. -/
  one : z.reg 60 = 1
  /-- Width of the candidate, or zero during row verification. -/
  value : z.reg 61 = V

private theorem frameSafe (d : Reg) (f : Word 8) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (readFrame d 62 63 f).safeReadOnly w p m s ↔ p 0+f.val < 2^w := by
  simp (config := {decide := true}) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits]
  omega

/-- Both address additions of a secondary field read fit the runtime word. -/
theorem fieldSafe (d : Reg) (f : Word 8) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ)
    (hf : p 0+63 < 2^w) (hh : frameField p m 63+f.val < 2^w) :
    (field d f).safeReadOnly w p m s := by
  simp (config := {decide := true}) [field,Code.block,Code.safeReadOnly,frameSafe,readFrameFixed,
    Code.evalNat,addressOpFits,hf,hh]
  omega

/-- Natural register image of a secondary field read. -/
theorem fieldValue (d : Reg) (f : Word 8) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (field d f).evalNat p m s =
      Function.update (Function.update (Function.update s 63 f.val) 62 (frameField p m 63 + f.val)) d
        (m (frameField p m 63 + f.val)) := by
  simp (config := {decide := true}) [field,Code.block,Code.evalNat,readFrameFixed,addressOp,
    Function.update_comm (by decide : (63 : Reg) ≠ 62)]

/-- Read-only execution preserves caller-visible state if all destinations are scratch. -/
theorem keptEval {regs : Reg → ℕ} {mem : ℕ → ℕ} {s : Bank w} {m : Memory w}
    (c : Code) (p : Arg → ℕ) (hc : c.protects 56 = true) (hk : Kept regs mem (.ofWords s m)) :
    Kept regs mem ⟨c.evalNat p (readings m) (readings s),readings m⟩ :=
  ⟨hk.1,fun j hj => (c.evalNat_protected _ _ _ hc j hj).trans (hk.2 j hj)⟩

private theorem setup (forRows : Bool) (s : Bank w) (m : Memory w)
    (h : Fits w (readings pub) (readings m)) :
    let l := layout (readings pub) (readings m)
    let c := if forRows then rowSetup else minSetup
    TestRun pub mac c s m c.slots True (ScanState (readings s) (readings m)
      (if forRows then l.entries else l.coordinates)
      (if forRows then l.actual else l.totals) (if forRows then l.claimed else l.chosen) 0 0) := by
  have ok (d : Reg) (f : Word 8) (hf : f.val ≤ 5) (z : Reg → ℕ) :=
    fieldSafe d f (readings pub) (readings m) z h.primary (by have := h.header; omega)
  have hw : 1 < 2^w := by have := h.primary; omega
  have zero : 0 < 2^w := Nat.two_pow_pos _
  have init : Kept (readings s) (readings m) (.ofWords s m) := ⟨rfl, fun _ _ => rfl⟩
  have fits0 := ok 58 0 (by decide)
  have fits1 := ok 59 1 (by decide)
  have fits2 := ok 57 2 (by decide)
  have fits3 := ok 58 3 (by decide)
  have fits4 := ok 57 4 (by decide)
  have fits5 := ok 59 5 (by decide)
  cases forRows <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    apply readTest _ s m True _ (by decide)
  all_goals first
    | change rowSetup.safeReadOnly w (readings pub) (readings m) (readings s)
    | change minSetup.safeReadOnly w (readings pub) (readings m) (readings s)
    | skip
  all_goals first
    | solve | simp (config := {decide := true}) [minSetup,rowSetup,Code.block,Code.safeReadOnly,
          fits0,fits1,fits2,fits3,fits4,fits5,hw,zero]
    | refine ⟨keptEval _ _ (by decide) init,?_,?_,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [layout,minSetup,rowSetup,Code.block,Code.evalNat,fieldValue]

private theorem evalReqEq (x y : Reg) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).evalNat p m s = s := by simp [requireEq,Code.evalNat]

private theorem safeReqEq (x y : Reg) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).safeReadOnly w p m s ↔ s x = s y := by simp [requireEq,Code.safeReadOnly]

private theorem fitReqEq (x y : Reg) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).relaxReject.safeReadOnly w p m s := by
  simp [requireEq,Code.relaxReject,Code.safeReadOnly]

/-- Native row-equality scan, starting at the beginning of both arrays. -/
theorem rows_run (s : Bank w) (m : Memory w) (fit : Fits w (readings pub) (readings m)) :
    let l := layout (readings pub) (readings m)
    TestRun pub mac rows s m (rowSetup.slots + l.entries*(rowBody.slots+1)+1)
      (RowsAgree l (readings m)) (Kept (readings s) (readings m)) := by
  let p := readings pub
  let mem := readings m
  let l := layout p mem
  let I := ScanState (readings s) mem l.entries l.actual l.claimed 0
  let good i := mem (l.actual+i) = mem (l.claimed+i)
  have step (i : ℕ) (hi : i < l.entries) (t : Bank w) (mt : Memory w) (hs : I i (.ofWords t mt)) :
      TestRun pub mac rowBody t mt rowBody.slots (good i) (I (i+1)) := by
    have a : l.actual+i < 2^w := by have := fit.actual; change l.actual + l.entries ≤ _ at this; omega
    have b : l.claimed+i < 2^w := by have := fit.claimed; change l.claimed + l.entries ≤ _ at this; omega
    have count : l.entries < 2^w := (m (frameField p mem 63+2)).isLt
    have inc : i+1 < 2^w := by omega
    have h56 : readings t 56 = i := hs.cursor
    have h58 : readings t 58 = l.actual := hs.left
    have h59 : readings t 59 = l.claimed := hs.right
    have h60 : readings t 60 = 1 := hs.one
    have hm : readings mt = mem := hs.kept.1
    apply readTest _ t mt _ _ (by decide)
    · change (Code.block [.binary .add 62 58 56, .load 62 62, .binary .add 63 59 56,
        .load 63 63, (requireEq 62 63).relaxReject, .binary .add 56 56 60]).safeReadOnly _ _ _ _
      simp (config := {decide := true}) [Code.block,Code.safeReadOnly,Code.evalNat_relaxReject,
        evalReqEq,fitReqEq,Code.evalNat,addressOp,addressOpFits,h56,h58,h59,h60,a,b,inc]
    · simp (config := {decide := true}) [rowBody,Code.block,safeReqEq,Code.safeReadOnly,evalReqEq,
        Code.evalNat,addressOp,addressOpFits,h56,h58,h59,h60,hm,a,b,inc,good]
    · refine ⟨keptEval _ _ (by decide) hs.kept,?_,?_,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [rowBody,Code.block,evalReqEq,Code.evalNat,addressOp,
          h56,h58,h59,h60] <;> first | exact hs.limit | exact hs.value
  have init := setup (mac := mac) true s m fit
  apply (init.seq fun t mt hz => test_counted_loop 56 57 rowBody l.entries (fun _ => rowBody.slots)
      good I (fun _ _ hz => ⟨hz.cursor,hz.limit⟩) step 0 (Nat.zero_le _) t mt hz).mono
  · simp [Finset.sum_const,Nat.add_assoc,l,mem,p]
  · simp [RowsAgree,good,l,mem,p]
  · exact fun _ hz => hz.kept

private theorem minGuard_eval (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    minGuard.evalNat p m s = s := by simp [minGuard,requireLt,Code.evalNat]

private theorem minGuard_safe (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    minGuard.safeReadOnly w p m s ↔ if s 56 < s 59 then s 61 < s 62 else s 61 ≤ s 62 := by
  by_cases h : s 56 < s 59 <;> simp [minGuard,requireLt,Code.safeReadOnly,h]

private theorem minGuard_fit (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    minGuard.relaxReject.safeReadOnly w p m s := by
  simp [minGuard,requireLt,Code.relaxReject,Code.safeReadOnly]

private theorem ifLtReject {x y : Reg} {body : Code} {s : Bank w} {m : Memory w}
    {good : Prop} {P : NatState → Prop} {cost : ℕ}
    (next : s x < s y → TestRun pub mac body s m cost good P) :
    TestRun pub mac (.ifLt x y body .reject) s m (cost+1) (s x < s y ∧ good) P := by
  constructor
  · rintro ⟨lt,g⟩
    obtain ⟨es,t,mt,r,cap,post⟩ := (next lt).complete g
    exact ⟨_,t,mt,Runs.ifLt (by simpa [lt] using r),
      show 1+traceCost es ≤ cost+1 by omega,post⟩
  · intro es t mt r
    cases r with
    | atom atomic _ _ => cases atomic
    | ifLt run =>
      by_cases lt : s x < s y
      · rw [ite_eq_left lt] at run
        obtain ⟨ok,post⟩ := (next lt).sound run
        exact ⟨⟨lt,ok⟩,post⟩
      · rw [ite_eq_right lt] at run
        cases run with | atom ha _ _ => cases ha

/-- Range-check the raw coordinate and certify its least-minimizer property against
the actual loaded totals. A bad tie or a surplus coordinate has no returning path. -/
theorem minimum_run (s : Bank w) (m : Memory w) (fit : Fits w (readings pub) (readings m)) :
    let l := layout (readings pub) (readings m)
    TestRun pub mac minimum s m (minSetup.slots+pivot.slots+l.coordinates*(minBody.slots+1)+2)
      (Least l (readings m)) (Kept (readings s) (readings m)) := by
  let mem := readings m
  let p := readings pub
  let l := layout p mem
  let V := mem (l.totals+l.chosen)
  let I := ScanState (readings s) mem l.coordinates l.totals l.chosen V
  let good j := if j < l.chosen then V < mem (l.totals+j) else V ≤ mem (l.totals+j)
  have step (i : ℕ) (hi : i < l.coordinates) (t : Bank w) (mt : Memory w) (hs : I i (.ofWords t mt)) :
      TestRun pub mac minBody t mt minBody.slots (good i) (I (i+1)) := by
    have a : l.totals+i < 2^w := by have := fit.totals; change l.totals+l.coordinates ≤ _ at this; omega
    have count : l.coordinates < 2^w := (m (frameField p mem 63+4)).isLt
    have inc : i+1 < 2^w := by omega
    have h56 : readings t 56 = i := hs.cursor
    have h58 : readings t 58 = l.totals := hs.left
    have h59 : readings t 59 = l.chosen := hs.right
    have h60 : readings t 60 = 1 := hs.one
    have h61 : readings t 61 = V := hs.value
    have hm : readings mt = mem := hs.kept.1
    apply readTest _ t mt _ _ (by decide)
    · change (Code.block [.binary .add 62 58 56, .load 62 62, minGuard.relaxReject,
        .binary .add 56 56 60]).safeReadOnly _ _ _ _
      simp (config := {decide := true}) [Code.block,Code.safeReadOnly,Code.evalNat_relaxReject,
        minGuard_eval,minGuard_fit,Code.evalNat,addressOp,addressOpFits,h56,h58,h60,a,inc]
    · simp (config := {decide := true}) [minBody,Code.block,minGuard_safe,Code.safeReadOnly,minGuard_eval,
        Code.evalNat,addressOp,addressOpFits,h56,h58,h59,h60,h61,hm,a,inc,good]
    · refine ⟨keptEval _ _ (by decide) hs.kept,?_,?_,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [minBody,Code.block,minGuard_eval,Code.evalNat,addressOp,
          h56,h58,h59,h60,h61]
      exact hs.limit
  have init := setup (mac := mac) false s m fit
  have tail (t : Bank w) (mt : Memory w)
      (hs : ScanState (readings s) mem l.coordinates l.totals l.chosen 0 0 (.ofWords t mt)) :
      TestRun pub mac (.ifLt 59 57 (.seq pivot (.whileLt 56 57 minBody)) .reject) t mt
        (pivot.slots+l.coordinates*(minBody.slots+1)+2)
        (Least l mem) (Kept (readings s) mem) := by
    have guard : t 59 < t 57 ↔ l.chosen < l.coordinates := by
      change readings t 59 < readings t 57 ↔ _
      rw [show readings t 59 = l.chosen from hs.right, show readings t 57 = l.coordinates from hs.limit]
    have next (valid : t 59 < t 57) :
        TestRun pub mac (.seq pivot (.whileLt 56 57 minBody)) t mt
          (pivot.slots + (l.coordinates*(minBody.slots+1)+1)) (∀ j < l.coordinates, good j)
          (Kept (readings s) mem) := by
      have range := guard.mp valid
      have a : l.totals+l.chosen < 2^w := by have := fit.totals; change l.totals+l.coordinates ≤ _ at this; omega
      have h58 : readings t 58 = l.totals := hs.left
      have h59 : readings t 59 = l.chosen := hs.right
      have hm : readings mt = mem := hs.kept.1
      have loadPivot : TestRun pub mac pivot t mt pivot.slots True (I 0) := by
        apply readTest _ t mt _ _ (by decide)
        · change pivot.safeReadOnly _ _ _ _
          simp [pivot,Code.block,Code.safeReadOnly,addressOpFits,h58,h59,a]
        · simp [pivot,Code.block,Code.safeReadOnly,addressOpFits,h58,h59,a]
        · refine ⟨keptEval _ _ (by decide) hs.kept,?_,?_,?_,?_,?_,?_⟩ <;>
            simp (config := {decide := true}) [pivot,Code.block,Code.evalNat,addressOp,h58,h59,hm,V] <;>
              first | exact hs.cursor | exact hs.limit | exact hs.one
      apply (loadPivot.seq fun z mz hz => test_counted_loop 56 57 minBody l.coordinates
          (fun _ => minBody.slots) good I (fun _ _ hz => ⟨hz.cursor,hz.limit⟩) step 0 (Nat.zero_le _)
          z mz hz).mono
      · simp
      · simp
      · exact fun _ hz => hz.kept
    exact (ifLtReject next).mono (by omega) (by rw [guard]; rfl) (fun _ hz => hz)
  apply (init.seq tail).mono (by simp [l,p,mem,Nat.add_assoc]) (by simp [l,p,mem]) (fun _ hz => hz)

/-- The fixed code returns exactly on matching row declarations and a correctly
tie-broken minimizing coordinate. Its cost is linear in the two scan lengths. -/
theorem check_run (s : Bank w) (m : Memory w) (fit : Fits w (readings pub) (readings m)) :
    let l := layout (readings pub) (readings m)
    TestRun pub mac check s m
      (rowSetup.slots + l.entries*(rowBody.slots+1)+1 +
       (minSetup.slots+pivot.slots+l.coordinates*(minBody.slots+1)+2))
      (RowsAgree l (readings m) ∧ Least l (readings m)) (Kept (readings s) (readings m)) := by
  have rowsPass := rows_run (mac := mac) s m fit
  apply rowsPass.seq
  intro t mt kept
  have hm : readings mt = readings m := kept.1
  have room : Fits w (readings pub) (readings mt) := hm ▸ fit
  have run := minimum_run (mac := mac) t mt room
  apply run.mono (by simp only [hm]; rfl) (by simp only [hm]) ?_
  intro z hz
  exact ⟨hz.1.trans hm,fun j hj => (hz.2 j hj).trans (kept.2 j hj)⟩

end RoutingISA.CubeLengths

end BorderVNP
end Computability
end OAI
