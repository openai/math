import OAI.Computability.BorderVNP.CubeISAHeaderDecodeModel

/-! # Exact native upper-field and padding iterations of the public declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderDecode

open VPVNP.BurstRAM Cube.DeclarationBits Cube.SelectorRead Finset

private def core (j : Reg) : Prop := j=20 ∨ j=21 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=29 ∨
  j=30 ∨ j=31 ∨ j=32 ∨ j=33 ∨ j=34

private theorem staticKeep {l : Layout} {r t : Reg → ℕ} (old : Static l r)
    (keep : ∀ j, core j → t j = r j) : Static l t := by
  obtain ⟨a,b,c,d,e,f,g,h,i,k,p⟩ := old
  exact ⟨(keep 20 (by simp [core])).trans a,(keep 21 (by simp [core])).trans b,
    (keep 22 (by simp [core])).trans c,(keep 25 (by simp [core])).trans d,
    (keep 28 (by simp [core])).trans e,(keep 29 (by simp [core])).trans f,
    (keep 30 (by simp [core])).trans g,(keep 31 (by simp [core])).trans h,
    (keep 32 (by simp [core])).trans i,(keep 33 (by simp [core])).trans k,
    (keep 34 (by simp [core])).trans p⟩

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Registers ready to store the next dense value; the compact cursor already
points at the following actual field. -/
private structure WriteState (l : Layout) (old : ℕ → ℕ) (k : ℕ) (z : NatState) : Prop where
  fixed : Static l z.reg
  cursor : z.reg 23 = k
  compact : z.reg 24 = l.start (k+1)
  bits : z.reg 41 = l.rw
  bound : z.reg 42 = l.cap+1
  value : z.reg 43 = l.value old k
  memory : z.mem = l.image old k

private theorem classify_run (l : Layout) (old : ℕ → ℕ) (k : ℕ) (s : Bank w) (m : Memory w)
    (room : Fits l w) (hk : k < l.entries) (hs : State l old k (.ofWords s m)) :
    BoundedRun pub mac classify s m classify.slots (fun z => State l old k z ∧
      z.reg 36 = k/l.a/l.d ∧ z.reg 37 = k/l.a%l.d) := by
  have hd : 0 < l.d := by
    by_contra! zero
    have eq : l.d = 0 := by omega
    simp [Layout.entries,eq] at hk
  have c : readings s 23 = k := hs.cursor
  have a : readings s 32 = l.a := hs.fixed.a
  have d : readings s 28 = l.d := hs.fixed.d
  have safe : classify.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [classify,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,
      a,d,hd,room.dimension]
  obtain ⟨es,t,r,cost,eq⟩ := classify.runReadOnly pub mac m s safe
  have keep (j : Reg) (ne : j ≠ 35 ∧ j ≠ 36 ∧ j ≠ 37) : readings t j = readings s j := by
    simpa [classify,Code.block,Code.evalNat,ne.1,ne.2.1,ne.2.2] using congrFun eq j
  have low (j : Reg) (h : core j) : readings t j = readings s j := by
    apply keep
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨es,t,m,r,cost,⟨staticKeep hs.fixed low,(keep 23 (by decide)).trans hs.cursor,
    (keep 24 (by decide)).trans hs.compact,(keep 41 (by decide)).trans hs.bits,
    (keep 42 (by decide)).trans hs.bound,hs.memory⟩,?_,?_⟩
  · simpa (config := {decide := true}) [classify,Code.block,Code.evalNat,addressOp,a,d,c,NatState.ofWords] using congrFun eq 36
  · simpa (config := {decide := true}) [classify,Code.block,Code.evalNat,addressOp,a,d,c,NatState.ofWords] using congrFun eq 37

private theorem write_run (l : Layout) (old : ℕ → ℕ) (k : ℕ) (s : Bank w) (m : Memory w)
    (room : Fits l w) (hk : k < l.entries) (hs : WriteState l old k (.ofWords s m)) :
    BoundedRun pub mac writeValue s m writeValue.slots (State l old (k+1)) := by
  let z := NatState.ofWords s m
  have h23 : z.reg 23 = k := hs.cursor
  have h30 : z.reg 30 = l.dense := hs.fixed.dense
  have h25 : z.reg 25 = 1 := hs.fixed.one
  have a : l.dense+k < 2^w := by have := room.denseEnd; omega
  have i : k+1 < 2^w := by have := room.count; omega
  have safe : writeValue.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [writeValue,Code.block,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,Code.evalNat,
      addressOpFits,h23,h25,h30,i,a]
  apply (writeValue.runFixed pub mac s m safe).mono le_rfl
  intro t ht
  rw [ht]
  change State l old (k+1) (writeValue.fixedEval (readings pub) z)
  have kept (j : Reg) (hj : j ≠ 23 ∧ j ≠ 27) : (writeValue.fixedEval (readings pub) z).reg j = z.reg j := by
    simp [writeValue,Code.block,Code.fixedEval,Code.evalNat,hj.1,hj.2]
  have low (j : Reg) (hj : core j) := kept j (by rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have h43 : z.reg 43 = l.value old k := hs.value
  have hm : z.mem = l.image old k := hs.memory
  refine ⟨staticKeep hs.fixed low,?_,(kept 24 (by decide)).trans hs.compact,
    (kept 41 (by decide)).trans hs.bits,(kept 42 (by decide)).trans hs.bound,?_⟩
  · simp (config := {decide := true}) [writeValue,Code.block,Code.fixedEval,Code.evalNat,addressOp,h23,h25]
  · simp (config := {decide := true}) [writeValue,Code.block,Code.fixedEval,Code.evalNat,addressOp,h23,h30,h43,hm,l.image_step]

private theorem branch {x y : Reg} {yes no : Code} {s : Bank w} {m : Memory w} {T : ℕ} {ok : Prop} {P : NatState → Prop}
    (checked : TestRun pub mac (if s x < s y then yes else no) s m T ok P) :
    TestRun pub mac (.ifLt x y yes no) s m (T+1) ok P := by
  refine ⟨fun good => ?_,?_⟩
  · obtain ⟨es,t,mt,r,cost,post⟩ := checked.complete good
    exact ⟨_,t,mt,.ifLt r,show 1+traceCost es ≤ T+1 by omega,post⟩
  · intro es t mt r
    cases r with
    | atom atomic _ _ => cases atomic
    | ifLt sub => exact checked.sound sub

/-- A uniform physical allowance for one dense entry. It bounds both a zero
write to a padding row and a genuine binary field read. -/
def entryCost (rw : ℕ) := classify.slots + (Cube.SelectorRead.init.slots+rw*(Cube.SelectorRead.step.slots+1)+
  1+(requireLt 43 42).slots+1+1) + writeValue.slots

private theorem choose_run (l : Layout) (old : ℕ → ℕ) (k : ℕ) (s : Bank w) (m : Memory w)
    (room : Fits l w) (hk : k < l.entries) (hs : State l old k (.ofWords s m))
    (low : readings s 36 = k/l.a/l.d) (high : readings s 37 = k/l.a%l.d) :
    TestRun pub mac fieldValue s m
      (Cube.SelectorRead.init.slots+l.rw*(Cube.SelectorRead.step.slots+1)+1+(requireLt 43 42).slots+1+1)
      (upper l.d l.a k → Cube.SelectorRead.Valid old (l.start k) l.rw (l.cap+1)) (WriteState l old k) := by
  let readCost := Cube.SelectorRead.init.slots+l.rw*(Cube.SelectorRead.step.slots+1)+1+(requireLt 43 42).slots
  have cond : s 37 < s 36 ↔ ¬upper l.d l.a k := by
    change readings s 37 < readings s 36 ↔ ¬_ ≤ _
    rw [high,low]; omega
  change TestRun pub mac (.ifLt 37 36 (.constant 43 0) (.seq reader (.binary .add 24 24 21))) s m
    (readCost+1+1) _ _
  apply branch
  by_cases h : upper l.d l.a k
  · rw [ite_eq_right (fun g => cond.mp g h)]
    have lo : l.source ≤ l.start k := by dsimp [Layout.start,fieldStart]; omega
    have finish : l.start k+l.rw ≤ l.start l.entries := by
      simpa only [l.start_succ k,ite_eq_left h] using l.start_mono (show k+1 ≤ l.entries from hk)
    have roomRead : l.start k+l.rw ≤ 2^w := finish.trans room.stream.le
    have hm : readings m = l.image old k := hs.memory
    have same (j : ℕ) (hj : j < l.rw) : readings m (l.start k+j) = old (l.start k+j) := by
      rw [hm]
      apply room.input old hk.le <;> omega
    have ⟨value,valid⟩ := decoded_congr (readings m) old (l.start k) l.rw (l.cap+1) same
    have rd := reader_run (pub := pub) (mac := mac) s m (l.start k) l.rw (l.cap+1)
      hs.compact hs.bits hs.bound room.small room.rowWidth roomRead
    have bump (t : Bank w) (mt : Memory w) (hr : (NatState.ofWords t mt).mem = readings m ∧
        (NatState.ofWords t mt).reg 43 = (decoded (readings m) (l.start k) l.rw).val ∧
        ∀ j, ¬Scratch j → (NatState.ofWords t mt).reg j = readings s j) :
        TestRun pub mac (.binary .add 24 24 21) t mt 1 True (WriteState l old k) := by
      have keep (j : Reg) (hj : ¬Scratch j) : readings t j = readings s j := hr.2.2 j hj
      have ht24 : readings t 24 = l.start k := (keep 24 (by simp [Scratch])).trans hs.compact
      have ht21 : readings t 21 = l.rw := (keep 21 (by simp [Scratch])).trans hs.fixed.rw
      let c := Code.binary .add 24 24 21
      have safe : c.safeReadOnly w (readings pub) (readings mt) (readings t) := by
        change readings t 24 + readings t 21 < 2^w; rw [ht24,ht21]; exact finish.trans_lt room.stream
      obtain ⟨es,u,r,cost,eq⟩ := c.runReadOnly pub mac mt t safe
      have untouched (j : Reg) (hj : j ≠ 24) : readings u j = readings t j := by simpa [c,Code.evalNat,hj] using congrFun eq j
      have stable (j : Reg) (hj : core j) : readings u j = readings s j := by
        rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          exact (untouched _ (by decide)).trans (keep _ (by simp [Scratch]))
      have hs43 : readings t 43 = (decoded old (l.start k) l.rw).val := hr.2.1.trans (congrArg Fin.val value)
      have run : BoundedRun pub mac c t mt 1 (WriteState l old k) := by
        refine ⟨es,u,mt,r,cost,staticKeep hs.fixed stable,
          (untouched 23 (by decide)).trans ((keep 23 (by simp [Scratch])).trans hs.cursor),?_,
          (untouched 41 (by decide)).trans ((keep 41 (by simp [Scratch])).trans hs.bits),
          (untouched 42 (by decide)).trans ((keep 42 (by simp [Scratch])).trans hs.bound),?_,hr.1.trans hm⟩
        · simpa [NatState.ofWords,c,Code.evalNat,addressOp,ht24,ht21,l.start_succ,h] using congrFun eq 24
        · simpa only [Layout.value,ite_eq_left h,NatState.ofWords] using (untouched 43 (by decide)).trans hs43
      exact run.asTest rfl
    apply (rd.seq bump).mono le_rfl ?_ (fun _ hp => hp)
    simp only [and_true,h,true_implies,valid]
  · rw [ite_eq_left (cond.mpr h)]
    let c := Code.constant 43 0
    obtain ⟨es,t,r,cost,eq⟩ := c.runReadOnly pub mac m s (show (0 : Word 8).val < 2^w from Nat.two_pow_pos _)
    have keep (j : Reg) (hj : j ≠ 43) : readings t j = readings s j := by simpa [c,Code.evalNat,hj] using congrFun eq j
    have core' (j : Reg) (hj : core j) : readings t j = readings s j := by
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact keep _ (by decide)
    have run : BoundedRun pub mac c s m 1 (WriteState l old k) := by
      refine ⟨es,t,m,r,cost,staticKeep hs.fixed core',(keep 23 (by decide)).trans hs.cursor,
        ?_,(keep 41 (by decide)).trans hs.bits,(keep 42 (by decide)).trans hs.bound,?_,hs.memory⟩
      · simpa only [l.start_succ k,ite_eq_right h,Nat.add_zero,NatState.ofWords] using (keep 24 (by decide)).trans hs.compact
      · simpa [c,Code.evalNat,Layout.value,h,NatState.ofWords] using congrFun eq 43
    exact (run.asTest rfl).mono (by omega) (by simp [h]) (fun _ hp => hp)

/-- Every returning dense iteration consumes exactly the prescribed input bits and
stores the prescribed value; malformed upper fields have no returning path. -/
theorem step_test (l : Layout) (old : ℕ → ℕ) (k : ℕ) (s : Bank w) (m : Memory w)
    (room : Fits l w) (hk : k < l.entries) (hs : State l old k (.ofWords s m)) :
    TestRun pub mac step s m (entryCost l.rw)
      (upper l.d l.a k → Cube.SelectorRead.Valid old (l.start k) l.rw (l.cap+1))
      (State l old (k+1)) := by
  have first := (classify_run (pub := pub) (mac := mac) l old k s m room hk hs).asTest (by decide)
  apply (first.seq fun t mt hp => (choose_run l old k t mt room hk hp.1 hp.2.1 hp.2.2).seq
    (fun u mu hz => (write_run l old k u mu room hk hz).asTest (by decide))).mono
  · simp [entryCost,Nat.add_assoc]
  · simp
  · exact fun _ hp => hp

end RoutingISA.HeaderDecode

end BorderVNP
end Computability
end OAI
