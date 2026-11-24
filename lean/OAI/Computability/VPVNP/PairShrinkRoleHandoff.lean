import OAI.Computability.VPVNP.PairNodeChildLoop
import OAI.Computability.VPVNP.PairSimulationInlineLiteral
import OAI.Computability.VPVNP.PairSimulationLeafScalarStartup

/-!
# Hosted operand handoffs from the traversal-level locator

The child header reader needs the popped node and the old level's directory
fields. Shrink and refresh share this two-copy entry sequence. The hidden
shrink-field reader additionally needs the selected owner and the private
buffer in which it stores absorbed fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM BurstRAM.PrivateRAM NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r : ℕ}

/-- Copy the located node and its old-level field pointer to the child reader. -/
def childHandoff (pc : Fin 2 → Fin p) (loc : Fin 14 ↪ Fin r) (child : Fin 16 ↪ Fin r)
    (next : Fin p) : Fin 2 → Instr w p r 11 :=
  ![.copy (child 7) (loc 0) (pc 1), .copy (child 8) (loc 12) next]

theorem resize_childHandoff (pc : Fin 2 → Fin p) (loc : Fin 14 ↪ Fin r) (child : Fin 16 ↪ Fin r)
    (next : Fin p) (i : Fin 2) :
    (childHandoff (w := 5) pc loc child next i).resize w = childHandoff pc loc child next i := by
  fin_cases i <;> rfl

/-- Only the two named child registers change. -/
theorem childHandoff_run {M : Machine w p r 11} {pc : Fin 2 → Fin p} {loc : Fin 14 ↪ Fin r}
    {child : Fin 16 ↪ Fin r} {next : Fin p}
    (linked : ∀ i, M.code (pc i) = childHandoff pc loc child next i)
    (apart : child 7 ≠ loc 12) (c : Config w p r) (hc : c.pc = pc 0) (m : Memory w) :
    ∃ out, Prefix M m c out [] (List.replicate 2 .tick) ∧ out.pc = next ∧
      out.reg (child 7) = c.reg (loc 0) ∧ out.reg (child 8) = c.reg (loc 12) ∧
      (∀ j, j ≠ child 7 → j ≠ child 8 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let a := c.put (pc 1) (child 7) (c.reg (loc 0))
  let out := a.put next (child 8) (c.reg (loc 12))
  have s₀ : M.program.step c = .localStep a := by
    change (M.code c.pc).run _ _ = _
    rw [hc, linked]
    rfl
  have s₁ : M.program.step a = .localStep out := by
    change (M.code (pc 1)).run _ _ = _
    rw [linked]
    change CallAction.localStep (a.put next (child 8) (a.reg (loc 12))) = _
    simp [a, out, Config.put, Function.update_of_ne apart.symm]
  have path : ReadPrefix M m c (List.replicate 2 .tick) out :=
    ReadPrefix.tick s₀ (ReadPrefix.tick s₁ (ReadPrefix.nil _))
  exact ⟨out, ReadPrefix.execute path, rfl,
    by simp [out, a, Config.put], by simp [out, Config.put],
    fun j h7 h8 => by simp [out, a, Config.put, Function.update_of_ne h7, Function.update_of_ne h8],
    rfl, rfl⟩

set_option synthInstance.maxSize 10000

@[irreducible] private noncomputable def scalarPorts : ℕ := Fintype.card LeafStartup.ScalarPort

/-- The cache holds 38 words. Each of the scalar stacks following it
occupies a private interval of capacity `n^40`. -/
noncomputable def hiddenBaseWord (cache n : Word w) : Word w :=
  cache + 38 + (scalarPorts : Word w) * n^40

theorem hiddenBaseWord_cast (cache n : ℕ) :
    hiddenBaseWord (cache : Word w) (n : Word w) =
      ((cache + 38 + Fintype.card LeafStartup.ScalarPort * n^40 : ℕ) : Word w) := by
  have cast (t : ℕ) : (cache : Word w) + 38 + (t : Word w) * (n : Word w)^40 =
      ((cache + 38 + t * n^40 : ℕ) : Word w) := by push_cast; rfl
  unfold hiddenBaseWord scalarPorts
  exact cast _

/-- One geometry-pointer load, the existing fixed literal block for the
number of scalar stacks, and twenty private reads, copies and arithmetic rows. -/
noncomputable abbrev hiddenCount : ℕ := (scalarPorts + 2 + 20) + 1

theorem hiddenCount_eq : hiddenCount = Fintype.card LeafStartup.ScalarPort + 23 := by
  unfold hiddenCount scalarPorts
  rfl

instance : NeZero hiddenCount := ⟨Nat.succ_ne_zero (scalarPorts + 2 + 20)⟩

private def hiddenTailPC {C : ℕ} (pc : Fin ((C + 2 + 20) + 1) → Fin p) (i : Fin 20) :=
  pc ((i.natAdd (C + 2)).succ)

private def hiddenLiteralPC {C : ℕ} (pc : Fin ((C + 2 + 20) + 1) → Fin p) : Fin (C + 3) → Fin p :=
  Fin.lastCases (hiddenTailPC pc 0) (fun i => pc (i.castAdd 20).succ)

private def hiddenTail (pc : Fin 20 → Fin p) (loc : Fin 14 ↪ Fin r) (i : Fin 6 ↪ Fin r)
    (next : Fin p) : Fin 20 → Instr w p r 11 :=
  ![.constant (i 5) 9 (pc 1),
    .binary .add (i 2) (i 1) (i 5) (pc 2),
    .loadPrivate (i 2) (i 2) (pc 3),
    .binary .mul (i 5) (i 2) (i 2) (pc 4),
    .binary .mul (i 5) (i 5) (i 5) (pc 5),
    .binary .mul (i 5) (i 5) (i 2) (pc 6),
    .binary .mul (i 5) (i 5) (i 5) (pc 7),
    .binary .mul (i 5) (i 5) (i 5) (pc 8),
    .binary .mul (i 5) (i 5) (i 5) (pc 9),
    .binary .mul (i 0) (i 0) (i 5) (pc 10),
    .binary .mul (i 2) (i 2) (i 2) (pc 11),
    .constant (i 5) 8 (pc 12),
    .binary .add (i 1) (i 1) (i 5) (pc 13),
    .loadPrivate (i 1) (i 1) (pc 14),
    .constant (i 5) 19 (pc 15),
    .binary .add (i 5) (i 5) (i 5) (pc 16),
    .binary .add (i 1) (i 1) (i 5) (pc 17),
    .binary .add (i 1) (i 1) (i 0) (pc 18),
    .copy (i 0) (loc 7) (pc 19),
    .copy (i 5) (loc 11) next]

/-- Read the geometry pointer first, even if the caller's pointer register
overlaps a destination. Synthesize the scalar-port count using the shared
zero-and-one literal routine before computing the first transient address. -/
noncomputable def hiddenHandoff (pc : Fin hiddenCount → Fin p) (loc : Fin 14 ↪ Fin r)
    (inputs : Fin 6 ↪ Fin r) (stackEnd : Fin r) (next : Fin p) : Fin hiddenCount → Instr w p r 11 :=
  Fin.cases (n := scalarPorts + 2 + 20)
    (.loadPrivate (inputs 1) stackEnd (hiddenLiteralPC (C := scalarPorts) pc 0))
    (Fin.addCases (m := scalarPorts + 2) (n := 20) (motive := fun _ => Instr w p r 11)
      (InlinePublic.literalInstruction w scalarPorts scalarPorts
        (hiddenLiteralPC (C := scalarPorts) pc) (inputs 5) (inputs 0))
      (hiddenTail (hiddenTailPC (C := scalarPorts) pc) loc inputs next))

theorem resize_hiddenHandoff (pc : Fin hiddenCount → Fin p) (loc : Fin 14 ↪ Fin r)
    (inputs : Fin 6 ↪ Fin r) (stackEnd : Fin r) (next : Fin p) (i : Fin hiddenCount) :
    (hiddenHandoff (w := 5) pc loc inputs stackEnd next i).resize w =
      hiddenHandoff pc loc inputs stackEnd next i := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.addCases (m := scalarPorts + 2) (n := 20) (fun k => ?_) (fun k => ?_) j
  · simp only [hiddenHandoff, Fin.cases_succ, Fin.addCases_left, InlinePublic.literalInstruction]
    split_ifs <;> rfl
  · simp only [hiddenHandoff, Fin.cases_succ, Fin.addCases_right]
    fin_cases k <;> rfl

set_option maxHeartbeats 2000000 in
-- Simplifying the twenty register updates expands a nested bank of word operations.
private theorem hiddenTail_run {M : Machine w p r 11} {pc : Fin 20 → Fin p}
    {loc : Fin 14 ↪ Fin r} {inputs : Fin 6 ↪ Fin r} {next : Fin p}
    (linked : ∀ i, M.code (pc i) = hiddenTail pc loc inputs next i)
    (apart : ∀ i j, inputs i ≠ loc j) (c : Config w p r) (hc : c.pc = pc 0)
    (C : ℕ) (ports : c.reg (inputs 0) = (C : Word w)) :
    let G := c.reg (inputs 1)
    let n := c.privateMem (G + 9)
    let cache := c.privateMem (G + 8)
    ∃ out, PrimedCounter.GuessWord.Prefix M c (List.replicate 20 .tick) out ∧ out.pc = next ∧
      out.reg (inputs 0) = c.reg (loc 7) ∧ out.reg (inputs 1) = cache + 38 + (C : Word w) * n^40 ∧
      out.reg (inputs 2) = n*n ∧ out.reg (inputs 5) = c.reg (loc 11) ∧
      (∀ j, j ≠ inputs 0 → j ≠ inputs 1 → j ≠ inputs 2 → j ≠ inputs 5 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  intro G n cache
  let c1 := c.put (pc 1) (inputs 5) (9)
  let c2 := c1.put (pc 2) (inputs 2) (G + 9)
  let c3 := c2.put (pc 3) (inputs 2) (n)
  let c4 := c3.put (pc 4) (inputs 5) (n^2)
  let c5 := c4.put (pc 5) (inputs 5) (n^4)
  let c6 := c5.put (pc 6) (inputs 5) (n^5)
  let c7 := c6.put (pc 7) (inputs 5) (n^10)
  let c8 := c7.put (pc 8) (inputs 5) (n^20)
  let c9 := c8.put (pc 9) (inputs 5) (n^40)
  let c10 := c9.put (pc 10) (inputs 0) ((C : Word w) * n^40)
  let c11 := c10.put (pc 11) (inputs 2) (n*n)
  let c12 := c11.put (pc 12) (inputs 5) (8)
  let c13 := c12.put (pc 13) (inputs 1) (G+8)
  let c14 := c13.put (pc 14) (inputs 1) (cache)
  let c15 := c14.put (pc 15) (inputs 5) (19)
  let c16 := c15.put (pc 16) (inputs 5) (38)
  let c17 := c16.put (pc 17) (inputs 1) (cache+38)
  let c18 := c17.put (pc 18) (inputs 1) (cache+38+(C : Word w)*n^40)
  let c19 := c18.put (pc 19) (inputs 0) (c.reg (loc 7))
  let c20 := c19.put next (inputs 5) (c.reg (loc 11))
  have step (i : Fin 20) (d : Config w p r) (hd : d.pc = pc i) {act}
      (row : (hiddenTail pc loc inputs next i).run M.publicData d = act) :
      M.program.step d = act := by
    change (M.code d.pc).run _ _ = _
    rw [hd, linked]
    exact row
  have path : PrimedCounter.GuessWord.Prefix M c (List.replicate 20 .tick) c20 := by
    refine .tick (next := c1) (step 0 c hc ?_) <|
       .tick (next := c2) (step 1 c1 rfl ?_) <|
       .tick (next := c3) (step 2 c2 rfl ?_) <|
       .tick (next := c4) (step 3 c3 rfl ?_) <|
       .tick (next := c5) (step 4 c4 rfl ?_) <|
       .tick (next := c6) (step 5 c5 rfl ?_) <|
       .tick (next := c7) (step 6 c6 rfl ?_) <|
       .tick (next := c8) (step 7 c7 rfl ?_) <|
       .tick (next := c9) (step 8 c8 rfl ?_) <|
       .tick (next := c10) (step 9 c9 rfl ?_) <|
       .tick (next := c11) (step 10 c10 rfl ?_) <|
       .tick (next := c12) (step 11 c11 rfl ?_) <|
       .tick (next := c13) (step 12 c12 rfl ?_) <|
       .tick (next := c14) (step 13 c13 rfl ?_) <|
       .tick (next := c15) (step 14 c14 rfl ?_) <|
       .tick (next := c16) (step 15 c15 rfl ?_) <|
       .tick (next := c17) (step 16 c16 rfl ?_) <|
       .tick (next := c18) (step 17 c17 rfl ?_) <|
       .tick (next := c19) (step 18 c18 rfl ?_) <|
       .tick (next := c20) (step 19 c19 rfl ?_) <|
      .nil _
    all_goals simp (config := { zetaDelta := true, decide := true })
      [hiddenTail, Instr.run, Config.put, BinaryOp.eval, Function.update_of_ne (apart _ _).symm,
        ports]
    all_goals congr 2 <;> ring
  refine ⟨c20, path, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals first | intro j h0 h1 h2 h5 | skip
  all_goals simp (config := { zetaDelta := true, decide := true })
    [Config.put, Function.update_of_ne, *]

/-- The owner and old level come from the locator. The hidden-field array
starts immediately above the geometry's operand cache and all leaf scalar
stacks, and its individual slots have stride `n*n`. -/
theorem hiddenHandoff_run {M : Machine w p r 11} {pc : Fin hiddenCount → Fin p}
    {loc : Fin 14 ↪ Fin r} {inputs : Fin 6 ↪ Fin r} {stackEnd : Fin r} {next : Fin p}
    (linked : ∀ i, M.code (pc i) = hiddenHandoff pc loc inputs stackEnd next i)
    (apart : ∀ i j, inputs i ≠ loc j) (c : Config w p r) (hc : c.pc = pc 0) (m : Memory w) :
    let G := c.privateMem (c.reg stackEnd)
    let n := c.privateMem (G + 9)
    ∃ out, Prefix M m c out [] (List.replicate hiddenCount .tick) ∧ out.pc = next ∧
      out.reg (inputs 0) = c.reg (loc 7) ∧
      out.reg (inputs 1) = hiddenBaseWord (c.privateMem (G + 8)) n ∧
      out.reg (inputs 2) = n * n ∧ out.reg (inputs 5) = c.reg (loc 11) ∧
      (∀ j, j ≠ inputs 0 → j ≠ inputs 1 → j ≠ inputs 2 → j ≠ inputs 5 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  intro G n
  let a := c.put (hiddenLiteralPC (C := scalarPorts) pc 0) (inputs 1) G
  have first : M.program.step c = .localStep a := by
    change (M.code c.pc).run _ _ = _
    rw [hc, linked]
    rfl
  have lit (i : Fin (scalarPorts + 2)) : M.code (hiddenLiteralPC (C := scalarPorts) pc i.castSucc) =
      InlinePublic.literalInstruction w scalarPorts scalarPorts
        (hiddenLiteralPC (C := scalarPorts) pc) (inputs 5) (inputs 0) i := by
    simp only [hiddenLiteralPC, Fin.lastCases_castSucc]
    rw [linked]
    simp only [hiddenHandoff, Fin.cases_succ, Fin.addCases_left, hiddenLiteralPC]
  obtain ⟨mid, litPath, atEnd, ports, keep, mem, pers⟩ :=
    InlinePublic.literal_prefix (inputs.injective.ne (by decide)) le_rfl lit a rfl
  simp only [hiddenLiteralPC, Fin.lastCases_last] at atEnd
  have tail (i : Fin 20) : M.code (hiddenTailPC (C := scalarPorts) pc i) =
      hiddenTail (hiddenTailPC (C := scalarPorts) pc) loc inputs next i := by
    simp only [hiddenTailPC]
    rw [linked]
    simp only [hiddenHandoff, Fin.cases_succ, Fin.addCases_right]
  obtain ⟨out, tailPath, done, owner, base, stride, level, keepTail, tailMem, tailPers⟩ :=
    hiddenTail_run tail apart mid atEnd scalarPorts ports
  have trace := (PrimedCounter.GuessWord.Prefix.tick first litPath).append tailPath
  have path : PrimedCounter.GuessWord.Prefix M c (List.replicate hiddenCount .tick) out := by
    simpa only [← List.replicate_succ, ← List.replicate_add, hiddenCount, Nat.succ_add] using trace
  have quiet (k : ℕ) : choiceBits (List.replicate k (.tick : Event w)) = [] := by
    induction k with | zero => rfl | succ k ih => simpa [List.replicate_succ, choiceBits] using ih
  have geom : mid.reg (inputs 1) = G := by
    rw [keep _ (inputs.injective.ne (by decide)) (inputs.injective.ne (by decide))]
    simp [a]
  have located (j : Fin 14) : mid.reg (loc j) = c.reg (loc j) := by
    rw [keep _ (apart _ _).symm (apart _ _).symm]
    simp [a, Config.put, Function.update_of_ne (apart _ _).symm]
  have hm : mid.privateMem = c.privateMem := mem
  refine ⟨out, fun f bs => by simpa only [quiet] using path.execute f m bs, done,
    owner.trans (located 7), ?_, ?_, level.trans (located 11), ?_, tailMem.trans hm,
    tailPers.trans pers⟩
  · simpa only [hiddenBaseWord, geom, hm] using base
  · simpa only [geom, hm] using stride
  · intro j h0 h1 h2 h5
    rw [keepTail _ h0 h1 h2 h5, keep _ h5 h0]
    exact Function.update_of_ne h1 ..

/-- Save the hidden-field base in locator register eight for the map that
follows the absorbed-field scan. The extra copy takes exactly one tick. -/
theorem cachedHiddenHandoff_run {M : Machine w p r 11} {pc : Fin (hiddenCount + 1) → Fin p}
    {loc : Fin 14 ↪ Fin r} {inputs : Fin 6 ↪ Fin r} {stackEnd : Fin r} {next : Fin p}
    (linked : ∀ i, M.code (pc i.castSucc) =
      hiddenHandoff (pc ∘ Fin.castSucc) loc inputs stackEnd (pc (Fin.last hiddenCount)) i)
    (cacheRow : M.code (pc (Fin.last hiddenCount)) = .copy (loc 8) (inputs 1) next)
    (apart : ∀ i j, inputs i ≠ loc j) (c : Config w p r) (hc : c.pc = pc 0) (m : Memory w) :
    let G := c.privateMem (c.reg stackEnd)
    let n := c.privateMem (G + 9)
    ∃ out, Prefix M m c out [] (List.replicate (hiddenCount + 1) .tick) ∧ out.pc = next ∧
      out.reg (inputs 0) = c.reg (loc 7) ∧
      out.reg (inputs 1) = hiddenBaseWord (c.privateMem (G + 8)) n ∧
      out.reg (inputs 2) = n * n ∧ out.reg (inputs 5) = c.reg (loc 11) ∧
      out.reg (loc 8) = out.reg (inputs 1) ∧
      (∀ j, j ≠ loc 8 → j ≠ inputs 0 → j ≠ inputs 1 → j ≠ inputs 2 → j ≠ inputs 5 →
        out.reg j = c.reg j) ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  intro G n
  obtain ⟨mid, first, atCopy, owner, base, stride, level, frame, mem, pers⟩ :=
    hiddenHandoff_run (pc := pc ∘ Fin.castSucc) linked apart c hc m
  let out := mid.put next (loc 8) (mid.reg (inputs 1))
  have step : M.program.step mid = .localStep out := by
    change (M.code mid.pc).run _ _ = _
    rw [atCopy, cacheRow]
    rfl
  have last : Prefix M m mid out [] [.tick] :=
    ReadPrefix.execute (ReadPrefix.tick step (ReadPrefix.nil _))
  have keep (j : Fin r) (h : j ≠ loc 8) : out.reg j = mid.reg j := Function.update_of_ne h ..
  refine ⟨out, ?_, rfl, (keep _ (apart 0 8)).trans owner, (keep _ (apart 1 8)).trans base,
    (keep _ (apart 2 8)).trans stride, (keep _ (apart 5 8)).trans level, ?_,
    fun j h8 h0 h1 h2 h5 => (keep j h8).trans (frame j h0 h1 h2 h5), mem, pers⟩
  · simpa only [List.nil_append, List.replicate_succ'] using first.trans last
  · exact (Config.put_same ..).trans (keep _ (apart 1 8)).symm

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
