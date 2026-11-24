import OAI.Computability.VPVNP.CompressorDescriptorParameters

/-!
# Persistent cursor parameters from the pair ABI

The native parameter body reads the eight inputs prepared at workspace
offset nine. A seventeen-word loader starts at the workspace base, using
the last eight cached words for the body. The body publishes the eight
computed cursor fields at level zero, scalar offset six. A final native
copy restores the computed fields to the active frame for the stride pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorParameters

open BurstRAM BurstRAM.PrivateRAM CursorBounds DescriptorSpace PhaseRecipe
open CursorRAM.ParametersInit
open scoped Fin.CommRing

variable {w : ℕ}

private def sourceSlot (j : Fin 8) : Fin 17 := j.natAdd 9
private abbrev body := CursorRAM.ParametersInit.program.template (some 9)
private def padded := LiveStageLink.widen body (Function.Embedding.refl _) sourceSlot

/-- The loader uses workspace public slot two and the input bank at offset nine. -/
def loader := LiveStageLink.widen (Frame.compile padded) (Function.Embedding.refl _)
  (fun _ : Fin 1 ↦ (2 : Fin 11))

private theorem offset_bank (base : Word w) (m : Memory w) :
    (Frame.data base m : Fin 17 → Word w) ∘ sourceSlot = Frame.data (base+9) m := by
  funext j
  change m (base+((9+j.val : ℕ) : Word w)).val = m (base+9+(j.val : Word w)).val
  rw [Nat.cast_add, Nat.cast_ofNat, add_assoc]

private theorem execute_loader (pub : Fin 11 → Word w) (fuel : ℕ) (s : Word w) (m : Memory w) :
    let M := loader.instantiate w pub
    let Q := body.instantiate w (Frame.data (pub 2+9) m)
    execute M.program (fuel+4*17) (M.program.start s) m [] =
      (execute Q.program fuel (Q.program.start s) m []).map
        (LiveStageLink.prependLog (Frame.loadEvents (pub 2) m 0 17)) := by
  dsimp only
  rw [loader, LiveStageLink.execute_widen_start]
  change execute (Frame.machine padded (pub 2)).program (fuel+4*17)
    ((Frame.machine padded (pub 2)).program.start s) m [] = _
  rw [Frame.execute_frame padded (pub 2) s fuel m [], padded, LiveStageLink.execute_widen_start, offset_bank]

/-- The eight reserved scalar cells begin immediately after the six live level scalars. -/
def saved (L : Layout) (w : ℕ) : Word w := CursorRAM.encode w (levelStart L 0+6)

/-- The cursor parameters consumed by the scalar, stride and incidence passes. -/
noncomputable def outputs (L : Layout) (B n a l w : ℕ) : Fin 8 → Word w :=
  CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1)
    (virtualBits B n-l) l a (initialWidth B n) (incidenceStart L 0)

/-- The parameter-loader report, including its reads of the external frame, writes of the
computed operands and returned cursor. -/
noncomputable def loaderReport (L : Layout) (B n a l : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) : Report w :=
  LiveStageLink.prependLog (Frame.loadEvents (pub 2) m 0 17)
    ⟨events n (saved L w) (outputs L B n a l w), some (s+1)⟩

private theorem frame_native (pub : Fin 11 → Word w) (f : ℕ) (s : Word w) (m : Memory w)
    (rep : Report w) (run : let M := body.instantiate w (Frame.data (pub 2+9) m)
      execute M.program f (M.program.start s) m [] = some rep) :
    let M := loader.instantiate w pub
    execute M.program (f+4*17) (M.program.start s) m [] =
      some (LiveStageLink.prependLog (Frame.loadEvents (pub 2) m 0 17) rep) :=
  (execute_loader pub f s m).trans (congrArg (Option.map (LiveStageLink.prependLog (Frame.loadEvents (pub 2) m 0 17))) run)

private theorem frame_effect (base dest s : Word w) (n : ℕ) (m : Memory w) (fields : Fin 8 → Word w)
    (room : dest.val+8 ≤ 2^w) :
    let bodyR : Report w := ⟨events n dest fields,some (s+1)⟩
    let r := LiveStageLink.prependLog (Frame.loadEvents base m 0 17) bodyR
    let out := after m r.events
    r.result = some (s+1) ∧ Frame.data dest out = fields ∧
      (∀ addr, addr < dest.val ∨ dest.val+8 ≤ addr → out addr = m addr) ∧
      r.events.length = VirtualParameters.ticks n+110 ∧ r.probes = 25 ∧ choiceBits r.events = [] := by
  intro bodyR r out
  have effect := Frame.frame_cost base m 0 17 bodyR
  have afterBody : out = after m bodyR.events := effect.2.2.2.1
  have stored := frame_ready m n dest fields room
  have wk := work n dest fields
  refine ⟨rfl,(congrArg (Frame.data (k := 8) dest) afterBody).trans stored.1,
    fun addr ha ↦ (congrFun afterBody addr).trans (stored.2 addr ha), ?_, ?_, effect.2.2.1.trans wk.2.2⟩
  · have small : ∀ t : ℕ, 4*17+(t+42) = t+110 := fun t ↦ by omega
    exact effect.1.trans ((congrArg (4*17+·) wk.1).trans (small _))
  · exact effect.2.1.trans (congrArg (17+·) wk.2.1)

set_option maxHeartbeats 300000 in
/-- With the prepared bank in memory, the compiled pair-ABI call writes the
persistent bank, changes no other external word and uses 25 probes. -/
theorem publish {L B n a l} (hw : w = wordBits B n) (hB : 1 ≤ B) (hl : l ≤ virtualBits B n)
    (h : Capacity B n a l (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6))
    (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bank : Frame.data (pub 2+9) m = (fun i ↦ CursorRAM.encode w
      (inputValues n (addressBits B n) a l (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6) i))) :
    let M := loader.instantiate w pub
    let r := loaderReport L B n a l pub s m
    let out := after m r.events
    execute M.program (VirtualParameters.ticks n+43+4*17) (M.program.start s) m [] = some r ∧
      r.result = some (s+1) ∧ Frame.data (saved L w) out = outputs L B n a l w ∧
      (∀ addr, addr < levelStart L 0+6 ∨ levelStart L 0+14 ≤ addr → out addr = m addr) ∧
      r.events.length = VirtualParameters.ticks n+110 ∧ r.probes = 25 ∧ choiceBits r.events = [] := by
  intro M r out
  let p : Fin 8 → Word w := Frame.data (pub 2+9) m
  have pv (i : Fin 8) : (p i).val = inputValues n (addressBits B n) a l (directoryBase L) 1
      (incidenceStart L 0) (levelStart L 0+6) i :=
    (congrArg Fin.val (congrFun bank i)).trans (Nat.mod_eq_of_lt (hw ▸ h.public_lt i))
  have rowEq : p 4 = CursorRAM.encode w (directoryBase L) := congrFun bank 4
  have tagEq : p 5 = CursorRAM.encode w 1 := congrFun bank 5
  have columnEq : (p 6).val = incidenceStart L 0 := pv 6
  have fields : CursorRAM.ScheduleInit.inputs (p 4) (p 5) (virtualBits B n-l) l a
      (initialWidth B n) (p 6).val = outputs L B n a l w := by
    rw [rowEq, tagEq, columnEq]; rfl
  have dest : p 7 = saved L w := congrFun bank 7
  have nativeBody := native (B := B) (n := n) (a := a) (l := l) (pub := p) s m hB
    ((by decide : 2 ≤ 3).trans h.length_ge) hw (pv 0) (pv 1) (pv 2) (pv 3) (hw ▸ h.degree_lt) hl
  have sameLog := congrArg₂ (events n) dest fields
  have result := nativeBody.trans
    (congrArg some (congrArg (fun es ↦ (⟨es,some (s+1)⟩ : Report w)) sameLog))
  have hv : (saved L w).val = levelStart L 0+6 := (congrArg Fin.val dest.symm).trans (pv 7)
  have room : (saved L w).val+8 ≤ 2^w := hv ▸ (hw ▸ h.frame_end.le)
  have ef := frame_effect (pub 2) (saved L w) s n m (outputs L B n a l w) room
  refine ⟨frame_native pub (VirtualParameters.ticks n+43) s m _ result, ef.1, ef.2.1, ?_, ef.2.2.2⟩
  intro addr ha
  apply ef.2.2.1 addr
  simpa only [hv,Nat.add_assoc,Nat.reduceAdd] using ha

/-- Read the computed persistent words into registers before writing their
active-frame copies. -/
def copy (F : Shape) : FormulaRow 5 where
  dest := (.publicWord 0 : Expr).add (.lit 9)
  fields j := .load ((persistentBank F.arity).add (.lit j.val))

/-- The persistent-frame copy instruction table with its public operands embedded in the pair
machine's eleven-word bank. -/
def copyTable (F : Shape) := LiveStageLink.widen (copy F).recipe.table (Function.Embedding.refl _) operand

/-- Copying uses the stored chronological row count to locate the first level. -/
theorem copy_run {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (s : Word w) (fit : frameBase L + 8 < 2^w) :
    let R := copy L.shape
    let M := (copyTable L.shape).instantiate w pub
    let r := R.recipe.report (pub ∘ operand) s m
    let out := after m r.events
    execute M.program (R.recipe.code.length+1) (M.program.start s) m [] = some r ∧
      r.result = some (s+1) ∧
      (Frame.data (pub 2+9) out : Fin 8 → Word w) = Frame.data (saved L w) m ∧
      (∀ addr, addr < frameBase L ∨ frameBase L+8 ≤ addr → out addr = m addr) ∧
      r.events.length = R.recipe.code.length ∧ r.probes = R.recipe.reads+8 ∧ choiceBits r.events = [] := by
  intro R M r out
  have hx : (pub 2+9).val = frameBase L := by
    change _ = L.base+9
    change L.base+9+8 < 2^w at fit
    have h9 : (9 : Word w).val = 9 := Nat.mod_eq_of_lt (by omega : 9 < 2^w)
    rw [Fin.val_add,h.workspace,h9,Nat.mod_eq_of_lt (by omega : L.base+9 < 2^w)]
  have room : (pub 2+9).val+8 ≤ 2^w := hx ▸ fit.le
  have ⟨hr,ret,store,keep,work⟩ := R.execute (pub ∘ operand) s m room
  refine ⟨(LiveStageLink.execute_widen_start ..).trans hr, ret, ?_, ?_, work⟩
  · funext j
    rw [Frame.data_at _ _ room j]
    apply (store j).trans
    change m (((firstLevel L.shape.arity).eval (pub ∘ operand) s m + 6) + (j.val : Word w)).val =
      m ((saved L w)+(j.val : Word w)).val
    rw [eval_level h, saved]
    congr 2
    change ((levelStart L 0 : ℕ) : Word w) + 6 + (j.val : Word w) =
      ((levelStart L 0 + 6 : ℕ) : Word w) + (j.val : Word w)
    rw [Nat.cast_add, Nat.cast_ofNat]
  · intro addr ha
    apply keep addr
    change addr < (pub 2+9).val ∨ (pub 2+9).val+8 ≤ addr
    rwa [hx]

/-- The reports refer to the actual entry memory of each successive stage. -/
structure Trace (w : ℕ) where
  /-- Report publishing the raw input-length, geometry and address operands of the cursor
  frame. -/
  raw : Report w
  /-- Report loading the raw frame and computing the final cursor parameters. -/
  loaded : Report w
  /-- Report copying the final cursor parameters to their persistent level-zero locations. -/
  copied : Report w

/-- External memory after executing the raw parameter publisher's report. -/
def Trace.postRaw (t : Trace w) (m : Memory w) := after m t.raw.events
/-- External memory after the raw publisher and parameter loader reports. -/
def Trace.postLoad (t : Trace w) (m : Memory w) := after (t.postRaw m) t.loaded.events
/-- External memory after the raw publisher, parameter loader and persistent frame copy. -/
def Trace.post (t : Trace w) (m : Memory w) := after (t.postLoad m) t.copied.events
/-- The three descriptor-parameter reports in their execution order. -/
def Trace.log (t : Trace w) := [t.raw, t.loaded, t.copied]

/-- Construct the raw, loader and copy reports using the specified cursors and each preceding
report's output memory. -/
noncomputable def trace (L : Layout) (B n a initial phases T lanes : ℕ) (pub : Fin 11 → Word w)
    (s₀ s₁ s₂ : Word w) (m : Memory w) : Trace w :=
  let r₀ := (raw L.shape a initial phases lanes).recipe.report (pub ∘ operand) s₀ m
  let m₁ := after m r₀.events
  let r₁ := loaderReport L B n a (T*lanes) pub s₁ m₁
  let r₂ := (copy L.shape).recipe.report (pub ∘ operand) s₂ (after m₁ r₁.events)
  ⟨r₀,r₁,r₂⟩

set_option maxHeartbeats 600000 in
/-- Execute the three fixed pair-ABI tables. Each entry state may be chosen
by its enclosing linker. Both banks contain the actual cursor parameters,
and all other memory, including the row count, is preserved. -/
theorem run {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (hw : w = CursorBounds.wordBits B n) (hB : 1 ≤ B) (a lanes : ℕ)
    (hl : T*lanes ≤ virtualBits B n) (arity : 7 ≤ L.shape.arity) (scalars : 14 ≤ L.shape.scalarFields)
    (hc : Capacity B n a (T*lanes) (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6))
    (s₀ s₁ s₂ : Word w) :
    let t := trace L B n a initial phases T lanes pub s₀ s₁ s₂ m
    let A := (table L.shape a initial phases lanes).instantiate w pub
    let M := loader.instantiate w pub
    let C := (copyTable L.shape).instantiate w pub
    let R := raw L.shape a initial phases lanes
    let Q := copy L.shape
    execute A.program (R.recipe.code.length+1) (A.program.start s₀) m [] = some t.raw ∧
      execute M.program (VirtualParameters.ticks n+43+4*17) (M.program.start s₁) (t.postRaw m) [] = some t.loaded ∧
      execute C.program (Q.recipe.code.length+1) (C.program.start s₂) (t.postLoad m) [] = some t.copied ∧
      t.raw.result = some (s₀+1) ∧ t.loaded.result = some (s₁+1) ∧ t.copied.result = some (s₂+1) ∧
      Frame.data (saved L w) (t.post m) = outputs L B n a (T*lanes) w ∧
      Frame.data (pub 2+9) (t.post m) = outputs L B n a (T*lanes) w ∧
      (∀ addr, (addr < frameBase L ∨ frameBase L+8 ≤ addr) →
        (addr < levelStart L 0+6 ∨ levelStart L 0+14 ≤ addr) → t.post m addr = m addr) ∧
      levelStart L 0+14 ≤ levelStart L 0+L.shape.scalarFields ∧
      RAMBuckets.cost Report.probes t.log = R.recipe.reads + Q.recipe.reads + 44 ∧
      (eventLog t.log).length = R.recipe.code.length + (VirtualParameters.ticks n+110) + Q.recipe.code.length ∧
      branchPaths t.log = [[],[],[]] := by
  intro t A M C R Q
  have before : frameBase L+8 ≤ levelStart L 0+6 := by
    calc
      frameBase L+8 ≤ frameBase L+(L.shape.arity+1) := Nat.add_le_add_left (by omega) _
      _ ≤ directoryBase L := frame_before_directory L
      _ ≤ levelStart L 0+6 := by
        simp only [levelStart, Nat.zero_mul, Nat.add_zero, levelsBase]
        exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have savedFit : levelStart L 0+6+8 < 2^w := hw ▸ hc.frame_end
  have activeFit := before.trans_lt ((Nat.le_add_right ..).trans_lt savedFit)
  have ⟨h₀,r₀,rawBank,k₀,sz₀,p₀,c₀⟩ := prepare h s₀ a lanes activeFit
  have ⟨h₁,r₁,bank,k₁,sz₁,p₁,c₁⟩ := publish hw hB hl hc pub s₁ (t.postRaw m) rawBank
  have countAddr : (pub 2+8).val = L.base+8 := by
    change L.base+9+8 < 2^w at activeFit
    rw [Fin.val_add,h.workspace,show (8 : Word w).val = 8 from Nat.mod_eq_of_lt (by omega : 8 < 2^w),
      Nat.mod_eq_of_lt (by omega : L.base+8 < 2^w)]
  have countLow : (pub 2+8).val < frameBase L := countAddr ▸ (Nat.add_lt_add_left (by decide : 8 < 9) L.base)
  have countSaved : (pub 2+8).val < levelStart L 0+6 := countLow.trans_le ((Nat.le_add_right ..).trans before)
  have sameCount : t.postLoad m (pub 2+8).val = m (pub 2+8).val :=
    (k₁ _ (Or.inl countSaved)).trans (k₀ _ (Or.inl countLow))
  have h' : Ready L B n initial phases T pub (t.postLoad m) :=
    { h with total := (congrArg Fin.val sameCount).trans h.total }
  have ⟨h₂,r₂,active,k₂,sz₂,p₂,c₂⟩ := copy_run h' s₂ activeFit
  have savedVal : (saved L w).val = levelStart L 0+6 :=
    Nat.mod_eq_of_lt ((Nat.le_add_right ..).trans_lt savedFit)
  have room : (saved L w).val+8 ≤ 2^w := savedVal ▸ savedFit.le
  have permanent : (Frame.data (saved L w) (t.post m) : Fin 8 → Word w) = Frame.data (saved L w) (t.postLoad m) := by
    funext j
    rw [Frame.data_at _ _ room, Frame.data_at _ _ room]
    exact k₂ _ (Or.inr (before.trans (savedVal ▸ Nat.le_add_right ..)))
  refine ⟨h₀,h₁,h₂,r₀,r₁,r₂,permanent.trans bank,active.trans bank,?_,Nat.add_le_add_left scalars _,?_,?_,?_⟩
  · intro addr ha hs
    exact (k₂ _ ha).trans ((k₁ _ hs).trans (k₀ _ ha))
  · change 1+t.raw.probes+(1+t.loaded.probes+(1+t.copied.probes+0)) = R.recipe.reads+Q.recipe.reads+44
    change t.raw.probes = R.recipe.reads+8 at p₀
    change t.loaded.probes = 25 at p₁
    change t.copied.probes = Q.recipe.reads+8 at p₂
    rw [p₀,p₁,p₂]; omega
  · simp only [Trace.log,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
    change t.raw.events.length = R.recipe.code.length at sz₀
    change t.loaded.events.length = VirtualParameters.ticks n+110 at sz₁
    change t.copied.events.length = Q.recipe.code.length at sz₂
    simp only [sz₀,sz₁,sz₂,Nat.add_assoc]
  · change [choiceBits t.raw.events, choiceBits t.loaded.events, choiceBits t.copied.events] = _
    change choiceBits t.raw.events = [] at c₀
    change choiceBits t.loaded.events = [] at c₁
    change choiceBits t.copied.events = [] at c₂
    rw [c₀,c₁,c₂]

end CompressorRecords.DescriptorParameters

end VPVNP
end Computability
end OAI
