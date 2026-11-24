import OAI.Computability.VPVNP.CompressorBlockHeaderFootprint
import OAI.Computability.VPVNP.CompressorSourceSequence

/-! # Native header packets at their actual script occurrences -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.HeaderPacket

open BurstRAM PhaseRecipe BlockPlanner BlockHeaderRun DescriptorSpace SourceTransport SourceOnline
open scoped Fin.CommRing

variable {w : ℕ}

/-- A worker executes the evaluated public operands and stops at the planner's
exclusive cursor bound. Its actual reads and writes stay in descriptor data. -/
structure Run (L : Layout) (pub : Fin 5 → Word w) (s : Word w) (v : BlockPlanner.Visit)
    (m : Memory w) (rs : List (Report w)) (fuel : ℕ) (bits : List (List Bool)) : Prop where
  positive : 0 < fuel
  execute : let M := (v.worker.table.instantiate w (fun i ↦ (v.params i).eval pub s m)).program
    runSegment M fuel (some (v.initial.eval pub s m)) m bits = some rs
  progress : Progress (v.stop.eval pub s m) (v.initial.eval pub s m) rs
  read : Reads (levelStart L 0 ≤ ·) (eventLog rs)
  write : Writes (levelStart L 0 ≤ ·) (eventLog rs)

/-- The phase index is an actual occurrence in the catalog, including when
several occurrences share the same native code. -/
def attach (A : Script) (j : Fin A.size) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (fuel : ℕ) (bits : List (List Bool)) : SourceOnline.Visit A w :=
  ⟨j,fuel,(A.visit j).initial.eval pub s m,(A.visit j).stop.eval pub s m,
    fun i ↦ ((A.visit j).params i).eval pub s m,bits⟩

theorem attach_runs {L : Layout} (A : Script) (j : Fin A.size) {v pub s m rs fuel bits}
    (occurrence : A.visit j = v) (h : Run (w := w) L pub s v m rs fuel bits) :
    (attach A j pub s m fuel bits).Runs m rs := by
  subst v
  exact h.execute

theorem attach_checked {L : Layout} (A : Script) (j : Fin A.size) {v pub s m rs fuel bits}
    (occurrence : A.visit j = v) (h : Run (w := w) L pub s v m rs fuel bits) (cap : ℕ)
    (recipe : (A.plan.recipes j).2.code.length+1+2*Schedule.Online.N A.size A.size+5 ≤ cap)
    (clock : fuel+3+4*((A.catalog j).params+1)+2*Schedule.Online.N A.size A.size+5 ≤ cap) :
    Checked A L cap ⟨attach A j pub s m fuel bits,m,rs⟩ := by
  subst v
  exact ⟨h.positive,recipe,clock,h.progress,h.read,h.write⟩

theorem singleton {L : Layout} {v : BlockPlanner.Visit} {pub : Fin 5 → Word w} {s : Word w}
    {m : Memory w} {r : Report w} {fuel : ℕ} (positive : 0 < fuel)
    (run : rawCall v pub s m fuel = some r)
    (step : v.initial.eval pub s m < v.stop.eval pub s m)
    (ret : r.result = some (v.stop.eval pub s m))
    (rd : Reads (levelStart L 0 ≤ ·) r.events) (wr : Writes (levelStart L 0 ≤ ·) r.events) :
    Run L pub s v m [r] fuel [[]] := by
  refine ⟨positive,?_,.next step ret (.done le_rfl),?_,?_⟩
  · dsimp only
    rw [runSegment]
    change (match rawCall v pub s m fuel with
      | none => none
      | some rep => (some ([] : List (Report w))).map (rep :: ·)) = _
    rw [run]; rfl
  · simpa only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using rd
  · simpa only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using wr

private theorem succ_active (src : Word w) (fit : src.val+1 < 2^w) : src < src+1 := by
  have hi : 1 < 2^w := by omega
  apply Fin.lt_def.mpr
  change src.val < (src.val + (1 % 2^w)) % 2^w
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt fit]
  omega

theorem formula (L : Layout) (row : FormulaRow 3) (source dest : PhaseRecipe.Expr)
    (pub : Fin 5 → Word w) (s src dst : Word w) (m : Memory w)
    (he : source.eval pub s m = src) (fit : src.val+1 < 2^w)
    (run : rawCall (BlockHeaderPlan.formula row source dest) pub s m (row.recipe.code.length+1) =
      some (scalarReport row src dst m))
    (read : Reads (levelStart L 0 ≤ ·) (scalarReport row src dst m).events)
    (write : Writes (levelStart L 0 ≤ ·) (scalarReport row src dst m).events) :
    Run L pub s (BlockHeaderPlan.formula row source dest) m [scalarReport row src dst m]
      (row.recipe.code.length+1) [[]] := by
  apply singleton (Nat.succ_pos _) run _ _ read write
  · change source.eval pub s m < source.eval pub s m + ((1 : ℕ) : Word w)
    rw [he,Nat.cast_one]; exact succ_active src fit
  · change some (src+1) = some (source.eval pub s m + ((1 : ℕ) : Word w))
    rw [he,Nat.cast_one]

theorem heads {L : Layout} {i : Fin L.levels} (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (dest : PhaseRecipe.Expr) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (run : rawCall (BlockHeaderPlan.heads L.shape dest) pub s m ((DescriptorHeads.publisher L.shape).recipe.code.length+1)
      = some (headReport L i m)) :
    Run L pub s (BlockHeaderPlan.heads L.shape dest) m [headReport L i m]
      ((DescriptorHeads.publisher L.shape).recipe.code.length+1) [[]] := by
  obtain ⟨rd,wr⟩ := BlockHeaderFootprint.heads L i six fit m
  have headRoom := DescriptorSpace.level_room L fit i
  have two : 1 < 2^w := by
    unfold levelStart levelsBase directoryBase plannerTag frameBase at headRoom
    omega
  apply singleton (Nat.succ_pos _) run _ _ rd wr
  · change 0 % 2^w < 1 % 2^w
    rw [Nat.zero_mod,Nat.mod_eq_of_lt two]; decide
  · change some ((0 : Word w)+1) = some ((1 : ℕ) : Word w)
    simp

open private fit_fields header_val address_val from OAI.Computability.VPVNP.CompressorBlockHeaderRun

theorem initial {L : Layout} {a low l : ℕ} {m : Memory w} {nonempty : 0 < L.levels}
    {six : 6 ≤ L.shape.scalarFields} (h : Initial a low l L nonempty six m)
    (fourteen : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (pub : Fin 5 → Word w) (s : Word w)
    (first : BlockHeaderPlan.firstHeader.eval pub s m = header w L 0)
    (count : (pub 3).val < levelStart L 0) :
    let base := header w L 0
    let row := Scalars.initialRow (.terminal a)
    let mid := initialMemory a L m
    Run L pub s (BlockHeaderPlan.initialScalars a) m [scalarReport row (base+6) base m]
      (row.recipe.code.length+1) [[]] ∧
      Run L pub s (BlockHeaderPlan.heads L.shape BlockHeaderPlan.firstHeader) mid [headReport L 0 mid]
        ((DescriptorHeads.publisher L.shape).recipe.code.length+1) [[]] := by
  obtain ⟨rs,rh⟩ := h.visits pub s first count
  let z : Fin L.levels := ⟨0,nonempty⟩
  have room := fit_fields L z fit
  have src : BlockHeaderPlan.persistentFrame.eval pub s m = header w L 0+6 := by
    change BlockHeaderPlan.firstHeader.eval pub s m + (6 : Word w) = _
    rw [first]
  have next : (header w L 0+6).val+1 < 2^w := by
    rw [show (header w L 0+6).val = levelStart L 0+6 from address_val L 0 6 (by change levelStart L 0+_ < _ at room; omega)]
    change levelStart L 0+_ < _ at room
    omega
  obtain ⟨read,write⟩ := BlockHeaderFootprint.initial_scalar L nonempty fourteen fit (.terminal a) m
  exact ⟨formula L _ _ _ pub s _ _ m src next rs read write,heads (i := z) six fit _ pub s _ rh⟩

open Compression LevelFields

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {R : Type*}
  [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

theorem substep (v : SelectedLevel B f hf) {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Substep v L i j six m) (fit : endAddress L < 2^w)
    (first step : ℕ) (old : first+step = i.val) (new : first+(step+1) = j.val)
    (pub : Fin 5 → Word w) (s : Word w) (entry : Entry L first pub s m)
    (head : BlockHeaderPlan.firstHeader.eval pub s m = header w L 0)
    (pitch : (pub 1-1).val < levelStart L i) (count : (pub 3).val < levelStart L i) :
    let ls := BlockHeaderPlan.substep L.shape step (Scalars.ofOrigin v.origin)
    let src := header w L i
    let dst := header w L j
    let mid := inputMemory v L i m
    let next := outputMemory v L i j m
    Run L pub s (ls[0]'(by simp [ls])) m [scalarReport (inputRow v) src src m] ((inputRow v).recipe.code.length+1) [[]] ∧
      Run L pub s (ls[1]'(by simp [ls])) mid [scalarReport (outputRow v) src dst mid] ((outputRow v).recipe.code.length+1) [[]] ∧
      Run L pub s (ls[2]'(by simp [ls])) next [headReport L j next] ((DescriptorHeads.publisher L.shape).recipe.code.length+1) [[]] := by
  obtain ⟨r₁,r₂,r₃⟩ := run.visits v first step old new pub s entry head pitch count
  let mid := inputMemory v L i m
  have e₁ : Entry L first pub s mid :=
    ⟨entry.pointer,(run.relabel.2.2.2.2.1 _ (.inl pitch)).trans entry.pitch⟩
  have src : ∀ {mem : Memory w}, Entry L first pub s mem → (atLevel step).eval pub s mem = header w L i :=
    fun e ↦ old ▸ eval_atLevel e step
  have room : (header w L i).val+1 < 2^w := by
    rw [header_val L i fit]
    have := fit_fields L i fit
    omega
  obtain ⟨rd₁,wr₁⟩ := BlockHeaderFootprint.advance_scalar L i i six fit (.terminal v.inputExponent)
    (Scalars.ofOrigin v.origin) m
  obtain ⟨rd₂,wr₂⟩ := BlockHeaderFootprint.advance_scalar L i j six fit (Scalars.ofOrigin v.origin)
    (.terminal v.outputExponent) mid
  exact ⟨formula L _ _ _ pub s _ _ m (src entry) room r₁ rd₁ wr₁,
    formula L _ _ _ pub s _ _ mid (src e₁) room r₂ rd₂ wr₂,heads (i := j) six fit _ pub s _ r₃⟩

end CompressorRecords.HeaderPacket

end VPVNP
end Computability
end OAI
