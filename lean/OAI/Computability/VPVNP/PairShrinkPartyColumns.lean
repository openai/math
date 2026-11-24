import OAI.Computability.VPVNP.PairResidentFrameColumn
import OAI.Computability.VPVNP.PairShrinkCallFields
import OAI.Computability.VPVNP.PairShrinkABFrameAddress
import OAI.Computability.VPVNP.PairShrinkSurvivingColumn

/-!
# Native frame schedule for one party of a shrinking motif

The AB interval, when present, is followed by the incident surviving
subdivisions in source and then target order. Each assembled operand
occupies its own stride in scratch. This permits all frames to run in
one program while every operand has the value it would have in isolation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyColumns

open BurstRAM BurstRAM.PrivateRAM CompressorRecords ShrinkCallFields ResidentColumn
open scoped Fin.CommRing

/-- AB has one staging region. Each surviving type has a region at each end. -/
abbrev Column := Option (Bool × Fin 4)

/-- Test whether the selected party gathers the AB demand or the given oriented surviving
supply field in the chosen layout. -/
def active (party : Fin 6) (layout : Bool) : Column → Bool
  | none => decide (party = 0 ∨ party = 1)
  | some (dir, t) => decide (party = supplyParty dir (layout, t))

private def all : List Column :=
  none :: (List.ofFn (fun t : Fin 4 ↦ some (false, t)) ++
    List.ofFn (fun t : Fin 4 ↦ some (true, t)))

/-- The fixed list of candidate gather columns filtered to the ones incident to this party. -/
def columns (party : Fin 6) (layout : Bool) := all.filter (active party layout)

theorem mem_columns (party : Fin 6) (layout : Bool) (c : Column) :
    c ∈ columns party layout ↔ active party layout c := by
  have present : c ∈ all := by
    rcases c with _ | ⟨dir, t⟩
    · exact List.mem_cons_self
    · cases dir <;> fin_cases t <;> simp [all]
  simp [columns, present]

/-- An active gather column together with its membership in this party's filtered list. -/
abbrev At (party : Fin 6) (layout : Bool) := {c // c ∈ columns party layout}

/-- The number of frame copies in a column, given by the AB arc count or the selected supply
role's subdivision count. -/
def frames (abCount : ℕ) (subdiv : Fin 4 → ℕ) : Column → ℕ
  | none => abCount
  | some (_, t) => subdiv t

/-- Private staging destination for the AB demand or the oriented surviving supply word of this
column. -/
def base (s : Scratch) : Column → ℕ
  | none => s.staging
  | some (dir, t) => s.surviving dir t

variable (party : Fin 6) (layout : Bool) (abCount : ℕ) (subdiv : Fin 4 → ℕ)

/-- A copy visit consisting of an incident column and a valid frame ordinal within that column. -/
abbrev Visit := (c : At party layout) × Fin (frames abCount subdiv c.val)

/-- Enumerate the active columns in party order and every frame within each column in
increasing ordinal order. -/
def visits : List (Visit party layout abCount subdiv) :=
  (columns party layout).attach.flatMap fun c ↦
    (List.finRange (frames abCount subdiv c.val)).map (Sigma.mk c)

/-- The finite instruction table visits every frame of every incident column. -/
def gather {α : Type*}
    (f : ∀ c : At party layout, Fin (frames abCount subdiv c.val) → α)
    (i : Fin (visits party layout abCount subdiv).length) : α :=
  let v := (visits party layout abCount subdiv).get i
  f v.1 v.2

/-- Use the thick-wire worker on AB and the reverse subdivision worker on each supply field. -/
def setup (oldDegree newDegree pieces : ℕ) (ab : ShrinkAB.Physical.Header)
    (surv : Bool → Fin 4 → ShrinkSurvivingColumn.Inputs) :
    (c : At party layout) → Fin (frames abCount subdiv c.val) → Setup
  | ⟨none, _⟩, i => ab.setup oldDegree abCount pieces (decide (party = 1)) i.val
  | ⟨some (dir, t), _⟩, i => (surv dir t).setup newDegree subdiv t dir i

variable {party layout abCount subdiv} {w : ℕ}

private theorem writes_eq
    (row : ∀ c : At party layout, Fin (frames abCount subdiv c.val) → Row)
    (priv : Word w → Word w) :
    writes (gather party layout abCount subdiv row) (List.finRange _) priv =
      (columns party layout).attach.foldl
        (fun old c ↦ writes (row c) (List.finRange _) old) priv := by
  let vs := visits party layout abCount subdiv
  let write (old : Word w → Word w) (v : Visit party layout abCount subdiv) :=
    (row v.1 v.2).write old
  change (List.finRange vs.length).foldl (fun old i ↦ write old (vs.get i)) priv = _
  rw [← List.foldl_map, List.map_get_finRange]
  change ((columns party layout).attach.flatMap _).foldl write priv = _
  simp only [List.foldl_flatMap, List.foldl_map, writes]
  rfl

private theorem keep_fold {α : Type*} (ls : List α)
    (step : (Word w → Word w) → α → Word w → Word w) (addr : Word w)
    (keeps : ∀ i ∈ ls, ∀ old, step old i addr = old addr) (old : Word w → Word w) :
    ls.foldl step old addr = old addr := by
  induction ls generalizing old with
  | nil => rfl
  | cons i rest ih =>
    exact (ih (fun j hj ↦ keeps j (List.mem_cons_of_mem i hj)) (step old i)).trans
      (keeps i List.mem_cons_self old)

private theorem store_congr (dst : ℕ) (bits : List Bool) (addr : Word w)
    {m n : Word w → Word w} (eqv : m addr = n addr) :
    PrivateFields.storeBits dst bits m addr = PrivateFields.storeBits dst bits n addr := by
  induction bits generalizing dst m n with
  | nil => exact eqv
  | cons bit rest ih =>
    apply ih
    by_cases same : addr = (dst : Word w)
    · subst addr; simp
    · simp [Function.update_of_ne same, eqv]

private theorem writes_congr {n : ℕ} (row : Fin n → Row) (ls : List (Fin n)) (addr : Word w)
    {m n' : Word w → Word w} (eqv : m addr = n' addr) :
    writes row ls m addr = writes row ls n' addr := by
  induction ls generalizing m n' with
  | nil => exact eqv
  | cons i rest ih => exact ih (store_congr _ _ addr eqv)

private def number : Column → ℕ
  | none => 0
  | some (dir, t) => 1 + dir.toNat * 4 + t.val

private theorem number_injective : Function.Injective number := by
  rintro (_ | ⟨d, i⟩) (_ | ⟨e, j⟩) h
  · rfl
  · simp [number] at h
    omega
  · simp [number] at h
  · cases d <;> cases e <;> simp [number] at h ⊢ <;> omega

private theorem base_eq (s : Scratch) (c : Column) :
    base s c = s.staging + number c * s.stride := by
  cases c <;> simp [base, number, Scratch.surviving]

private theorem separate (s : Scratch) {c d : Column} (ne : c ≠ d) :
    base s c + s.stride ≤ base s d ∨ base s d + s.stride ≤ base s c := by
  have step (x y : Column) (h : number x < number y) : base s x + s.stride ≤ base s y := by
    rw [base_eq, base_eq, Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  exact (lt_or_gt_of_ne (number_injective.ne ne)).imp (step c d) (step d c)

variable (scratch : Scratch)
variable (row : ∀ c : At party layout, Fin (frames abCount subdiv c.val) → Row)

/-- Every nonempty slice stays within the stride reserved for its column. -/
def InBuffer (c : At party layout) (i : Fin (frames abCount subdiv c.val)) : Prop :=
  0 < (row c i).bits.length → base scratch c.val ≤ (row c i).destination + (row c i).targetOffset ∧
    (row c i).destination + (row c i).targetOffset + (row c i).bits.length ≤
      base scratch c.val + scratch.stride

/-- A frame written at its assigned base is confined whenever its last bit is within the stride. -/
theorem inBuffer_of (c : At party layout) (i : Fin (frames abCount subdiv c.val))
    (dest : (row c i).destination = base scratch c.val)
    (bound : 0 < (row c i).bits.length →
      (row c i).targetOffset + (row c i).bits.length ≤ scratch.stride) :
    InBuffer scratch row c i := by
  intro pos
  rw [dest]
  have := bound pos
  omega

variable (pivot : ℕ) (fits : ∀ c i, (row c i).Fits w pivot)
variable (inside : ∀ c i, InBuffer scratch row c i)

include fits inside in
private theorem keep_column (c : At party layout) (addr : Word w)
    (outside : addr.val < base scratch c.val ∨ base scratch c.val + scratch.stride ≤ addr.val)
    (old : Word w → Word w) :
    writes (row c) (List.finRange _) old addr = old addr := by
  apply keep_fold
  intro i _ priv
  by_cases zero : (row c i).bits.length = 0
  · simp [Row.write, List.length_eq_zero_iff.mp zero, PrivateFields.storeBits]
  have hp := Nat.pos_of_ne_zero zero
  have bounds := inside c i hp
  exact PrivateFields.storeBits_outside _ _ priv addr ((fits c i).room hp).le (by omega)

include fits inside in
/-- The final memory at each operand agrees with running that column alone.
All addresses below staging retain the child packets and shared hidden fields. -/
theorem memory (old : Word w → Word w) :
    let final := writes (gather party layout abCount subdiv row) (List.finRange _) old
    (∀ c : At party layout, ∀ addr : Word w,
      base scratch c.val ≤ addr.val → addr.val < base scratch c.val + scratch.stride →
        final addr = writes (row c) (List.finRange _) old addr) ∧
    (∀ addr : Word w, addr.val < scratch.staging → final addr = old addr) := by
  intro final
  have joined := writes_eq row old
  change final = _ at joined
  rw [joined]
  let cs := (columns party layout).attach
  let step (m : Word w → Word w) (c : At party layout) := writes (row c) (List.finRange _) m
  constructor
  · intro c addr lo hi
    have other (d : At party layout) (hd : d ≠ c) (m : Word w → Word w) :
        step m d addr = m addr := by
      have sep := separate scratch (Subtype.val_injective.ne hd)
      apply keep_column scratch row pivot fits inside
      omega
    have nd : cs.Nodup := by
      have allNd : all.Nodup := by decide
      exact List.Nodup.attach (allNd.filter _)
    obtain ⟨pre, post, hs⟩ := List.append_of_mem (List.mem_attach _ c)
    change cs = pre ++ c :: post at hs
    rw [hs, List.nodup_append] at nd
    change cs.foldl step old addr = step old c addr
    rw [hs, List.foldl_append, List.foldl_cons]
    have after := keep_fold post step addr
      (fun d hd ↦ other d (fun eqv ↦ (List.nodup_cons.mp nd.2.1).1 (eqv ▸ hd)))
      (step (pre.foldl step old) c)
    apply after.trans
    apply writes_congr
    exact keep_fold pre step addr (fun d hd ↦ other d (nd.2.2 d hd c List.mem_cons_self)) old
  · intro addr below
    apply keep_fold
    intro d _ m
    apply keep_column scratch row pivot fits inside d addr _ m
    rw [base_eq]
    exact Or.inl (below.trans_le (Nat.le_add_right _ _))

variable {p r k : ℕ}
variable (S : ∀ c : At party layout, Fin (frames abCount subdiv c.val) → Setup)
local notation "flatSetup" => gather party layout abCount subdiv S
local notation "flatRow" => gather party layout abCount subdiv row
local notation "order" => List.finRange (List.length (visits party layout abCount subdiv))

include fits inside in
/-- Run the fixed concatenated frame code at this party. Each target contains the same
operand as in its own column run, and all previously supplied inputs below staging survive. -/
theorem native (M : Machine w p r k)
    (vm : ∀ i, Fin (RegisterSetup.regCount ((flatSetup i).operands)) ↪ Fin r)
    (inputs : Fin 6 → Fin r) (loc : Label flatSetup → Fin p) (ret : Fin p)
    (code : ∀ l, M.code (loc l) = instruction flatSetup vm inputs loc ret l)
    (safe : ∀ i v j, vm i v ≠ inputs j)
    (mem : Memory w) (pub : Fin 5 → Word w) (state : Word w)
    (recorded : ∀ c i, (row c i).Recorded (S c i) pub state mem)
    (cfg : Config w p r) (entry : cfg.pc = start flatSetup loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    (read : ∀ c i, (row c i).reads cfg.privateMem) :
    ∃ events out, Result flatSetup vm M ret flatRow order mem cfg out events ∧
      (∀ c : At party layout, ∀ addr : Word w,
        base scratch c.val ≤ addr.val → addr.val < base scratch c.val + scratch.stride →
          out.privateMem addr = writes (row c) (List.finRange _) cfg.privateMem addr) ∧
      (∀ addr : Word w, addr.val < scratch.staging →
        out.privateMem addr = cfg.privateMem addr) := by
  obtain ⟨events, out, res⟩ := ResidentColumn.native M loc ret code safe flatRow mem pub state
    (fun _ ↦ recorded _ _) pivot (fun _ ↦ fits _ _) cfg entry hp hs (fun _ ↦ read _ _)
  refine ⟨events, out, res, ?_⟩
  rw [res.memory]
  exact memory scratch row pivot fits inside cfg.privateMem

section Bounds

open Compression Compression.PackingData NodeArguments

variable {a g : ℕ} (X : State a (packingLaneBits a g))

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

set_option maxHeartbeats 800000 in
-- Compare the worker’s old-arc index and the matching dependent thick-fiber coordinate.
/-- Every nonempty frame from the AB worker fits the logical demand word. -/
theorem ab_bound (m : X.packingData.Motif)
    (arcFit : Fintype.card X.Base * 2 ^ (packingLaneBits a g) * 2 ^ a ≤ 2 ^ w)
    (bucketFit : (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a +
      (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a ≤ 2 ^ w)
    (i : Fin (2 ^ (Shrink.colors a) * 2 ^ a / 4)) (arena : Arena)
    (nodes : X.network.Site → ℕ) (layout dir : Bool)
    (x : X.packingData.PlacedHalf X.packingWidth layout (ShrinkOldHalves.abSite X m dir))
    (first dst : ℕ) :
    let r := ShrinkAB.Physical.row X m arcFit bucketFit i arena nodes layout dir x
      (first := first) (dest := dst)
    0 < r.bits.length →
      r.targetOffset + r.bits.length ≤ X.packingData.abWidth X.shrinkNumber X.packingWidth m := by
  intro r pos
  let b := X.packingData.bundle m
  let z := ShrinkAB.Physical.members X arcFit bucketFit b i
  let cut := X.packingData.demandSlice X.shrinkNumber X.shrinkOrder X.packingWidth b z ⟨m, rfl⟩
  have len : r.bits.length = cut.length := List.length_ofFn
  change cut.targetOffset + r.bits.length ≤ _
  rw [len]
  exact ShrinkAB.target_bound X.packingData X.shrinkNumber X.shrinkOrder X.packingWidth
    ⟨m, rfl⟩ z (len ▸ pos)

/-- A surviving reverse frame has precisely the endpoint's subdivision width. -/
theorem surviving_bound {b pad : ℕ} (layout : Bool) (subdiv : Fin 4 → ℕ)
    (width : X.packingData.Motif → Fin 4 → ℕ)
    {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
    (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad)
    (m : X.packingData.Motif) (t : Fin 4) (dir : Bool)
    (z : (X.shrinkOutputState layout subdiv width I).network.Half
      (ShrinkSurvivingOperands.site X layout m t dir))
    (arena : Arena) (node dst : ℕ) (bank : ShrinkSliceSweep.Row w)
    (hpos : ∀ t, 0 < subdiv t) (j : Fin (subdiv t)) :
    let r := ShrinkSurvivingColumn.row X layout subdiv width I m t dir z arena node dst bank j
    r.targetOffset + r.bits.length ≤ width m t := by
  intro r
  have len := ShrinkSurvivingColumn.row_length X layout subdiv width I m t dir z arena
    node dst bank hpos j
  change r.bits.length = _ at len
  rw [len]
  exact ShrinkSurvivingFrames.end_le _ _ (hpos t) j

end Bounds

end PairSimulation.ShrinkPartyColumns

end VPVNP
end Computability
end OAI
