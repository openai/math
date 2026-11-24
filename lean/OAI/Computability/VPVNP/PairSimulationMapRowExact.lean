import OAI.Computability.VPVNP.PairSimulationMapRowFields
import OAI.Computability.VPVNP.PairSimulationMapOffsets

/-!
# One decoded copy of a grouped motif in private RAM

The selected grid point, selector and party fix all widths, compared fields,
and row names. The variable input consists of the resident wire bits, their
base addresses and the running offsets. The program reads the fields, selects
the corresponding fixed parameter, and advances both demand and supply offsets.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapRow

open MotifSelector MotifDemandPadding MotifEntry MotifGrid MotifBlocks MotifConversion MapLookup
open BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM
open scoped Fin.CommRing

variable {J D E : Type} [DecidableEq J]

/-- Source and target are separate positions even for loops. Absent positions
have an empty resident bit slice. -/
def endpoint {A : Type} (src dst : A → J) (j : J) (len : A → ℕ)
    (x : DemandBits src dst len j) : Bool × A → (l : ℕ) × (Fin l → Bool)
  | (false, e) => if h : j = src e then ⟨len e, x.1 e h⟩ else ⟨0, Fin.elim0⟩
  | (true, e) => if h : j = dst e then ⟨len e, x.2 e h⟩ else ⟨0, Fin.elim0⟩

/-- The two ends of each group share its running offset. -/
def group : LabelField D E → D ⊕ E
  | .inl (_, e) => .inl e
  | .inr (_, e) => .inr e

private theorem digit_eq_widen {l w n : ℕ} (hn : n ≤ w) (bits : Fin l → Bool) (off : ℕ) :
    (readField bits off n : BurstRAM.Word w) = widen hn (fieldIndex bits off n) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt ((readField_lt ..).trans_le (Nat.pow_le_pow_right (by decide) hn))

private theorem read_empty (off n : ℕ) :
    readField (Fin.elim0 : Fin 0 → Bool) off n = 0 := by simp [readField_eq_sum, paddedBit]

variable [Fintype J] [Fintype D] [Fintype E]
  {K : Type} [Field K] {src dst : D → J} {G : Supply J E}
  {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ} (B : FixedBlock K src dst G
    (realWidths p₀) (realWidths q₀) H H') (z : B.grid.demands) (s : Selector B)
  {u : ℕ} (i : Fin u) (j : J) (demand : D → ℕ) (v : E → ℕ) (d : DemandBits src dst demand j)
  (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)
  (base : LabelField D E → ℕ) (off : E → ℕ)

/-- A copy's complete endpoint slices, including demand padding and payload clipping. -/
noncomputable def slices : MapRowFields.Slices (LabelField D E) (D ⊕ E) := by
  let edges := Sum.elim (endpoint src dst j demand d)
    (endpoint G.src G.dst j v (mapHalf G (fun _ ↦ payloadBits) x))
  exact ⟨fun f ↦ (edges f).1, fun f ↦ (edges f).2, base,
    Sum.elim (fun e ↦ baseDemand B z e * i.val) off⟩

/-- The tuple of base demand digits and base payload digits from this copy. -/
noncomputable def row : LabelRow B z s j :=
  (demandFields src dst (baseDemand B z) i j d, mapHalf G (fun e b ↦
    fieldIndex (payloadBits b) (off e) (basePayload B s e)) x)

variable {w : ℕ} (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ e, basePayload B s e ≤ w)

/-- The digits actually read by the native field scan give exactly the public-table key. -/
theorem digit_eq_key (f : LabelField D E) :
    MapRowFields.digit group (Sum.elim (baseDemand B z) (basePayload B s))
        (slices B z i j demand v d x base off) f =
      labelKey B z s j fd fs (row B z s i j demand v d x off) f := by
  let read (seg : (l : ℕ) × (Fin l → Bool)) (off n : ℕ) : BurstRAM.Word w :=
    (readField seg.2 off n : BurstRAM.Word w)
  rcases f with ⟨b, e⟩ | ⟨b, e⟩
  · change read (endpoint src dst j demand d (b, e)) _ _ = _
    cases b <;> rw [endpoint]
    · split
      · rename_i h
        simpa [read, labelKey, halfKey, h, row, demandFields, slices, group] using
          digit_eq_widen (fd e) (d.1 e h) (baseDemand B z e * i.val)
      · rename_i h
        simp [read, read_empty, labelKey, halfKey, h]
    · split
      · rename_i h
        simpa [read, labelKey, halfKey, h, row, demandFields, slices, group] using
          digit_eq_widen (fd e) (d.2 e h) (baseDemand B z e * i.val)
      · rename_i h
        simp [read, read_empty, labelKey, halfKey, h]
  · change read (endpoint G.src G.dst j v (mapHalf G (fun _ ↦ payloadBits) x) (b, e)) _ _ = _
    cases b <;> rw [endpoint]
    · split
      · rename_i h
        simpa [read, labelKey, halfKey, h, row, mapHalf, slices, group] using
          digit_eq_widen (fs e) (payloadBits (x.1 e h)) (off e)
      · rename_i h
        simp [read, read_empty, labelKey, halfKey, h]
    · split
      · rename_i h
        simpa [read, labelKey, halfKey, h, row, mapHalf, slices, group] using
          digit_eq_widen (fs e) (payloadBits (x.2 e h)) (off e)
      · rename_i h
        simp [read, read_empty, labelKey, halfKey, h]


variable {r k pcCount : ℕ}

/-- A single cursor register per demand or supply group. -/
def offsetReg (reg : MapRowFields.Registers (LabelField D E) (D ⊕ E) r) : (D ⊕ E) ↪ Fin r :=
  (⟨MapRowFields.Slot.offset, fun _ _ ↦ MapRowFields.Slot.offset.inj⟩ :
    (D ⊕ E) ↪ MapRowFields.Slot (LabelField D E) (D ⊕ E)).trans reg

/-- Advance groups in a fixed order, including groups with no endpoint at the party. -/
noncomputable def groups (D E : Type) [Fintype D] [Fintype E] : List (D ⊕ E) :=
  Finset.univ.toList

theorem mem_groups (g : D ⊕ E) : g ∈ groups D E := by simp [groups]

theorem groups_nodup : (groups D E).Nodup := Finset.nodup_toList _

variable (reg : MapRowFields.Registers (LabelField D E) (D ⊕ E) r)
  (widthPort : (D ⊕ E) → Fin k)
  (key : LabelRow B z s j → LabelField D E → Fin k) (name : LabelRow B z s j → Fin k)

/-- Concrete table text chosen before the number of repetitions or the wire inputs. -/
noncomputable def nameFlow : Flow r k :=
  (table (labelFields D E) key (labelRows B z s j)).flow
    (fun f ↦ reg (.query f)) (reg .tmp) (reg .label) name

/-- Advance every demand and supply group's shared endpoint offset by the selected row's public
width. -/
noncomputable def advanceFlow : Flow r k :=
  MapOffsets.code (offsetReg reg) widthPort (reg .tmp) (groups D E)

/-- A fixed dispatch for the selected grid, selector and party. All links are between
individual instruction rows. The enclosing evaluator supplies its normal and bad exits. -/
structure Sites where
  /-- Locations of the setup and padded-reader instructions used to assemble this row's
  endpoint digits. -/
  fields : MapRowFields.Sites (LabelField D E) pcCount
  /-- Program-counter placement for the flow that looks up a parameter name from the assembled
  endpoint digits. -/
  lookupPC : (nameFlow B z s j reg key name).Label → Fin pcCount
  /-- Program-counter placement for the flow that advances the demand and supply offsets after
  lookup. -/
  advancePC : (advanceFlow reg widthPort).Label → Fin pcCount

variable (P : Sites (pcCount := pcCount) B z s j reg widthPort key name)

/-- The machine links the field reads, parameter lookup, and offset updates in order, directing
success to the supplied continuation and failure to the bad exit. -/
structure Linked (M : Machine w pcCount r k) (stop bad : Fin pcCount) : Prop where
  fields : MapRowFields.Linked reg group widthPort M P.fields
    (P.lookupPC (nameFlow B z s j reg key name).entry) (labelFields D E)
  lookup : Flow.Linked M (nameFlow B z s j reg key name) P.lookupPC
    (P.advancePC (advanceFlow reg widthPort).entry) bad
  advance : Flow.Linked M (advanceFlow reg widthPort) P.advancePC stop bad

/-- Worst-case cost of the path for this base copy. -/
noncomputable def cap : ℕ :=
  MapRowFields.steps group (Sum.elim (baseDemand B z) (basePayload B s)) (labelFields D E) +
    (2 * (labelFields D E).length * (labelRows B z s j).length + 1) +
    (2 * (groups D E).length + 1)

omit [DecidableEq J] in
/-- One bound serves all branches of the fixed block before choosing any inputs,
word width, repetitions, grid point, selector or party. -/
theorem exists_uniform_cap : ∃ C : ℕ, ∀ z s j, cap B z s j ≤ C := by
  classical
  refine ⟨∑ z : B.grid.demands, ∑ s : Selector B, ∑ j, cap B z s j, fun z s j ↦ ?_⟩
  calc
    cap B z s j ≤ ∑ j', cap B z s j' :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ s', ∑ j', cap B z s' j' :=
      Finset.single_le_sum (f := fun s' : Selector B ↦ ∑ j', cap B z s' j')
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ s)
    _ ≤ ∑ z', ∑ s', ∑ j', cap B z' s' j' :=
      Finset.single_le_sum (f := fun z' : B.grid.demands ↦ ∑ s', ∑ j', cap B z' s' j')
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ z)

/-- The exact count uses the physical public bank and this copy's decoded row.
The field scan and the cursor advances take fixed time. The label lookup stops
as soon as its first matching row is found. -/
noncomputable def exactSteps (pub : Fin k → BurstRAM.Word w) : ℕ :=
  MapRowFields.steps group (Sum.elim (baseDemand B z) (basePayload B s)) (labelFields D E) +
    ((table (labelFields D E) key (labelRows B z s j)).eval pub
      (labelKey B z s j fd fs (row B z s i j demand v d x off))).2 +
    (2 * (groups D E).length + 1)

omit [DecidableEq J] in
theorem exactSteps_le_cap (pub : Fin k → BurstRAM.Word w) :
    exactSteps B z s i j demand v d x off fd fs key pub ≤ cap B z s j := by
  exact Nat.add_le_add_right (Nat.add_le_add_left (table_eval ..).2 _) _

/-- Reading one decoded copy computes its prescribed parameter ordinal and advances
the natural offsets of every group. The only private operations are deterministic ticks. -/
theorem native_exact (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (M : Machine w pcCount r k) (stop bad : Fin pcCount)
    (hl : Linked B z s j reg widthPort key name P M stop bad)
    (hp : ∀ g, M.publicData (widthPort g) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w))
    (hkey : ∀ y f, M.publicData (key y f) = labelKey B z s j fd fs y f)
    (hname : ∀ y, M.publicData (name y) = ordinal (lookup B z s j y.1 y.2))
    (fit : MapRowFields.Fits group (Sum.elim (baseDemand B z) (basePayload B s))
      (slices B z i j demand v d x base off) w)
    (c : Config w pcCount r)
    (hc : c.pc = P.fields.first (P.lookupPC (nameFlow B z s j reg key name).entry)
      (labelFields D E))
    (hr : MapRowFields.Resident reg (slices B z i j demand v d x base off) c) :
    let buffers := slices B z i j demand v d x base off
    let width := Sum.elim (baseDemand B z) (basePayload B s)
    let n := exactSteps B z s i j demand v d x off fd fs key M.publicData
    ∃ out, Prefix M c (List.replicate n .tick) out ∧ out.pc = stop ∧
      out.reg (reg .label) = ordinal (MapStream.readRow src dst (baseDemand B z) demand G
        (basePayload B) (lookup B z) v j d x i s off) ∧
      MapRowFields.Resident reg { buffers with offset := fun g ↦ buffers.offset g + width g } out ∧
      (∀ q, q ≠ reg .label → (∀ g, q ≠ reg (.offset g)) → q ≠ reg .tmp →
        q ≠ reg .start → q ≠ reg .cursor → (∀ f, q ≠ reg (.query f)) → out.reg q = c.reg q) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  classical
  intro buffers width n
  let fields := labelFields D E
  let y := row B z s i j demand v d x off
  obtain ⟨m, pre, hm, digits, frame, mem, per⟩ :=
    MapRowFields.native reg group widthPort width buffers M P.fields _ fields
      hl.fields hp fit c hc hr
  have keys (f : LabelField D E) : m.reg (reg (.query f)) = labelKey B z s j fd fs y f :=
    (digits f (mem_labelFields f)).trans (digit_eq_key B z s i j demand v d x base off fd fs f)
  obtain ⟨a, scan, ha, hname', rest, mem', per'⟩ := native_label_exact B z s j fd fs
    (labelRows B z s j) (mem_labelRows B z s j) fields mem_labelFields key name
    (fun f ↦ reg (.query f)) (reg .tmp) (reg .label) (by simp) ordinal M hkey hname
    P.lookupPC _ bad hl.lookup m hm y keys
  obtain ⟨out, adv, hd, vals, stable, mem'', per''⟩ :=
    MapOffsets.native (offsetReg reg) widthPort (reg .tmp) (by simp [offsetReg])
      (groups D E) groups_nodup M P.advancePC stop bad hl.advance a ha
  have am := MapRowFields.resident_frame reg buffers hr frame mem
  have hmem := mem''.trans (mem'.trans mem)
  have hframe (q) (hn : q ≠ reg .label) (hg : ∀ g, q ≠ reg (.offset g)) (ht : q ≠ reg .tmp)
      (hs : q ≠ reg .start) (hc' : q ≠ reg .cursor) (hq : ∀ f, q ≠ reg (.query f)) :
      out.reg q = c.reg q :=
    (stable q ht fun g _ ↦ hg g).trans <| (rest q ht hn).trans <|
      frame q hs hc' ht fun f _ ↦ hq f
  refine ⟨out, ?_, hd, ?_, ?_, hframe, hmem, per''.trans (per'.trans per)⟩
  · dsimp only [n, exactSteps]
    rw [List.replicate_add, List.replicate_add]
    exact (pre.append scan).append adv
  · exact (stable _ (by simp) (by simp [offsetReg])).trans hname'
  · constructor
    · rw [hframe, hr.one] <;> simp
    · intro f
      rw [hframe, hr.base] <;> simp
    · intro f
      rw [hframe, hr.dataEnd] <;> simp
    · intro g
      have h := vals g
      change out.reg (reg (.offset g)) = a.reg (reg (.offset g)) + _ at h
      rw [ite_eq_left (mem_groups g), hp, rest, am.offset] at h <;> try simp
      simpa [width, Nat.cast_add] using h
    · intro f l
      rw [hmem, hr.data]

end PairSimulation.MapRow

end VPVNP
end Computability
end OAI
