import OAI.Computability.VPVNP.PairSimulationMapRowCode
import OAI.Computability.VPVNP.PairSimulationMapRowLoop
import OAI.Computability.VPVNP.PairSimulationMapDriverCode

/-!
# Installing the row driver and every selector's matrix in one finite table

For a fixed block, grid point and party, all selectors share the query, cursor,
and result registers. Each selector has its own width and matrix ports. The
row returns to the driver's label store, and all failed paths use the common
rejecting exit. The enclosing program can supply the final width-check address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapBank

open MotifSelector MotifGrid MotifBlocks MotifConversion MapLookup
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open scoped Fin.CommRing

variable {J D E : Type} [Fintype J] [Fintype D] [Fintype E]
  {K : Type} [Field K] {src dst : D → J} {G : Supply J E}
  {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (j : J) {r k p w : ℕ}

/-- Register slots shared across all selector rows of one map bank. Six belong to the outer
driver, and the endpoint and group slots include the label register returned to that
driver. -/
abbrev Register (D E : Type) := Fin 6 ⊕ MapRowFields.Slot (LabelField D E) (D ⊕ E)

/-- The selector's dispatch ordinal and the width and matrix words for that row. -/
abbrev PublicPort :=
  Selector B ⊕ ((s : Selector B) × MapRowCode.Port (LabelRow B z s j) (LabelField D E) (D ⊕ E))

/-- Shared register and public-port positions inside an enclosing machine. -/
structure Allocation (r k : ℕ) where
  /-- Inject the row bank's driver and field slots into the enclosing machine's register file. -/
  register : Register D E ↪ Fin r
  /-- Assign distinct public-word positions to the selector ordinals and the widths, keys, and
  parameter names of each selector's matrix. -/
  port : PublicPort B z j ↪ Fin k

private noncomputable def number (X : Type*) [Finite X] : X ≃ Fin (Nat.card X) := by
  letI := Fintype.ofFinite X
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- These finite counts always suffice for this fixed motif. -/
noncomputable def allocation :
    Allocation B z j (Nat.card (Register D E)) (Nat.card (PublicPort B z j)) := by
  classical
  exact ⟨(number _).toEmbedding, (number _).toEmbedding⟩

namespace Allocation

variable {B z j} (A : Allocation B z j r k)

/-- Place the endpoint, group, and scratch registers used by the selected matrix row in the
machine register file. -/
def rowReg : MapRowFields.Registers (LabelField D E) (D ⊕ E) r :=
  Function.Embedding.inr.trans A.register

/-- The driver's last register is precisely the shared row result. -/
def driverReg : Fin 7 ↪ Fin r :=
  (⟨Fin.lastCases (.inr (.label : MapRowFields.Slot (LabelField D E) (D ⊕ E))) Sum.inl, by
    intro l m he
    fin_cases l <;> fin_cases m <;> first | rfl | cases he⟩ : Fin 7 ↪ Register D E).trans A.register

/-- Public port holding the ordinal against which the driver compares the loaded selector. -/
def selectorPort (s : Selector B) : Fin k := A.port (.inl s)

/-- Public port for the selected base demand width or supply payload width of group `g`. -/
def widthPort (s : Selector B) (g : D ⊕ E) : Fin k := A.port (.inr ⟨s, .inl g⟩)

/-- Public port holding the expected digit of field `f` in matrix row `y` for selector `s`. -/
def keyPort (s : Selector B) (y : LabelRow B z s j) (f : LabelField D E) : Fin k :=
  A.port (.inr ⟨s, .inr (.inl (y, f))⟩)

/-- Public port holding the parameter ordinal returned when the lookup matches row `y` for
selector `s`. -/
def namePort (s : Selector B) (y : LabelRow B z s j) : Fin k :=
  A.port (.inr ⟨s, .inr (.inr y)⟩)

/-- Local public values can be installed without constraining any other public ports. -/
noncomputable def words (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) :
    PublicPort B z j → BurstRAM.Word w
  | .inl s => selector s
  | .inr ⟨s, .inl g⟩ => ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w)
  | .inr ⟨s, .inr (.inl (y, f))⟩ => labelKey B z s j fd (fs s) y f
  | .inr ⟨s, .inr (.inr y)⟩ => ordinal (lookup B z s j y.1 y.2)

/-- Install the complete fixed public table while preserving enclosing ports. -/
noncomputable def install (values : PublicPort B z j → BurstRAM.Word w)
    (other : Fin k → BurstRAM.Word w) (q : Fin k) : BurstRAM.Word w := by
  classical
  exact if h : ∃ a, A.port a = q then values h.choose else other q

theorem install_at (values : PublicPort B z j → BurstRAM.Word w) (other : Fin k → BurstRAM.Word w)
    (a : PublicPort B z j) : A.install values other (A.port a) = values a := by
  classical
  have he : ∃ t, A.port t = A.port a := ⟨a, rfl⟩
  rw [install, dite_eq_left he, A.port.injective he.choose_spec]

/-- Code and public words determine the exact comparison and row ordinal at each selector. -/
theorem public_spec (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (selector : Selector B ↪ BurstRAM.Word w) (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (M : Machine w p r k)
    (h : ∀ a, M.publicData (A.port a) = words fd fs selector ordinal a) :
    Function.Injective (M.publicData ∘ A.selectorPort) ∧
    (∀ s g, M.publicData (A.widthPort s g) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w)) ∧
    (∀ s y f, M.publicData (A.keyPort s y f) = labelKey B z s j fd (fs s) y f) ∧
    (∀ s y, M.publicData (A.namePort s y) = ordinal (lookup B z s j y.1 y.2)) := by
  have he : M.publicData ∘ A.selectorPort = selector := funext fun s ↦ h (.inl s)
  exact ⟨he ▸ selector.injective, fun s g ↦ h (.inr ⟨s, .inl g⟩),
    fun s y f ↦ h (.inr ⟨s, .inr (.inl (y, f))⟩), fun s y ↦ h (.inr ⟨s, .inr (.inr y)⟩)⟩

/-- Only body labels are allocated for a row. Its exit belongs to the driver. -/
noncomputable abbrev RowBody (s : Selector B) :=
  {a : MapRowCode.RowAddress B z s j A.rowReg (A.widthPort s) (A.keyPort s) (A.namePort s) //
    MapRowCode.inBody _ _ a = true}

/-- The two exits designate the following width comparison and rejection. -/
noncomputable abbrev Address :=
  (Fin 5 ⊕ (Selector B × Bool)) ⊕ ((s : Selector B) × A.RowBody s) ⊕ Bool

variable (loc : A.Address → Fin p)

/-- Place a selector's row instructions in the bank, redirect its successful return to the
driver's label store, and send its failed lookup to the shared rejecting exit. -/
noncomputable def rowPlace (s : Selector B)
    (a : MapRowCode.RowAddress B z s j A.rowReg (A.widthPort s) (A.keyPort s) (A.namePort s)) :
    Fin p :=
  if h : MapRowCode.inBody _ _ a then loc (.inr (.inl ⟨s, ⟨a, h⟩⟩)) else
    match a with
    | .inr (.inr (.inr (.inr false))) => loc (.inl (.inl 2))
    | _ => loc (.inr (.inr true))

/-- Program counters for field reads, matrix lookup, and offset advancement of one selector's
row in the combined bank. -/
noncomputable def sites (s : Selector B) :=
  MapRowCode.rowSites B z s j A.rowReg (A.widthPort s) (A.keyPort s) (A.namePort s)
    (A.rowPlace loc s)

/-- Assemble the driver that walks the private selector array, dispatches to the chosen row,
stores its returned label, and enters the width check after the last copy. -/
noncomputable def driver : MapDriver.Program (Selector B) p r k where
  selectors := selectorTable B
  port := A.selectorPort
  reg := A.driverReg
  pc i := loc (.inl (.inl i))
  comparePC s b := loc (.inl (.inr (s, b)))
  rowPC s := (A.sites loc s).fields.first
    ((A.sites loc s).lookupPC (MapRow.nameFlow B z s j A.rowReg (A.keyPort s) (A.namePort s)).entry)
    (labelFields D E)
  checkWidths := loc (.inr (.inr false))
  bad := loc (.inr (.inr true))

/-- The row result register coincides with the driver's label register, while
all six controller operands occupy separate locations. -/
theorem registerLayout : MapRowLoop.RegisterLayout B (A.driver loc) A.rowReg := by
  constructor
  · rfl
  · intro i hi a
    fin_cases i <;> first
    | exact (hi rfl).elim
    | apply A.register.injective.ne; exact Sum.inl_ne_inr


open Classical in
/-- Fixed text relocated to the encompassing address space. Only the body instructions
are used when linking it into a larger evaluation pipeline. -/
noncomputable def text : A.Address → Instr 2 p r k
  | .inl a => ((A.driver loc).code a).resize 2
  | .inr (.inl ⟨s, a⟩) =>
    MapRowCode.text _ _ (A.rowPlace loc s) A.rowReg MapRow.group (A.widthPort s)
      (labelFields D E) a.val
  | .inr (.inr false) => .accept
  | .inr (.inr true) => .reject

/-- Test whether an address belongs to the driver or a selected row body. The two exits have
separate addresses for use by an enclosing program. -/
def inBody : A.Address → Bool
  | .inr (.inr _) => false
  | _ => true

private theorem driver_resize (a : MapDriver.Program.Location (Selector B)) :
    (((A.driver loc).code a).resize 2).resize w = ((A.driver loc).code a).resize w := by
  rcases a with i | ⟨s, b⟩
  · fin_cases i <;> rfl
  · cases b <;> rfl

/-- Every selector returns to the shared label store. All its rejecting paths target
the driver's common bad exit. -/
theorem linked (M : Machine w p r k) (h : ∀ a, A.inBody a = true →
    M.code (loc a) = (A.text loc a).resize w) :
    (A.driver loc).Linked M ∧ ∀ s, MapRow.Linked B z s j A.rowReg (A.widthPort s) (A.keyPort s)
      (A.namePort s) (A.sites loc s) M ((A.driver loc).pc 2) (A.driver loc).bad := by
  constructor
  · apply MapDriver.Program.linked_of_code _ (Finset.nodup_toList _)
    intro a
    have he : (A.driver loc).address a = loc (.inl a) := by rcases a with i | ⟨s, b⟩ <;> rfl
    rw [he, h _ rfl]
    exact A.driver_resize loc a
  · intro s
    apply MapRowCode.row_linked B z s j A.rowReg (A.widthPort s) (A.keyPort s)
      (A.namePort s) (A.rowPlace loc s) M
    intro a ha
    rw [rowPlace, dite_eq_left ha, h _ rfl]
    rfl

/-- A fixed numbering of the combined address set. -/
noncomputable def locations : A.Address ≃ Fin (Nat.card A.Address) := number _

/-- Standalone finite implementation for all selected rows together with their driver. -/
noncomputable def template : Template (Nat.card A.Address) r k :=
  let place := A.locations
  ⟨2, (A.driver place).pc 0, fun i ↦ A.text place (place.symm i)⟩

/-- All code links of the entire driver and every decoded row hold in the same machine
for every word width and public input. -/
theorem template_linked (pub : Fin k → BurstRAM.Word w) :
    let loc := A.locations
    let M := A.template.instantiate w pub
    (A.driver loc).Linked M ∧ ∀ s, MapRow.Linked B z s j A.rowReg (A.widthPort s) (A.keyPort s)
      (A.namePort s) (A.sites loc s) M ((A.driver loc).pc 2) (A.driver loc).bad := by
  dsimp only
  apply A.linked
  intro a _
  simp [template, Template.instantiate]

/-- Install all row widths, all selector ordinals and all fixed matrix words in
the same standalone instruction table. -/
noncomputable def machine (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) :
    Machine w (Nat.card A.Address) r k :=
  A.template.instantiate w (A.install (words fd fs selector ordinal) (fun _ ↦ 0))

variable [DecidableEq J] {u : ℕ} (demand : D → ℕ) (v : E → ℕ)
  (d : MotifEntry.DemandBits src dst demand j)
  (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)
  (base : LabelField D E → ℕ) (θ : Fin u → Selector B)

/-- The actual finite driver and row machine writes the ordered parameter ordinals
of every copy and reaches the final-width checker with the full offset vector. -/
theorem native (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (selector : Selector B ↪ BurstRAM.Word w) (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (source dest : ℕ) (hs : source + u < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : source + u ≤ dest ∨ dest + u ≤ source) (c : Config w (Nat.card A.Address) r) :
    let P := A.driver A.locations
    let M := A.machine fd fs selector ordinal
    let buffers := MapRowLoop.buffers B z j demand v d x base θ
    let label := fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
      (basePayload B) (lookup B z) v j d x i (θ i)
      (fun e ↦ MotifEntry.offset (fun l ↦ basePayload B (θ l) e) i))
    (∀ i : Fin u, MapRowFields.Fits MapRow.group
      (Sum.elim (baseDemand B z) (basePayload B (θ i))) (buffers i.val) w) →
    (∀ f (l : Fin ((buffers 0).len f)), ((base f + l.val : ℕ) : BurstRAM.Word w).val < dest ∨
      dest + u ≤ ((base f + l.val : ℕ) : BurstRAM.Word w).val) →
    P.Ready M θ label source dest 0 c → MapRowFields.Resident A.rowReg (buffers 0) c →
    ∃ ticks out, ticks ≤ P.visitCap (MapRowLoop.rowCap B z j) * u + 1 ∧
      PrimedCounter.GuessWord.Prefix M c (List.replicate ticks .tick) out ∧
      out.pc = P.checkWidths ∧ MapRowFields.Resident A.rowReg (buffers u) out ∧
      (∀ i : Fin u, out.privateMem ((dest + i.val : ℕ) : BurstRAM.Word w) = label i) ∧
      (∀ a : BurstRAM.Word w, a.val < dest ∨ dest + u ≤ a.val →
        out.privateMem a = c.privateMem a) ∧ out.persistent = c.persistent := by
  intro P M buffers label fit hbits ready resident
  obtain ⟨code, rows⟩ := A.template_linked (A.install (words fd fs selector ordinal) (fun _ ↦ 0))
  obtain ⟨inj, widths, keys, names⟩ := A.public_spec fd fs selector ordinal M
    (A.install_at (words fd fs selector ordinal) (fun _ ↦ 0))
  have layout := A.registerLayout A.locations
  have run := MapRowLoop.rowRuns B z j demand v d x base θ P A.rowReg layout ordinal
    A.widthPort A.keyPort A.namePort (A.sites A.locations) M P.bad (fun _ ↦ rfl) rows
    fd fs widths keys names fit
  exact P.native code inj θ (fun i ↦ Finset.mem_toList.mpr (Finset.mem_univ _)) label
    _ source dest _ (MapRowLoop.stable B z j demand v d x base θ P A.rowReg layout dest hbits)
    run hs hd sep c ready resident

end Allocation

end PairSimulation.MapBank

end VPVNP
end Computability
end OAI
