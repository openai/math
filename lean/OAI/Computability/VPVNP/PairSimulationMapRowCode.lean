import OAI.Computability.VPVNP.PairSimulationMapRow

/-!
# Finite instruction table for one decoded base row

The field setup and padded reader have four and seven instruction rows per
endpoint. Their exits follow the fixed field order. The lookup and offset
advance blocks use their own finite labels. A pair of final instructions
returns the parameter ordinal or rejects.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapRowCode

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM MapRowFields
open scoped Fin.CommRing

variable {I A : Type*} [DecidableEq I] {r k p w : ℕ}

/-- Distinct addresses of all instruction rows, including the two exits. -/
abbrev Address (I : Type*) (look advance : Flow r k) :=
  (I × Fin 4) ⊕ (I × Fin 7) ⊕ Fin look.length ⊕ Fin advance.length ⊕ Bool

variable (look advance : Flow r k) (loc : Address I look advance → Fin p)

/-- Program counters for the four setup instructions and seven padded-reader instructions of
each endpoint, relocated into the row's address space. -/
def fieldSites : Sites I p where
  setupPC i a := loc (.inl (i, a))
  readerPC i a := loc (.inr (.inl (i, a)))

/-- Relocate a label of the matrix lookup flow to its instruction address in the row table. -/
def lookupPC (a : look.Label) : Fin p := loc (.inr (.inr (.inl (look.labels a))))

/-- Relocate a label of the group offset advance flow to its instruction address in the row
table. -/
def advancePC (a : advance.Label) : Fin p := loc (.inr (.inr (.inr (.inl (advance.labels a)))))

/-- The row's normal return address when `bad` is false or its rejecting address when `bad` is
true. -/
def exitPC (bad : Bool) : Fin p := loc (.inr (.inr (.inr (.inr bad))))

/-- Resolve the fall-through after the field's reader against the fixed field order. -/
def afterField (sites : Sites I p) (stop : Fin p) (i : I) : List I → Fin p
  | [] => stop
  | h :: rest => if h = i then sites.first stop rest else afterField sites stop i rest

variable (reg : Registers I A r) (group : I → A) (widthPort : A → Fin k)
  (fields : List I)

/-- Instructions for the fixed base row in a larger enclosing instruction address space. -/
def text : Address I look advance → Instr 2 p r k
  | .inl (i, a) =>
    let sites := fieldSites look advance loc
    setup reg group widthPort (sites.setupPC i) (sites.readerPC i) i a
  | .inr (.inl (i, a)) =>
    let sites := fieldSites look advance loc
    let start := lookupPC look advance loc look.entry
    FieldRead.instruction (sites.readerPC i) (readerRegs reg i) (afterField sites start i fields) a
  | .inr (.inr (.inl n)) =>
    let start := advancePC look advance loc advance.entry
    let toPC := fun t : Option look.Label ↦ (t.map (lookupPC look advance loc)).getD start
    ((look.code (look.labels.symm n)).map toPC).emit (exitPC look advance loc true)
  | .inr (.inr (.inr (.inl n))) =>
    let toPC := fun t : Option advance.Label ↦
      (t.map (advancePC look advance loc)).getD (exitPC look advance loc false)
    ((advance.code (advance.labels.symm n)).map toPC).emit (exitPC look advance loc true)
  | .inr (.inr (.inr (.inr false))) => .returnState (reg .label)
  | .inr (.inr (.inr (.inr true))) => .reject

private theorem fields_linked (sites : Sites I p) (stop : Fin p) (M : Machine w p r k)
    (fs : List I) (hn : fs.Nodup)
    (hs : ∀ i ∈ fs, ∀ a, M.code (sites.setupPC i a) =
      setup reg group widthPort (sites.setupPC i) (sites.readerPC i) i a)
    (hr : ∀ i ∈ fs, FieldRead.Linked M (sites.readerPC i) (readerRegs reg i)
      (afterField sites stop i fs)) :
    Linked reg group widthPort M sites stop fs := by
  induction fs with
  | nil => trivial
  | cons i fs ih =>
    obtain ⟨hi, hn'⟩ := List.nodup_cons.mp hn
    refine ⟨hs i (by simp), ?_, ih hn' (fun j hj ↦ hs j (by simp [hj])) ?_⟩
    · simpa [afterField] using hr i List.mem_cons_self
    · intro j hj
      have ne : i ≠ j := fun he ↦ hi (he ▸ hj)
      simpa [afterField, ne] using hr j (List.mem_cons_of_mem _ hj)

/-- The normal and rejecting exits can instead belong to the enclosing evaluator. -/
def inBody : Address I look advance → Bool
  | .inr (.inr (.inr (.inr _))) => false
  | _ => true

/-- Linking the concrete text supplies the instruction hypotheses of each subroutine. -/
theorem linked (M : Machine w p r k) (hn : fields.Nodup)
    (h : ∀ a, inBody look advance a = true →
      M.code (loc a) = (text look advance loc reg group widthPort fields a).resize w) :
    let sites := fieldSites look advance loc
    let l := lookupPC look advance loc
    let a := advancePC look advance loc
    let stop := exitPC look advance loc false
    let bad := exitPC look advance loc true
    Linked reg group widthPort M sites (l look.entry) fields ∧
      Flow.Linked M look l (a advance.entry) bad ∧ Flow.Linked M advance a stop bad := by
  intro sites l a stop bad
  refine ⟨fields_linked reg group widthPort sites _ M fields hn ?_ ?_, ⟨?_⟩, ⟨?_⟩⟩
  · intro i _ t
    rw [show sites.setupPC i t = loc (.inl (i, t)) from rfl, h _ rfl]
    fin_cases t <;> rfl
  · intro i _ t
    rw [show sites.readerPC i t = loc (.inr (.inl (i, t))) from rfl, h _ rfl]
    fin_cases t <;> rfl
  · intro t
    rw [show l t = loc (.inr (.inr (.inl (look.labels t)))) from rfl, h _ rfl]
    simp [text, l, a, bad]
  · intro t
    rw [show a t = loc (.inr (.inr (.inr (.inl (advance.labels t))))) from rfl, h _ rfl]
    simp [text, a, stop, bad]

variable [Fintype I]

/-- Numerical labels chosen entirely from the finite table, before word width or input. -/
noncomputable def addresses :
    Address I look advance ≃ Fin (Fintype.card (Address I look advance)) :=
  Fintype.equivFin _

/-- A standalone executable template whose normal exit returns the emitted ordinal. -/
noncomputable def template : Template (Fintype.card (Address I look advance)) r k :=
  let place := addresses (I := I) look advance
  ⟨2, (fieldSites look advance place).first (lookupPC look advance place look.entry) fields,
    fun pc ↦ text look advance place reg group widthPort fields (place.symm pc)⟩

/-- The standalone table has all required instruction rows for every word width. -/
theorem template_text (pub : Fin k → Word w) (a : Address I look advance) :
    let place := addresses (I := I) look advance
    ((template look advance reg group widthPort fields).instantiate w pub).code (place a) =
      (text look advance place reg group widthPort fields a).resize w := by
  simp [template, Template.instantiate]


section Block

open MotifSelector MotifDemandPadding MotifGrid MotifBlocks MotifConversion MapLookup

variable {J D E : Type} [Fintype J] [Fintype D] [Fintype E]
  {K : Type} [Field K] {src dst : D → J} {G : Supply J E}
  {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (s : Selector B) (j : J)
  (reg : Registers (LabelField D E) (D ⊕ E) r) (wp : (D ⊕ E) → Fin k)
  (key : LabelRow B z s j → LabelField D E → Fin k) (name : LabelRow B z s j → Fin k)

/-- All counters of a decoded base row's code. -/
noncomputable abbrev RowAddress :=
  Address (LabelField D E) (MapRow.nameFlow B z s j reg key name) (MapRow.advanceFlow reg wp)

/-- Link a row's fixed setup, read, lookup and cursor advance to the chosen PC positions. -/
noncomputable def rowSites (place : RowAddress B z s j reg wp key name → Fin p) :
    MapRow.Sites (pcCount := p) B z s j reg wp key name :=
  ⟨fieldSites _ _ place, lookupPC _ _ place, advancePC _ _ place⟩

open scoped Classical in
/-- Only the indicated body addresses are required to match. The exit addresses
can hold the next iteration or the caller's rejection instruction. -/
theorem row_linked (place : RowAddress B z s j reg wp key name → Fin p) (M : Machine w p r k)
    (h : ∀ a, inBody _ _ a = true → M.code (place a) =
      (text _ _ place reg MapRow.group wp (labelFields D E) a).resize w) :
    MapRow.Linked B z s j reg wp key name (rowSites B z s j reg wp key name place) M
      (exitPC _ _ place false) (exitPC _ _ place true) := by
  obtain ⟨hf, hl, ha⟩ := linked _ _ place reg MapRow.group wp (labelFields D E) M
    (Finset.nodup_toList _) h
  exact ⟨hf, hl, ha⟩

open scoped Classical in
/-- A single finite machine text realizes the decoded row links simultaneously for all
word widths and public inputs. Its size uses only the fixed motif data. -/
theorem row_template :
    let Addr := RowAddress B z s j reg wp key name
    let place := addresses (I := LabelField D E) (MapRow.nameFlow B z s j reg key name)
      (MapRow.advanceFlow reg wp)
    let sites := rowSites B z s j reg wp key name place
    ∃ T : Template (Fintype.card Addr) r k,
      T.entry = sites.fields.first (sites.lookupPC (MapRow.nameFlow B z s j reg key name).entry)
        (labelFields D E) ∧ ∀ w (pub : Fin k → BurstRAM.Word w),
      MapRow.Linked B z s j reg wp key name sites (T.instantiate w pub)
          (exitPC _ _ place false) (exitPC _ _ place true) ∧
        (T.instantiate w pub).code (exitPC _ _ place false) = .returnState (reg .label) ∧
        (T.instantiate w pub).code (exitPC _ _ place true) = .reject := by
  dsimp only
  refine ⟨template _ _ reg MapRow.group wp (labelFields D E), rfl, fun w pub ↦ ⟨?_, ?_, ?_⟩⟩
  · exact row_linked B z s j reg wp key name _ _ (fun a _ ↦ template_text _ _ _ _ _ _ pub a)
  · exact template_text _ _ _ _ _ _ pub (.inr (.inr (.inr (.inr false))))
  · exact template_text _ _ _ _ _ _ pub (.inr (.inr (.inr (.inr true))))

/-- Width constants, every compared row word, and every emitted ordinal can occupy
separate public ports of the fixed program. -/
abbrev Port (X I A : Type*) := A ⊕ ((X × I) ⊕ X)

/-- Public-word assignment for one selector, grid point, and party, giving the group widths,
the expected digit at each row field, and the parameter ordinal of each matched row. -/
noncomputable def publicWords
    (ports : Port (LabelRow B z s j) (LabelField D E) (D ⊕ E) ≃ Fin k)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ e, basePayload B s e ≤ w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) (a : Fin k) : BurstRAM.Word w :=
  (ports.symm a).elim
    (fun g ↦ ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w))
    (Sum.elim (fun q ↦ labelKey B z s j fd fs q.1 q.2)
      (fun y ↦ ordinal (lookup B z s j y.1 y.2)))

theorem publicWords_spec
    (ports : Port (LabelRow B z s j) (LabelField D E) (D ⊕ E) ≃ Fin k)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ e, basePayload B s e ≤ w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) :
    let pub := publicWords B z s j ports fd fs ordinal
    (∀ g, pub (ports (.inl g)) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w)) ∧
    (∀ y i, pub (ports (.inr (.inl (y, i)))) = labelKey B z s j fd fs y i) ∧
    (∀ y, pub (ports (.inr (.inr y))) = ordinal (lookup B z s j y.1 y.2)) := by
  simp [publicWords]

end Block

end PairSimulation.MapRowCode

end VPVNP
end Computability
end OAI
