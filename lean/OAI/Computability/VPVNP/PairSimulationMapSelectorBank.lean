import OAI.Computability.VPVNP.PairSimulationMapSelectors

/-!
# Relocatable finite text of the complete motif selector phase

The directory scanner checks every incident selector suffix against the
anchor. It enters the fixed anchor decoder on agreement, and both parts
share a bad exit. The success address can be the first row-driver test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapSelectorBank

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM

variable {X : Type*} {p r k w b : ℕ}

/-- The selector phase's disjoint banks of eleven directory-scan registers and nine
anchor-decoder registers. -/
abbrev Register := Fin 11 ⊕ Fin 9

/-- The first group holds port-scanner registers and the second holds
anchor-decoder registers. Public ports contain raw codes and ordinals. -/
structure Allocation (X : Type*) (r k : ℕ) where
  /-- Place the directory scanner's registers and the anchor decoder's registers at distinct
  positions in the enclosing machine. -/
  register : Register ↪ Fin r
  /-- Allocate distinct public ports to each selector's raw bit code and to its decoded
  ordinal. -/
  port : (X ⊕ X) ↪ Fin k

/-- Finite placement for all selector-stage opcodes and two continuation addresses. -/
inductive Location (lookupRows : ℕ) where
  | directory (i : Fin 7)
  | compareBits (i : Fin 7)
  | decoder (i : Fin 5)
  | reader (i : Fin 7)
  | lookup (i : Fin lookupRows)
  | exit (bad : Bool)
  deriving Fintype, DecidableEq

private noncomputable def number (Y : Type*) [Finite Y] : Y ≃ Fin (Nat.card Y) := by
  letI := Fintype.ofFinite Y
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- Standalone allocation that numbers all twenty selector registers and both public words of
each selector. -/
noncomputable def allocation (X : Type*) [Finite X] :
    Allocation X (Nat.card Register) (Nat.card (X ⊕ X)) :=
  ⟨(number Register).toEmbedding, (number (X ⊕ X)).toEmbedding⟩

namespace Allocation

variable (A : Allocation X r k)

/-- Physical register placement for the eleven registers of the incident port scanner. -/
def scanReg : Fin 11 ↪ Fin r := Function.Embedding.inl.trans A.register
/-- Physical register placement for the nine registers of the anchor selector decoder. -/
def decoderReg : Fin 9 ↪ Fin r := Function.Embedding.inr.trans A.register
/-- Public port containing the raw selector code against which the extracted anchor bits are
compared. -/
def codePort (x : X) := A.port (.inl x)
/-- Public port containing the ordinal produced when the anchor decoder matches this selector's
code. -/
def namePort (x : X) := A.port (.inr x)

/-- Finite lookup flow that compares the extracted anchor field against the listed selector
codes and loads the matching ordinal into the decoder's output register. -/
def lookup (xs : List X) : Flow r k :=
  ReadDecode.selectorFlow xs A.codePort A.namePort (AnchorDecode.fieldRegs A.decoderReg)
    (A.decoderReg 0)

/-- Addresses of the selector phase, including the directory and agreement loops, the anchor
decoder and reader, the lookup rows for the given selector list, and both exits. -/
abbrev Address (xs : List X) := Location (A.lookup xs).length

variable (xs : List X) (loc : A.Address xs → Fin p)

/-- The two components share the bad continuation. The successful decoder
leaves its ordinal array ready at the supplied success address. -/
def program : MapSelectors.Program X p r k where
  decoder := {
    xs := xs
    key := A.codePort
    name := A.namePort
    reg := A.decoderReg
    pc i := loc (.decoder i)
    reader i := loc (.reader i)
    label l := loc (.lookup ((A.lookup xs).labels l))
    done := loc (.exit false)
    bad := loc (.exit true) }
  scan i := loc (.directory i)
  inner i := loc (.compareBits i)
  reg := A.scanReg
  saved := by
    intro i _ _ _
    have ne (j : Fin 11) : A.decoderReg i ≠ A.scanReg j :=
      A.register.injective.ne Sum.inr_ne_inl
    exact ⟨ne 0, ne 1, ne 2, ne 4, ne 5, ne 6, ne 7⟩

/-- Test whether a selector-phase address designates an instruction body that an enclosing
program installs, with both continuations supplied by the caller. -/
def inBody : A.Address xs → Bool
  | .exit _ => false
  | _ => true

/-- The finite text uses a normal or bad halt only in standalone placements.
A linked use installs the body and gives both exits to its enclosing program. -/
def text : A.Address xs → Instr 2 p r k
  | .directory i =>
    let P := A.program xs loc
    MapPortScan.instruction P.scan P.reg (P.inner 0) (P.decoder.pc 0) P.decoder.bad i
  | .compareBits i =>
    let P := A.program xs loc
    MapConsistency.instruction P.inner (MapPortScan.innerRegs P.reg) (P.scan 4) i
  | .decoder i => (A.program xs loc).decoder.instruction i
  | .reader i =>
    let P := (A.program xs loc).decoder
    FieldRead.instruction P.reader (AnchorDecode.fieldRegs P.reg) (P.label P.selector.entry) i
  | .lookup i =>
    let P := (A.program xs loc).decoder
    ((P.selector.code ((A.lookup xs).labels.symm i)).map (fun l ↦ (l.map P.label).getD (P.pc 4)))
      |>.emit P.bad
  | .exit false => .accept
  | .exit true => .reject

/-- Matching the body text at its relocated addresses discharges the
instruction hypotheses of the port scan, bit comparison, field reader,
selector lookup and ordinal-writing loop simultaneously. -/
theorem linked (M : Machine w p r k) (install : ∀ a, A.inBody xs a = true →
    M.code (loc a) = (A.text xs loc a).resize w) :
    (A.program xs loc).Linked M := by
  constructor
  · constructor
    · intro i
      apply (install (.directory i) rfl).trans
      fin_cases i <;> rfl
    · intro i
      apply (install (.compareBits i) rfl).trans
      fin_cases i <;> rfl
  · constructor
    · intro i
      apply (install (.decoder i) rfl).trans
      fin_cases i <;> rfl
    · intro i
      apply (install (.reader i) rfl).trans
      fin_cases i <;> rfl
    · constructor
      intro l
      apply (install (.lookup ((A.lookup xs).labels l)) rfl).trans
      let D := (A.program xs loc).decoder
      have eq : (A.lookup xs).labels.symm ((A.lookup xs).labels l) = l :=
        (A.lookup xs).labels.symm_apply_apply l
      exact congrArg (fun q : D.selector.Label ↦ (((D.selector.code q).map
        (fun t ↦ (t.map D.label).getD (D.pc 4))).emit D.bad).resize w) eq

/-- Install the fixed public constants in a surrounding public-word bank. -/
def words (fits : b ≤ w) (code : X ↪ Word b) (ordinal : X → Word w) : X ⊕ X → Word w :=
  Sum.elim (fun x ↦ MapLookup.widen fits (code x)) ordinal

theorem public_spec (M : Machine w p r k) (fits : b ≤ w) (code : X ↪ Word b)
    (ordinal : X → Word w) (h : ∀ a, M.publicData (A.port a) = words fits code ordinal a) :
    (∀ x, M.publicData ((A.program xs loc).decoder.key x) = MapLookup.widen fits (code x)) ∧
      ∀ x, M.publicData ((A.program xs loc).decoder.name x) = ordinal x :=
  ⟨fun x ↦ h (.inl x), fun x ↦ h (.inr x)⟩

/-- Numbering this body and its exits gives a standalone finite template. -/
noncomputable def locations : A.Address xs ≃ Fin (Nat.card (A.Address xs)) := number _

/-- Standalone finite selector template that enters the incident-port scan and accepts after
decoding the agreed anchor suffix or rejects a failed check. -/
noncomputable def template : Template (Nat.card (A.Address xs)) r k :=
  let loc := A.locations xs
  ⟨2, (A.program xs loc).scan 0, fun i ↦ A.text xs loc (loc.symm i)⟩

theorem template_linked (pub : Fin k → Word w) :
    (A.program xs (A.locations xs)).Linked ((A.template xs).instantiate w pub) := by
  apply A.linked
  intro a _
  simp [template, Template.instantiate]

end Allocation
end PairSimulation.MapSelectorBank

end VPVNP
end Computability
end OAI
