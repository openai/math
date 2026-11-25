import OAI.ThreeFlat.RAM.TickTerminalPadding
import OAI.Hierarchy.TraceReceiverForest
import OAI.Hierarchy.TraceReceiverInput
import OAI.ThreeFlat.RAM.CapacityPadding
import OAI.ThreeFlat.RAM.SelectedPadShape

namespace OAI
/-! # Running the selected trace factors on a single receiver ROM

The selected-history procedure writes four words per true cell and the two
dimension counters. A deterministic padding procedure constructs the shared
table library. The weighted interpreter generates the field multiplication
table, expands the cells, and contracts their disjoint forest. -/

noncomputable section

namespace Hierarchy.TraceFactorReceiver

open ThreeFlat Diagonal RAM
open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Contraction HistoryFactors PhysicalProcedure
open TickWeightedBank TickSeedTail ContinuationLink
open scoped BigOperators Classical Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {w p H J : ℕ}
variable (fit : Fits (shape F p H J) w) (hdr : Procedure w)

private abbrev e := seed (k:=hdr.slots+7) fit
private abbrev aux := 4+(e fit hdr).binds
private abbrev locs := count (e fit hdr)

private def params («meta» lut : ℕ) : Fin (hdr.slots+7) → Word w :=
  Fin.addCases hdr.publicData (interpreter p H J «meta» lut fit).publicData

private def gen : Fin (aux fit hdr) ↪ Fin (hdr.registers+(aux fit hdr+36)) :=
  (Fin.castAddEmb 36).trans (Fin.natAddEmb hdr.registers)

private def runRegs : Fin 36 ↪ Fin (hdr.registers+(aux fit hdr+36)) :=
  (Fin.natAddEmb (aux fit hdr)).trans (Fin.natAddEmb hdr.registers)

private def front : Block w hdr.labels (hdr.registers+(aux fit hdr+36)) (hdr.slots+7) :=
  hdr.block.reindex (Fin.castAddEmb (aux fit hdr+36)) (Fin.castAdd 7)

private def enter : Fin (locs fit hdr) :=
  TickGenerateTable.driver (e fit hdr) (Fin.castAddEmb (36+108)) 0

/-- This ROM depends on the preparation text, capacities, and the two scratch
addresses. Its code and public data are shared by all lists of selected roots. -/
def machine («meta» lut : ℕ) :
    Machine w (hdr.labels+locs fit hdr) (hdr.registers+(aux fit hdr+36)) (hdr.slots+7) :=
  ContinuationLink.close (front fit hdr) (enter fit hdr)
    (fun pc => TickWeightedBank.emit fit «meta» lut pc (gen fit hdr) (runRegs fit hdr)
      (Fin.natAdd hdr.slots)) (params fit hdr «meta» lut)

def evalCost (F : Type*) [Fintype F] (H J : ℕ) :=
  let q := Fintype.card F
  53+(q*q)*(6*(q*q)+10)+5*H+550*J

/-- Each weighted execution has its genuine field value at any common fuel
above the preparation and interpreter bounds. All preparatory memory writes
are witnessed by the physical procedure specification on the given input. -/
theorem run («meta» lut : ℕ)
    (hm : footprint (shape F p H J) ≤ «meta») (hl : footprint (shape F p H J) ≤ lut)
    (N : BitNetwork F p) (lib : Library N) (bits : N.internal=H) (cells : N.cells=J)
    (rows : «meta»+4*J ≤ 2^w) (tables : lut+8*lib.count ≤ 2^w)
    (space : footprint (shape F p H J)<2^w) (pin : Fin p → Bool)
    (pre : Memory w → Prop) (budget : ℕ)
    (ok : hdr.Spec pre (fun _ m => Ready fit N lib pin «meta» lut m) budget)
    (st : Word w) (m : Memory w) (start : pre m) :
    TickFuel.Returns (codec (shape F p H J) fit) (machine fit hdr «meta» lut).program
      (budget+evalCost F H J) ((machine fit hdr «meta» lut).program.start st) m (N.eval pin) := by
  let M := machine fit hdr «meta» lut
  let P := Fin.natAddEmb hdr.labels (m:=locs fit hdr)
  let pc := Fin.castAddEmb (n:=hdr.labels) (locs fit hdr)
  let R := Fin.castAddEmb (n:=hdr.registers) (aux fit hdr+36)
  let K := Fin.natAdd hdr.slots (m:=7)
  have installed : hdr.block.Installed M pc R (Fin.castAdd 7) (P (enter fit hdr)) :=
    close_installed (front fit hdr) (enter fit hdr) _ _
  have data (i : Fin hdr.slots) : M.publicData (i.castAdd 7)=hdr.publicData i := by
    simp [M,machine,ContinuationLink.close,params]
  obtain ⟨s,sb,d,out,walk,atEnd,prepared⟩ := ok M pc R (Fin.castAdd 7) (P (enter fit hdr))
    installed data (M.program.start st) m rfl start
  have code (i) : M.code (P i) = TickWeightedBank.emit fit «meta» lut P
      (gen fit hdr) (runRegs fit hdr) K i := close_tail ..
  have par (i : Fin 7) : M.publicData (K i) = (interpreter p H J «meta» lut fit).publicData i := by
    simp [M,K,machine,ContinuationLink.close,params]
  obtain ⟨t,tb,done⟩ := mass_sized M fit «meta» lut hm hl N lib bits cells rows tables space pin out d
    prepared.stored prepared.frame P (gen fit hdr) (runRegs fit hdr) K code par atEnd
  have result : TickFuel.Returns (codec (shape F p H J) fit) M.program t d out (N.eval pin) := done
  exact (result.prefix walk).later (Nat.add_le_add sb tb)

/-- The table initialization depends only on the alphabet of the field. -/
def fieldCost (F : Type*) [Fintype F] :=
  let t := TickTerminalPadding.tables F+2
  let q := Fintype.card F
  462+8*t*(6*(8*t)+10)+(q*q)*(6*(q*q)+10)

omit [Field F] in
/-- The same capacities and clock cover every selected forest, including an
empty slot. Padding and contraction charge only their common linear scan and
the one-time finite field tables. -/
theorem clock_fits {m inside bits cells : ℕ} (fixed : 4*fieldCost F ≤ m) (startup : 2*inside ≤ m) :
    let H := m/40000
    let J := 2*H
    let pad := H-bits
    let fill := J-(cells+pad)
    (inside+TickTerminalPadding.budget F pad fill)+evalCost F H J ≤ m := by
  intro H J pad fill
  have div : H*40000 ≤ m := Nat.div_mul_le_self m 40000
  have unused : pad+fill≤J := by dsimp only [pad,fill,J]; omega
  dsimp only [TickTerminalPadding.budget,evalCost,fieldCost] at *
  dsimp only [J] at *
  omega

/-- The archive phase, concrete padding and table generator, then weighted
interpreter in one native executable. -/
def receiver (control header «meta» lut : ℕ) :=
  machine fit (hdr.seq (TickTerminalPadding.procedure (codec (shape F p H J) fit)
    control header «meta» lut p H J)) «meta» lut

def dimensions {W pc regs slots : ℕ} (_ : Machine W pc regs slots) := (pc,regs,slots)

/-- The receiver suffix has a fixed architecture once the field is fixed.
Its scalar capacities and all selected records occur only as operands. -/
def overhead (F : Type*) [Fintype F] :=
  let pad := SelectedPadHeader.program 1 0 0 0 0 0 0
  let t := TickTerminalPadding.tables F+2
  let q := Fintype.card F
  let e := 3*(q*q)+3
  (pad.labels+(TickPaddedROM.labels t+96)+(3*e+1+6+(36+108)),
   pad.registers+max (4+TickPaddedROM.binds t) 33+(4+e+36),8)

set_option maxRecDepth 8192 in
theorem receiver_dimensions (control header «meta» lut : ℕ) :
    dimensions (receiver fit hdr control header «meta» lut) =
      (hdr.labels+(overhead F).1,hdr.registers+(overhead F).2.1,hdr.slots+(overhead F).2.2) := by
  let code := codec (shape F p H J) fit
  let pad := TickTerminalPadding.procedure code control header «meta» lut p H J
  let proc := hdr.seq pad
  let rows := SelectedPadHeader.program w control header «meta» p H (TickTerminalPadding.tables F)
  let template := SelectedPadHeader.program 1 0 0 0 0 0 0
  let t := TickTerminalPadding.tables F+2
  have ps : pad.labels=template.labels+(TickPaddedROM.labels t+96) ∧
      pad.registers=template.registers+max (4+TickPaddedROM.binds t) 33 ∧ pad.slots=1 := by
    have actual := SelectedPadHeader.dimensions w control header «meta» p H (TickTerminalPadding.tables F)
    have fixed := SelectedPadHeader.dimensions 1 0 0 0 0 0 0
    change rows.labels+(TickPaddedROM.labels t+96)=template.labels+(TickPaddedROM.labels t+96) ∧
      rows.registers+max (4+TickPaddedROM.binds t) 33=template.registers+max (4+TickPaddedROM.binds t) 33 ∧
      rows.slots+1=1
    exact ⟨congrArg (fun n=>n+(TickPaddedROM.labels t+96)) (actual.1.trans fixed.1.symm),
      congrArg (fun n=>n+max (4+TickPaddedROM.binds t) 33) (actual.2.1.trans fixed.2.1.symm),
      congrArg (·+1) actual.2.2⟩
  have steps := HistoryFieldSeed.fieldExpr_steps (K:=proc.slots+7) code (mulBase p H J)
  change (e fit proc).steps=_ at steps
  rw [DescriptorExpr.Term.steps_eq] at steps
  have be : (e fit proc).binds = 3*(Fintype.card F*Fintype.card F)+3 := by omega
  have de : (e fit proc).labels = 3*(3*(Fintype.card F*Fintype.card F)+3)+1 := by
    rw [DescriptorExpr.Term.labels_eq,be]
  change (hdr.labels+pad.labels+((e fit proc).labels+6+(36+108)),
    hdr.registers+pad.registers+(4+(e fit proc).binds+36),hdr.slots+pad.slots+7) = _
  rw [ps.1,ps.2.1,ps.2.2,be,de]
  simp only [overhead,Nat.add_assoc,template,t]

theorem run_forest {n : ℕ} {arity : Fin n → ℕ}
    (nets : ∀ i, BitNetwork F (arity i)) (wires : ∀ i, Fin (arity i) → Fin p)
    (pin : Fin p → Bool) (control header «meta» lut : ℕ)
    (bits : (forest nets wires).internal ≤ H)
    (cells : (forest nets wires).cells+(H-(forest nets wires).internal) ≤ J)
    (hm : footprint (shape F p H J) ≤ «meta») (hl : footprint (shape F p H J) ≤ lut)
    (low : cellsBase p H≤«meta») (rowRoom : «meta»+4*J≤lut)
    (lutRoom : lut+8*(TickTerminalPadding.tables F+2)≤header)
    (headerRoom : header+4<2^w) (controlRoom : control+3<2^w)
    (apart : control+4≤header ∨ header+4≤control) (pre : Memory w → Prop) (budget : ℕ)
    (records : hdr.Spec pre (fun _ m => TickTerminalPadding.recorded (H:=H)
      (forest nets wires) pin control «meta» m) budget)
    (st : Word w) (m : Memory w) (start : pre m) :
    let N := forest nets wires
    let pad := H-N.internal
    let fill := J-(N.cells+pad)
    let M := receiver fit hdr control header «meta» lut
    TickFuel.Returns (codec (shape F p H J) fit) M.program
      ((budget+TickTerminalPadding.budget F pad fill)+evalCost F H J)
      (M.program.start st) m (∏ i, (nets i).eval (pin ∘ wires i)) := by
  intro N pad fill M
  let code := codec (shape F p H J) fit
  let padding := TickTerminalPadding.procedure code control header «meta» lut p H J
  let proc := hdr.seq padding
  let ready := fun (_ : Memory w) m => Ready fit (TraceCircuit.addPadding N pad fill)
    ((HistoryCompiledRows.library N).padded pad fill) pin «meta» lut m
  have generate : padding.Spec (TickTerminalPadding.recorded (H:=H) N pin control «meta»)
      ready (TickTerminalPadding.budget F pad fill) :=
    TickTerminalPadding.ready N pin fit control header «meta» lut bits cells low rowRoom
      lutRoom headerRoom controlRoom apart
  have prepare : proc.Spec pre ready (budget+TickTerminalPadding.budget F pad fill) := by
    intro _ _ _ machine
    exact Procedure.Spec.mono (A:=proc)
      (Procedure.Spec.seq (A:=hdr) (B:=padding) records generate (fun _ _ h => h))
      (fun _ h => h) (fun _ _ h => h.choose_spec.2) le_rfl machine
  obtain ⟨hb,hc⟩ := fixed_capacities N bits cells
  have result := run fit proc «meta» lut hm hl _ _ hb hc (by omega)
    (show lut+8*(TickTerminalPadding.tables F+2)≤2^w by omega) (by omega)
    pin pre _ prepare st m start
  rw [TraceCircuit.addPadding_eval] at result
  dsimp only [N] at result
  rw [forest_eval] at result
  exact result

/-- The complete receiver starts with the visible, unshifted self-programmed
input tape. The subsequent archive phase reads precisely those bits two words
higher and emits the selected numeric records. -/
def fromTape (control header «meta» lut : ℕ) :=
  receiver fit ((TickHeaderShift.procedure w p).seq hdr) control header «meta» lut

theorem fromTape_dimensions (control header «meta» lut : ℕ) :
    dimensions (fromTape fit hdr control header «meta» lut) =
      (37+hdr.labels+(overhead F).1,19+hdr.registers+(overhead F).2.1,6+hdr.slots+(overhead F).2.2) := by
  rw [fromTape,receiver_dimensions]
  obtain ⟨pc,reg,par⟩ := TickHeaderShift.text w p
  change ((TickHeaderShift.procedure w p).labels+hdr.labels+(overhead F).1,
    (TickHeaderShift.procedure w p).registers+hdr.registers+(overhead F).2.1,
    (TickHeaderShift.procedure w p).slots+hdr.slots+(overhead F).2.2) = _
  rw [pc,reg,par]

omit [Fintype F] in
private theorem value_of_padded_run {pc reg params labels regs slots bound fuel : ℕ}
    (M : Machine w pc reg params) (hp : pc ≤ labels) (hr : reg ≤ regs) (hk : params ≤ slots)
    (code : FieldCode F w) (st : Word w) (input : Memory w) (v : F)
    (run : TickFuel.Returns code M.program bound (M.program.start st) input v) (time : bound ≤ fuel) :
    RAM.value code (CapacityPadding.pad M hp hr hk) fuel st input = v := by
  refine (CapacityPadding.value_pad code M hp hr hk fuel st input).trans ?_
  change mass code M.program fuel (M.program.start st) input = v
  simpa only [Nat.zero_add] using (run.later time) 0

theorem tick_product {n : ℕ} {arity : Fin n → ℕ} {labels regs slots depth fuel : ℕ}
    (nets : ∀ i, BitNetwork F (arity i)) (wires : ∀ i, Fin (arity i) → Fin p)
    (input : ℕ → Bool) (control header «meta» lut : ℕ)
    (bits : (forest nets wires).internal ≤ H)
    (cells : (forest nets wires).cells+(H-(forest nets wires).internal) ≤ J)
    (hm : footprint (shape F p H J) ≤ «meta») (hl : footprint (shape F p H J) ≤ lut)
    (low : cellsBase p H≤«meta») (rowRoom : «meta»+4*J≤lut)
    (lutRoom : lut+8*(TickTerminalPadding.tables F+2)≤header)
    (headerRoom : header+4<2^w) (controlRoom : control+3<2^w)
    (apart : control+4≤header ∨ header+4≤control) (shiftRoom : 2+p+p<2^w)
    (inside : ℕ) (records : hdr.Spec
      (fun m => m=TickMountedPins.memory (w:=w) (fun i : Fin p => input i.val))
      (fun _ m => TickTerminalPadding.recorded (H:=H) (forest nets wires)
        (fun i : Fin p => input i.val) control «meta» m) inside)
    (hf : Fintype.card F≤2^w) (st : Word w) :
    let N := forest nets wires
    let pad := H-N.internal
    let fill := J-(N.cells+pad)
    let actual := fromTape fit hdr control header «meta» lut
    ∀ (hp : (dimensions actual).1 ≤ labels) (hr : (dimensions actual).2.1 ≤ regs)
      (hk : (dimensions actual).2.2 ≤ slots),
    let M := CapacityPadding.pad actual hp hr hk
    ∀ (honest : NativeTrace.Fits M p 0 depth fuel),
    (∀ i, input i.val=NativeTrace.executable M i) →
    (28+16*p+inside+TickTerminalPadding.budget F pad fill)+evalCost F H J≤fuel →
    (NativeTrace.network M honest hf st).eval (TraceBitHeader.advicePins 0 (NativeTrace.executable M) input) =
      ∏ i, (nets i).eval (fun j => input (wires i j).val) := by
  intro N pad fill actual hp hr hk M honest authentic clock
  let pin (i : Fin p) := input i.val
  let pre := fun m => m=inputMemory M p input
  let shift := TickHeaderShift.procedure w p
  have mount : shift.Spec pre (fun _ out => out=TickMountedPins.memory pin) (28+16*p) :=
    mount_input M input (by simpa only [Nat.zero_add] using honest.mount) authentic shiftRoom
  have emit : (shift.seq hdr).Spec pre (fun _ m => TickTerminalPadding.recorded (H:=H) N pin control «meta» m)
      (28+16*p+inside) := by
    intro _ _ _ machine
    exact Procedure.Spec.mono (A:=shift.seq hdr)
      (Procedure.Spec.seq (A:=shift) (B:=hdr) mount records (fun _ _ h => h))
      (fun _ h => h) (fun _ _ h => h.choose_spec.2) le_rfl machine
  have exec := run_forest fit ((TickHeaderShift.procedure w p).seq hdr) nets wires pin control header
    «meta» lut bits cells hm hl low rowRoom lutRoom headerRoom controlRoom apart pre (28+16*p+inside)
    emit st (inputMemory M p input) rfl
  have result : TickFuel.Returns (codec (shape F p H J) fit) actual.program
      (28+16*p+inside+TickTerminalPadding.budget F pad fill+evalCost F H J)
      (actual.program.start st) (inputMemory M p input) (∏ i, (nets i).eval (pin ∘ wires i)) := exec
  rw [NativeTrace.installed]
  change RAM.value (codec (shape F p H J) fit) (CapacityPadding.pad actual hp hr hk) fuel st
    (inputMemory M p input) = _
  exact value_of_padded_run actual hp hr hk (codec (shape F p H J) fit) st (inputMemory M p input)
    (∏ i, (nets i).eval (pin ∘ wires i)) result clock

end Hierarchy.TraceFactorReceiver
end

end OAI
