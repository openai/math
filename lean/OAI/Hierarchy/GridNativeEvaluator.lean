import OAI.Hierarchy.GridThroughOrdered
import OAI.Hierarchy.GridWiringNetwork
import OAI.ThreeFlat.RAM.GuessLoop
import OAI.ThreeFlat.RAM.ContractionTail
import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.TickStageSpec

namespace OAI
/-! # Native contraction of all selector settings with a common instruction table

A fixed rectangle of rail ports and a padded list of binary tests give every
legal controller setting identical header words and the same contraction time.
The selector instruction loop guesses each binary word once. After the
deterministic controller writes the cell image, the native contraction tail
returns its entry. Registers may contain arbitrary intermediate data. -/

noncomputable section
namespace Hierarchy.GridNativeEvaluator
open ThreeFlat
open GridThrough GridThrough.Ordered UniversalGrid
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open RAM RAM.BitLayout RAM.Contraction
open scoped BigOperators Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {k n p e w : ℕ}
variable (X : Catalyst.Approximation F k p)
abbrev Setting := Program (Fin e) n p X.width
def hidden := Ordered.hiddenCount e n + (n+1)^k*X.network.internal
def cells := (n+1)^k*X.network.cells + Ordered.edgeCount e n
def tailTime := 9 + 5*hidden (e:=e) (n:=n) X + 22*cells (e:=e) (n:=n) X

def net (s : Setting (e:=e) (n:=n) X) := (Ordered.wiring s).network X.network
omit [Fintype F] in
theorem dims (s : Setting (e:=e) (n:=n) X) :
    (net X s).internal=hidden (e:=e) (n:=n) X ∧ (net X s).cells=cells (e:=e) (n:=n) X := by
  have t := (Ordered.wiring s).network_sizes X.network
  exact ⟨t.2,t.1.trans (by rw [Ordered.wiring_count]; rfl)⟩

def footprint := 2+e*2+hidden (e:=e) (n:=n) X + 11*cells (e:=e) (n:=n) X + Fintype.card F^2
theorem fits (room : footprint (e:=e) (n:=n) X ≤ 2^w) (s : Setting (e:=e) (n:=n) X) :
    Contraction.Fits (net X s) w := by
  simpa only [Fits,mulBase,cellsBase,hiddenBase,(dims X s).1,(dims X s).2,footprint,pow_two] using room

def parameters (fieldRoom : Fintype.card F ≤ 2^w) : Fin 5 → Word w :=
  ![(hiddenBase (e*2) : Word w), (cellsBase (e*2) (hidden (e:=e) (n:=n) X) : Word w),
    (mulBase (e*2) (hidden (e:=e) (n:=n) X) (cells (e:=e) (n:=n) X) : Word w),
    (Fintype.card F : Word w),(FieldCode.ofCardLe fieldRoom).encode 1]

theorem param_eq (room : footprint (e:=e) (n:=n) X ≤ 2^w) (s : Setting (e:=e) (n:=n) X)
    (hf : Fintype.card F ≤ 2^w) :
    parameters (e:=e) (n:=n) X hf = Contraction.parameters (net X s) (fits X room s) := by
  simp only [parameters,Contraction.parameters,(dims X s).1,(dims X s).2,Contraction.codec]

omit [Field F] in
/-- Physical word bound on the entire accelerator, uniform over all selectors. -/
theorem path_bound {B : ℕ} (size : X.size ≤ B) (rails : e*(n+1) ≤ 2*k*((n+1)^k*B)) :
    tailTime (e:=e) (n:=n) X + footprint (e:=e) (n:=n) X ≤
      (400*k+40)*((n+1)^k*B) + (Fintype.card F)^2 + 11 := by
  have es : e≤e*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
  have cap : (n+1)^k * (X.network.cells+X.network.internal) ≤ (n+1)^k*B :=
    Nat.mul_le_mul_left _ ((Nat.le_add_right _ _).trans size)
  unfold tailTime footprint hidden cells Ordered.hiddenCount Ordered.edgeCount
  nlinarith only [es,rails,cap,Nat.zero_le (k*((n+1)^k*B)),Nat.zero_le ((n+1)^k*B),
    Nat.zero_le ((n+1)^k*X.network.cells),
    Nat.zero_le ((n+1)^k*X.network.internal)]

def capture {ell start : ℕ} (pc : Fin 9 ↪ Fin p) {r : ℕ} (reg : Fin 4 ↪ Fin r)
    {slots : ℕ} (exit : Fin p) : Fin 9 → Instr w p r slots :=
  fun j => Fin.addCases (m:=3) (n:=6) (motive:=fun _ => Instr w p r slots) (fun i : Fin 3 => match i with
    | 0 => .constant (reg 0) (start : Word w) (pc 1)
    | 1 => .constant (reg 1) ((start+ell : ℕ) : Word w) (pc 2)
    | 2 => .constant (reg 3) 1 (pc 3))
    (GuessLoop.block ((Fin.natAddEmb 3 (m:=6)).trans pc) reg exit) j

omit [Fintype F] in
/-- The native selector prefix occupies nine rows. It initializes its own
registers and gives every length-ell string weight one. -/
theorem capture_mass {r slots : ℕ} (M : Machine w p r slots)
    (field : FieldCode F w) (pc : Fin 9 ↪ Fin p) (reg : Fin 4 ↪ Fin r) (exit : Fin p)
    (start ell : ℕ) (room : start+ell<2^w)
    (inst : ∀ i,M.code (pc i)=capture (ell:=ell) (start:=start) pc reg exit i)
    (c : Config w p r) (m : Memory w) (atEntry : c.pc=pc 0) (f : ℕ) :
    let boot := ((c.put (pc 1) (reg 0) (start : Word w)).put (pc 2) (reg 1)
      ((start+ell : ℕ) : Word w)).put (pc 3) (reg 3) 1
    mass field M.program (f+4+5*ell) c m = ∑ s : Fin ell → Bool,
      mass field M.program f
        (GuessLoop.endConfig reg ((Fin.natAddEmb 3 (m:=6)).trans pc) exit ell s boot)
        (GuessLoop.install start s m) := by
  intro boot
  let gp := (Fin.natAddEmb 3 (m:=6)).trans pc
  have I : ∀ i,M.code (gp i)=GuessLoop.block gp reg exit i := fun i => by
    change M.code (pc (Fin.natAdd 3 i))=GuessLoop.block gp reg exit i
    simpa only [capture,Fin.addCases_right] using inst (Fin.natAdd 3 i)
  have a0 : M.code (pc 0) = .constant (reg 0) (start : Word w) (pc 1) := inst 0
  have a1 : M.code (pc 1) = .constant (reg 1) ((start+ell : ℕ) : Word w) (pc 2) := inst 1
  have a2 : M.code (pc 2) = .constant (reg 3) 1 (pc 3) := inst 2
  have adv : advance M.program 3 c m = some (boot,m) := by
    simp [advance,Machine.program,Instr.run,atEntry,a0,a1,a2,Config.put,boot]
  rw [show f+4+5*ell=(f+1+5*ell)+3 by omega,mass_of_advance _ _ adv]
  have h30 := reg.injective.ne (by decide : (3 : Fin 4) ≠ 0)
  have h31 := reg.injective.ne (by decide : (3 : Fin 4) ≠ 1)
  have h10 := reg.injective.ne (by decide : (1 : Fin 4) ≠ 0)
  have l : (boot.reg (reg 0)).val = start := by
    simp [boot,Config.put,Fin.val_natCast,Nat.mod_eq_of_lt (show start < 2^w by omega)]
  have r' : (boot.reg (reg 1)).val = start+ell := by
    rw [show boot.reg (reg 1) = ((start+ell : ℕ) : Word w) by
      simp only [boot,Config.put,Function.update_of_ne (Ne.symm h31),Function.update_self]]
    exact Fin.val_cast_of_lt room
  simpa only [l] using GuessLoop.mass_block field M gp reg exit I ell f boot m rfl
    (by rw [l,r']) (by simp [boot,Config.put])

/-- One accepted selector on the shared 35-row native table. Only the
generated numeric word image is required; the native weighted execution
is supplied by the table itself. -/
theorem evaluate {P R K : ℕ} (M : Machine w P R K)
    (pc : Fin 35 ↪ Fin P) (reg : Fin 10 ↪ Fin R) (pub : Fin 5 → Fin K)
    (room : footprint (e:=e) (n:=n) X ≤ 2^w) (hf : Fintype.card F ≤ 2^w)
    (inst : ∀ i,M.code (pc i)= ContractionTail.relocate pc reg pub (Contraction.instruction i))
    (data : ∀ i,M.publicData (pub i) = parameters (e:=e) (n:=n) X hf i)
    (s : Setting (e:=e) (n:=n) X) (x : GridDiagonal.Pins (Fin e))
    (c : Config w P R) (atTail : c.pc=pc 0) (m : Memory w) (extra : ℕ)
    (prepared : ∀ i < BitLayout.footprint (net X s),
      m i = BitLayout.memory (net X s) (FieldCode.ofCardLe hf)
        (x ∘ Wiring.railPin.symm) (fun _ => false) i) :
    mass (FieldCode.ofCardLe hf) M.program (extra+tailTime (e:=e) (n:=n) X) c m =
      s.wiring.eval X.coeff x := by
  let h := fits X room s
  have hdata : ∀ i,M.publicData (pub i) = Contraction.parameters (net X s) h i := by
    intro i
    exact (data i).trans (congrFun (param_eq X room s hf) i)
  have out := ContractionTail.mass_eq_network_of_prefix pc reg pub M (net X s) h inst hdata c atTail
    (x ∘ Wiring.railPin.symm) (fun _ => false) extra m prepared
  have result : (net X s).eval (x ∘ Wiring.railPin.symm) = s.wiring.eval X.coeff x :=
    ((Ordered.wiring s).network_eval X.network x).trans (Ordered.eval s X.coeff x)
  simpa only [tailTime,(dims X s).1,(dims X s).2,Nat.add_assoc] using out.trans result

open ContinuationLink PhysicalProcedure

def captureBlock (w start len : ℕ) : Block w 9 4 0 where
  first := 0
  emit pc reg _ exit := capture (w:=w) (ell:=len) (start:=start) pc reg exit

variable (emit : Procedure w)

def firstRegs : Fin 4 ↪ Fin (emit.registers+10) :=
  Fin.castLEEmb (by omega)
def first (start ell : ℕ) : Block w (9+emit.labels) (emit.registers+10) (emit.slots+5) :=
  ((captureBlock w start ell).reindex (firstRegs emit) Fin.elim0).seq
    (emit.block.reindex (Fin.castAddEmb 10) (Fin.castAdd 5))

/-- A fixed native ROM. The initializer takes nine instructions of text,
then runs the supplied deterministic setting compiler, then the same
35-row contraction for every accepted selector. -/
def machine (start ell : ℕ) (evalData : Fin 5 → Word w) :
    Machine w ((9+emit.labels)+35) (emit.registers+10) (emit.slots+5) :=
  ContinuationLink.close (first emit start ell) 0
    (fun pc i => ContractionTail.relocate pc (Fin.natAddEmb emit.registers)
      (Fin.natAdd emit.slots) (Contraction.instruction i))
    (Fin.addCases emit.publicData evalData)

private theorem exit_guess {R P : ℕ} (reg : Fin 4 ↪ Fin R) (pc : Fin 6 → Fin P) (exit : Fin P)
    (ell : ℕ) (s : Bits ell) (c : Config w P R) :
    (GuessLoop.endConfig reg pc exit ell s c).pc=exit := by
  induction ell generalizing c with
  | zero => rfl
  | succ n ih => exact ih _ _

/-- The controller need only construct its genuine numeric memory image or
reject. This theorem executes every summed selector and its tail on the
one machine, with an arbitrary common amount of extra fuel. -/
theorem value_eq (start ell budget : ℕ) (hf : Fintype.card F≤2^w)
    (room : footprint (e:=e) (n:=n) X ≤ 2^w) (tapeRoom : start+ell < 2^w)
    (m : Memory w) (st : Word w) (x : GridDiagonal.Pins (Fin e))
    (decode : Bits ell → Option (Setting (e:=e) (n:=n) X))
    (writer : ∀ s, TickStageSpec.Admission (FieldCode.ofCardLe hf) emit.block emit.publicData
      (·=GuessLoop.install start s m) (fun _ => (decode s).isSome)
      (fun _ out => ∀ v, decode s=some v → ∀ i<BitLayout.footprint (net X v),
        out i=BitLayout.memory (net X v) (FieldCode.ofCardLe hf)
          (x ∘ Wiring.railPin.symm) (fun _ => false) i) budget)
    (extra : ℕ) :
    value (FieldCode.ofCardLe hf) (machine emit start ell (parameters (e:=e) (n:=n) X hf))
      ((extra+tailTime (e:=e) (n:=n) X+budget)+4+5*ell) st m =
      ∑ s : Bits ell, (decode s).elim 0 (fun v => v.wiring.eval X.coeff x) := by
  let M := machine emit start ell (parameters (e:=e) (n:=n) X hf)
  let whole := Fin.castAddEmb (n:=9+emit.labels) 35
  let boot := (Fin.castAddEmb (n:=9) emit.labels).trans whole
  let pc := (Fin.natAddEmb 9 (m:=emit.labels)).trans whole
  let tail := Fin.natAddEmb (9+emit.labels) (m:=35)
  have install := ContinuationLink.close_installed (first emit start ell) 0
    (fun pc i => ContractionTail.relocate pc (Fin.natAddEmb emit.registers) (Fin.natAdd emit.slots)
      (Contraction.instruction i)) (Fin.addCases emit.publicData (parameters (e:=e) (n:=n) X hf))
  obtain ⟨hi,ci⟩ := (Block.seq_installed _ _ M whole (Function.Embedding.refl _) id (tail 0)).mp install
  have bootI : ∀ i,M.code (boot i)=capture (ell:=ell) (start:=start) boot (firstRegs emit)
      (pc emit.block.first) i := hi
  have controlI : emit.block.Installed M pc (Fin.castAddEmb 10) (Fin.castAdd 5) (tail 0) := ci
  have controlP (j : Fin emit.slots) : M.publicData (j.castAdd 5)=emit.publicData j := by
    simp [M,machine,ContinuationLink.close]
  have ti (i : Fin 35) : M.code (tail i)=ContractionTail.relocate tail (Fin.natAddEmb emit.registers)
      (Fin.natAdd emit.slots) (Contraction.instruction i) := by
    simp [M,machine,ContinuationLink.close,tail]
  have tp (j : Fin 5) : M.publicData (Fin.natAdd emit.slots j)=parameters (e:=e) (n:=n) X hf j := by
    simp [M,machine,ContinuationLink.close]
  change mass _ M.program _ (M.program.start st) m=_
  rw [capture_mass M _ boot (firstRegs emit) (pc emit.block.first) start ell tapeRoom bootI _ m rfl]
  apply Finset.sum_congr rfl
  intro s _
  obtain ⟨yes,no⟩ := writer s M pc (Fin.castAddEmb 10) (Fin.castAdd 5) (tail 0) controlI controlP
    _ (GuessLoop.install start s m) (exit_guess ..) rfl
  cases decodeEq : decode s with
  | none => exact no (by simp [decodeEq]) _
  | some v =>
    obtain ⟨t,ht,c',m',hpc,post,adv⟩ := yes (by simp [decodeEq])
    have eqn : extra+tailTime (e:=e) (n:=n) X+budget=(extra+(budget-t)+tailTime (e:=e) (n:=n) X)+t := by omega
    rw [eqn,mass_of_advance _ _ adv]
    exact evaluate X M tail (Fin.natAddEmb emit.registers) (Fin.natAdd emit.slots) room hf ti tp
      v x c' hpc m' _ (post v decodeEq)


end Hierarchy.GridNativeEvaluator
end

end OAI
