import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.PairSimulationPrivateSlices
import OAI.Computability.VPVNP.PairSimulationDFSDecode

/-!
# Native width lookup and independent child-slot guesses

The outgoing and incoming branches enter the same width-reading and bit-guess
instructions. An incoming slot first reads the inverse arc directory. The
guessed bits are written consecutively to the child's argument interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.FieldGuess

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices
open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {w p r k : ℕ}

/-- Registers 0--4 form the native private-field ABI. Registers 5--7 hold
physical port ID, inverse incidence base, and source width base. -/
def instruction (pc : Fin 6 → Fin p) (reg : Fin 8 ↪ Fin r) (guess : Fin p) :
    Fin 6 → Instr w p r k :=
  ![.binary .add (reg 4) (reg 6) (reg 5) (pc 1), .readExternal (reg 4) (reg 4) (pc 3),
    .copy (reg 4) (reg 5) (pc 3), .binary .add (reg 4) (reg 7) (reg 4) (pc 4),
    .readExternal (reg 1) (reg 4) (pc 5), .binary .add (reg 1) (reg 2) (reg 1) guess]

/-- Selects the width-lookup entry instruction for a slot. Incoming slots enter at instruction
zero to read the inverse incidence table, and outgoing slots enter at instruction two with
their port already known. -/
def entry (pc : Fin 6 → Fin p) (dir : Bool) : Fin p := pc (if dir then 0 else 2)

/-- The first five registers of the eight-register width routine, passed to the private
bit-guessing loop after the field end address has been computed. -/
def fieldRegs (reg : Fin 8 ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 3).trans reg

theorem resize_instruction (pc : Fin 6 → Fin p) (reg : Fin 8 ↪ Fin r) (guess : Fin p)
    (i : Fin 6) : (instruction (w := 1) (k := k) pc reg guess i).resize w =
      instruction pc reg guess i := by fin_cases i <;> rfl

/-- Requires the six installed width-lookup instructions to use the specified register
placement and transfer control to the bit-guessing entry. -/
def Linked (M : Machine w p r k) (pc : Fin 6 → Fin p) (reg : Fin 8 ↪ Fin r) (guess : Fin p) :=
  ∀ i, M.code (pc i) = instruction pc reg guess i

/-- Trace that determines the width of one port before any bit choices. An incoming port first
reads its arc ID from the inverse incidence table, then both directions read the width at
the resulting ID. -/
def headerEvents (T : IncidenceDirectory w) (m : Memory w) (dir : Bool) (port : Word w) :
    List (Event w) :=
  let id := if dir then m (T.actualIn + port).val else port
  (if dir then [.tick, .read (T.actualIn+port) id] else [.tick]) ++
    [.tick, .read (T.width+id) (m (T.width+id).val), .tick]

theorem header_cost (T : IncidenceDirectory w) (m : Memory w) (dir : Bool) (port : Word w) :
    countProbes (headerEvents T m dir port) = (if dir then 2 else 1) ∧
      (headerEvents T m dir port).length = (if dir then 5 else 4) ∧
      choiceBits (headerEvents T m dir port) = [] := by
  cases dir <;> exact ⟨rfl,rfl,rfl⟩

variable {M : Machine w p r k} {pc : Fin 6 → Fin p} {reg : Fin 8 ↪ Fin r} {guess : Fin p}

private theorem step_at (hl : Linked M pc reg guess) (i : Fin 6) (c : Config w p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction pc reg guess i).run M.publicData c := by
  simp [Machine.program,hc,hl i]

/-- Exact header continuation. No private field, histogram cell, or branch bit
is touched while following the two real incidence columns. -/
theorem header (hl : Linked M pc reg guess) (T : IncidenceDirectory w) (m : Memory w)
    (dir : Bool) (c : Config w p r) (hc : c.pc = entry pc dir)
    (hi : c.reg (reg 6) = T.actualIn) (hw : c.reg (reg 7) = T.width) :
    let port := c.reg (reg 5)
    ∃ out, out.pc = guess ∧ out.reg (reg 1) = c.reg (reg 2) + WidthRead.value T m dir port ∧
      (∀ j, j ≠ reg 1 → j ≠ reg 4 → out.reg j = c.reg j) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ ∀ fuel bs,
      execute M.program (fuel + (headerEvents T m dir port).length) c m bs =
        (execute M.program fuel out m bs).map
          (fun rep ↦ ⟨headerEvents T m dir port ++ rep.events,rep.result⟩) := by
  intro port
  let id := if dir then m (T.actualIn+port).val else port
  let addr := T.width+id
  let middle := c.put (pc 3) (reg 4) id
  let atWidth := middle.put (pc 4) (reg 4) addr
  let loaded := atWidth.put (pc 5) (reg 1) (m addr.val)
  let out := loaded.put guess (reg 1) (c.reg (reg 2) + m addr.val)
  let first : List (Event w) := if dir then [.tick,.read (T.actualIn+port) id] else [.tick]
  have enter : ReadPrefix M m c first middle := by
    cases dir with
    | false => exact ReadPrefix.tick (step_at hl 2 c hc) (ReadPrefix.nil _)
    | true =>
      let x := c.put (pc 1) (reg 4) (T.actualIn+port)
      have h₀ : M.program.step c = .localStep x := by
        rw [step_at hl 0 c hc]
        change CallAction.localStep (c.put _ _ (c.reg (reg 6) + port)) = _
        rw [hi]
      have h₁ : M.program.step x = .read (T.actualIn+port) (fun n ↦ x.put (pc 3) (reg 4) n) := by
        rw [step_at hl 1 x rfl]
        change CallAction.read (x.reg (reg 4)) _ = _
        rw [Config.put_same]
      refine ReadPrefix.tick h₀ (ReadPrefix.read _ h₁ ?_)
      have he : x.put (pc 3) (reg 4) (m (T.actualIn+port).val) = middle := by
        simp [middle, x, id, Config.put, Function.update_idem]
      rw [he]
      exact ReadPrefix.nil _
  have h₃ : M.program.step middle = .localStep atWidth := by
    rw [step_at hl 3 middle rfl]
    change CallAction.localStep (middle.put _ _ (middle.reg (reg 7) + middle.reg (reg 4))) = _
    simp [middle, atWidth, addr, Config.put, hw]
  have h₄ : M.program.step atWidth = .read addr (fun n ↦ atWidth.put (pc 5) (reg 1) n) := by
    rw [step_at hl 4 atWidth rfl]
    change CallAction.read (atWidth.reg (reg 4)) _ = _
    rw [Config.put_same]
  have h₅ : M.program.step loaded = .localStep out := by
    rw [step_at hl 5 loaded rfl]
    change CallAction.localStep (loaded.put _ _ (loaded.reg (reg 2) + loaded.reg (reg 1))) = _
    simp [out, loaded, atWidth, middle, Config.put]
  let last : List (Event w) := [.tick,.read addr (m addr.val),.tick]
  have leave : ReadPrefix M m middle last out :=
    ReadPrefix.tick h₃ (ReadPrefix.read _ h₄ (ReadPrefix.tick h₅ (ReadPrefix.nil _)))
  refine ⟨out, rfl, Config.put_same .., ?_, rfl, rfl, ?_⟩
  · intro j hj₁ hj₄
    simp [out,loaded,atWidth,middle,Config.put,Function.update_of_ne hj₁,Function.update_of_ne hj₄]
  · intro fuel bs
    change execute M.program (fuel+(first++last).length) c m bs = _
    rw [List.length_append, show fuel+(first.length+last.length) =
      (fuel+last.length)+first.length by omega,
      ReadPrefix.execute enter, ReadPrefix.execute leave]
    simp [headerEvents, first, last, addr, id, Option.map_map, Function.comp_def, List.append_assoc]

/-- The concrete slot of a child is read from the packed incidence table, then
its independently guessed payload is written at the declared private address. -/
theorem guess_slot {a g : ℕ} (X : State a g) (u : X.network.Site)
    (dst : ℕ) (dir : Bool) (j : Fin (2 ^ a)) (f : Fin (X.halfWidth u dir j) → Bool)
    (T : IncidenceDirectory w) (m : Memory w)
    (rep : T.ActualColumns X m) {bitsPC : Fin 7 → Fin p} {ret : Fin p}
    (hl : Linked M pc reg (bitsPC 0))
    (hb : PrivateFields.Linked M .guess bitsPC (fieldRegs reg) ret)
    (c : Config w p r) (hc : c.pc = entry pc dir) (hi : c.reg (reg 6) = T.actualIn)
    (hw : c.reg (reg 7) = T.width) (hport : c.reg (reg 5) = IncidenceDirectory.actualPort X (u, j))
    (hd : c.reg (reg 2) = (dst : Word w)) (h1 : c.reg (reg 3) = 1)
    (fit : dst + X.halfWidth u dir j < 2 ^ w) :
    let bits := List.ofFn f
    let es := headerEvents T m dir (c.reg (reg 5)) ++ PrivateFields.events (w := w) .guess bits
    ∃ out, out.pc = ret ∧ out.privateMem = PrivateFields.storeBits (dst)
      bits c.privateMem ∧ out.persistent = c.persistent ∧
      out.reg (reg 2) = ((dst + X.halfWidth u dir j : ℕ) : Word w) ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 2 → i ≠ reg 4 → out.reg i = c.reg i) ∧
      ∀ fuel tail, execute M.program (fuel + es.length) c m (bits ++ tail) =
        (execute M.program fuel out m tail).map (fun q ↦ ⟨es ++ q.events,q.result⟩) := by
  intro bits es
  obtain ⟨d, hp, he, keep, hm, hs, head⟩ := header hl T m dir c hc hi hw
  rw [hport, WidthRead.value_actual X u T m rep, hd] at he
  have hdst : d.reg (fieldRegs reg 2) = (dst : Word w) :=
    (keep _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans hd
  have hone : d.reg (fieldRegs reg 3) = 1 :=
    (keep _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1
  obtain ⟨out, pref, hr⟩ := PrivateFields.guess_prefix hb d hp (dst)
    bits hdst (by change d.reg (reg 1) = _; simpa [bits,CursorRAM.encode] using he) hone
    (by simpa [bits] using fit)
  refine ⟨out, hr.pc, hr.privateMem.trans (congrArg _ hm), hr.persistent.trans hs, ?_, ?_, ?_⟩
  · change out.reg (fieldRegs reg 2) = _
    simpa [bits] using hr.destination
  · intro i h₀ h₁ h₂ h₄
    exact (hr.frame _ h₀ h₂ h₄).trans (keep _ h₁ h₄)
  · intro fuel tail
    dsimp only [es]
    rw [List.length_append, show fuel+(_+_) =
      (fuel+(PrivateFields.events (w := w) .guess bits).length)+
      (headerEvents T m dir (c.reg (reg 5))).length by omega, head]
    have run := pref.execute fuel m tail
    rw [PrivateFields.events_bits] at run
    simpa [es, Option.map_map, Function.comp_def, List.append_assoc] using congrArg
      (Option.map (fun q : Report w ↦
        (⟨headerEvents T m dir (c.reg (reg 5)) ++ q.events,q.result⟩ : Report w))) run

/-- A truncated choice stream cannot return through a field, regardless of the
machine's continuation. This also applies after an arbitrary prefix of old slots. -/
theorem reject_short {a g : ℕ} (X : State a g) (u : X.network.Site) (dst : ℕ)
    (dir : Bool) (j : Fin (2 ^ a)) (T : IncidenceDirectory w) (m : Memory w)
    (rep : T.ActualColumns X m) {bitsPC : Fin 7 → Fin p} {ret : Fin p}
    (hl : Linked M pc reg (bitsPC 0))
    (hb : PrivateFields.Linked M .guess bitsPC (fieldRegs reg) ret)
    (c : Config w p r) (hc : c.pc = entry pc dir) (hi : c.reg (reg 6) = T.actualIn)
    (hw : c.reg (reg 7) = T.width) (hport : c.reg (reg 5) = IncidenceDirectory.actualPort X (u, j))
    (hd : c.reg (reg 2) = (dst : Word w)) (h1 : c.reg (reg 3) = 1)
    (fit : dst + X.halfWidth u dir j < 2 ^ w) (bs : List Bool)
    (short : bs.length < X.halfWidth u dir j) : ¬ DFS.Returns M c m bs := by
  obtain ⟨d, hp, he, keep, _, _, head⟩ := header hl T m dir c hc hi hw
  rw [hport, WidthRead.value_actual X u T m rep, hd] at he
  intro accept
  obtain ⟨fuel,out,run⟩ := (returns_prefix (fun f ↦ head f bs)).mp accept
  have bad := PrivateFields.guess_short hb d hp (dst)
    (X.halfWidth u dir j)
    ((keep _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans hd)
    (by change d.reg (reg 1) = _; simpa [CursorRAM.encode] using he)
    ((keep _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1)
    fit bs short fuel m
  rw [bad] at run
  cases run

end PairSimulation.NodeArguments.FieldGuess

end VPVNP
end Computability
end OAI
