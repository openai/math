import OAI.Computability.VPVNP.PairNodeFieldGuess

/-!
# Filling all half-wire arguments of a child

A finite scan enters the width and guess block at each of the old site's
outgoing slots, then its incoming slots. The fixed slot ordinal is added
to the first physical port. The destination cursor advances by the width
actually read at that port. The scan consumes exactly the semantic child
payload and leaves it in one private interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildSlots

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords LocalHistory
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices
open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {w p r k a g : ℕ}

/-- The first physical port of an old site is kept in register 8. -/
def guessRegs (reg : Fin 9 ↪ Fin r) : Fin 8 ↪ Fin r := (Fin.castAddEmb 1).trans reg

/-- Addresses of the instructions that compute the physical port, look up the field width, and
guess the field bits for each directed child slot. -/
structure Sites (n p : ℕ) where
  /-- The two instruction addresses that load the slot ordinal and add it to the site's first
  physical port. -/
  setup : Bool × Fin n → Fin 2 → Fin p
  /-- The six instruction addresses for the width lookup, including the inverse-incidence
  lookup on incoming slots. -/
  header : Bool × Fin n → Fin 6 → Fin p
  /-- The seven instruction addresses for guessing the slot's field and writing its bits to
  consecutive private cells. -/
  guess : Bool × Fin n → Fin 7 → Fin p

/-- Entry address of the first slot's setup block, or the supplied return address for an empty
slot list. -/
def first {n : ℕ} (s : Sites n p) (ret : Fin p) : List (Bool × Fin n) → Fin p
  | [] => ret
  | i :: _ => s.setup i 0

/-- Slot names can be read from a public operand or from a previously
initialized bank of private registers. Both reads take one local instruction. -/
inductive Names (n r k : ℕ) where
  | operand (port : Fin n → Fin k)
  | bank (register : Fin n → Fin r)

/-- The instruction that loads slot `j`'s ordinal into `dst` from its public operand or private
register and continues at `next`. -/
def Names.load {n : ℕ} (source : Names n r k) (j : Fin n) (dst : Fin r)
    (next : Fin p) : Instr w p r k :=
  match source with
  | .operand port => .publicWord dst (port j) next
  | .bank register => .copy dst (register j) next

/-- Every slot-name source holds its slot ordinal as a machine word in the public data or the
current register file. -/
def Names.Valid {n : ℕ} (source : Names n r k) (M : Machine w p r k)
    (c : Config w p r) : Prop :=
  match source with
  | .operand port => ∀ j, M.publicData (port j) = (j.val : Word w)
  | .bank register => ∀ j, c.reg (register j) = (j.val : Word w)

/-- The private slot-name bank is disjoint from the working registers. Public slot names impose
no register condition. -/
def Names.Apart {n d : ℕ} (source : Names n r k) (reg : Fin d ↪ Fin r) : Prop :=
  match source with
  | .operand _ => True
  | .bank register => ∀ i j, register i ≠ reg j

theorem Names.Valid.transfer {n d : ℕ} {source : Names n r k} {reg : Fin d ↪ Fin r}
    {M : Machine w p r k} {c z : Config w p r} (h : source.Valid M c)
    (apart : source.Apart reg) (frame : ∀ i, (∀ j, i ≠ reg j) → z.reg i = c.reg i) :
    source.Valid M z := by
  cases source with
  | operand => exact h
  | bank b => exact fun j => (frame (b j) (apart j)).trans (h j)

/-- Load the slot ordinal, add the site's first physical port, then enter the outgoing or
incoming width lookup according to the slot direction. -/
def setupWith {n : ℕ} (s : Sites n p) (reg : Fin 9 ↪ Fin r) (source : Names n r k)
    (i : Bool × Fin n) : Fin 2 → Instr w p r k :=
  ![source.load i.2 (reg 5) (s.setup i 1),
    .binary .add (reg 5) (reg 8) (reg 5) (FieldGuess.entry (s.header i) i.1)]

/-- The public-operand version of the two slot setup instructions. -/
abbrev setup {n : ℕ} (s : Sites n p) (reg : Fin 9 ↪ Fin r) (port : Fin n → Fin k)
    (i : Bool × Fin n) : Fin 2 → Instr w p r k := setupWith s reg (.operand port) i

theorem resize_setupWith {n : ℕ} (s : Sites n p) (reg : Fin 9 ↪ Fin r) (source : Names n r k)
    (i : Bool × Fin n) (j : Fin 2) : (setupWith (w := 1) s reg source i j).resize w =
      setupWith s reg source i j := by cases source <;> fin_cases j <;> rfl

theorem resize_setup {n : ℕ} (s : Sites n p) (reg : Fin 9 ↪ Fin r) (port : Fin n → Fin k)
    (i : Bool × Fin n) (j : Fin 2) : (setup (w := 1) s reg port i j).resize w =
      setup s reg port i j := resize_setupWith ..

/-- The machine links each listed slot's address setup, width lookup, and field guess in
sequence and passes control to `ret` after the last slot. -/
def LinkedWith {n : ℕ} (M : Machine w p r k) (s : Sites n p) (reg : Fin 9 ↪ Fin r)
    (source : Names n r k) (ret : Fin p) : List (Bool × Fin n) → Prop
  | [] => True
  | i :: rest => (∀ j, M.code (s.setup i j) = setupWith s reg source i j) ∧
    FieldGuess.Linked M (s.header i) (guessRegs reg) (s.guess i 0) ∧
    PrivateFields.Linked M .guess (s.guess i) (FieldGuess.fieldRegs (guessRegs reg))
      (first s ret rest) ∧ LinkedWith M s reg source ret rest

/-- The slot scan is linked through its return address with slot ordinals supplied by public
operands. -/
abbrev Linked {n : ℕ} (M : Machine w p r k) (s : Sites n p) (reg : Fin 9 ↪ Fin r)
    (port : Fin n → Fin k) (ret : Fin p) := LinkedWith M s reg (.operand port) ret

/-- Total semantic field length in the specified part of the scan. -/
noncomputable def length (X : State a g) (u : X.network.Site)
    (slots : List (Bool × Fin (2 ^ a))) : ℕ :=
  (slots.map fun i ↦ X.halfWidth u i.1 i.2).sum

/-- The guessed half-wire bits concatenated in the given slot order, with each field listed in
increasing bit index. -/
noncomputable def bits (X : State a g) (u : X.network.Site)
    (data : (i : Bool × Fin (2 ^ a)) → Fin (X.halfWidth u i.1 i.2) → Bool)
    (slots : List (Bool × Fin (2 ^ a))) : List Bool := slots.flatMap fun i ↦ List.ofFn (data i)

/-- The scan trace in slot order, recording two address-setup ticks, the incidence and width
lookup events for the slot direction, and the private field guess. -/
noncomputable def events (X : State a g) (u : X.network.Site) (T : IncidenceDirectory w)
    (m : Memory w) (data : (i : Bool × Fin (2 ^ a)) → Fin (X.halfWidth u i.1 i.2) → Bool)
    (slots : List (Bool × Fin (2 ^ a))) : List (Event w) := slots.flatMap fun i ↦
  [.tick,.tick] ++ FieldGuess.headerEvents T m i.1 (IncidenceDirectory.actualPort X (u, i.2)) ++
    PrivateFields.events .guess (List.ofFn (data i))

private theorem append_store (dst : ℕ) (xs ys : List Bool) (mem : Word w → Word w) :
    PrivateFields.storeBits dst (xs ++ ys) mem =
      PrivateFields.storeBits (dst+xs.length) ys (PrivateFields.storeBits dst xs mem) := by
  induction xs generalizing dst mem with
  | nil => simp [PrivateFields.storeBits]
  | cons x xs ih => simp [PrivateFields.storeBits, ih, Nat.add_assoc, Nat.add_comm 1]

private theorem physical_port (X : State a g) (u : X.network.Site) (j : Fin (2 ^ a)) :
    IncidenceDirectory.actualPort (w := w) X (u, 0) + (j.val : Word w) =
      IncidenceDirectory.actualPort X (u,j) := by
  change ((_:ℕ) : Word w) + _ = ((_:ℕ) : Word w)
  simp

variable {X : State a g} {u : X.network.Site} {T : IncidenceDirectory w} {m : Memory w}
variable {M : Machine w p r k} {s : Sites (2 ^ a) p} {reg : Fin 9 ↪ Fin r}
variable {port : Fin (2 ^ a) → Fin k} {source : Names (2 ^ a) r k} {ret : Fin p}

private theorem address_prefix (i : Bool × Fin (2 ^ a))
    (code : ∀ j, M.code (s.setup i j) = setupWith s reg source i j)
    (c : Config w p r) (names : source.Valid M c) (hc : c.pc = s.setup i 0)
      (hp : c.reg (reg 8) = IncidenceDirectory.actualPort X (u, 0)) :
    ∃ d, d.pc = FieldGuess.entry (s.header i) i.1 ∧
      d.reg (reg 5) = IncidenceDirectory.actualPort X (u, i.2) ∧
      (∀ j, j ≠ reg 5 → d.reg j = c.reg j) ∧ d.privateMem = c.privateMem ∧
      d.persistent = c.persistent ∧ ReadPrefix M m c [.tick,.tick] d := by
  let c₁ := c.put (s.setup i 1) (reg 5) (i.2.val : Word w)
  let d := c₁.put (FieldGuess.entry (s.header i) i.1) (reg 5)
    (IncidenceDirectory.actualPort X (u, i.2))
  have h₀ : M.program.step c = .localStep c₁ := by
    rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl,hc,code]
    cases source with
    | operand pt =>
      change CallAction.localStep (c.put _ _ (M.publicData (pt i.2))) = _
      rw [names]
    | bank b =>
      change CallAction.localStep (c.put _ _ (c.reg (b i.2))) = _
      rw [names]
  have h₁ : M.program.step c₁ = .localStep d := by
    rw [show M.program.step c₁ = (M.code c₁.pc).run M.publicData c₁ from rfl,
      show c₁.pc = s.setup i 1 from rfl,code]
    change CallAction.localStep (c₁.put _ _ (c₁.reg (reg 8)+c₁.reg (reg 5))) = _
    simp [d,c₁,Config.put,hp,physical_port]
  exact ⟨d,rfl,Config.put_same ..,fun j hj ↦ by
    simp [d,c₁,Config.put,Function.update_of_ne hj],rfl,rfl,
    ReadPrefix.tick h₀ (ReadPrefix.tick h₁ (ReadPrefix.nil _))⟩

/-- Ordered success and exact suffix. Every child slot, including an incoming
slot at a self-loop, consumes a separate segment of the stream. -/
theorem scanWith (slots : List (Bool × Fin (2 ^ a))) (hl : LinkedWith M s reg source ret slots)
    (apart : source.Apart reg) (rep : T.ActualColumns X m)
    (data : (i : Bool × Fin (2 ^ a)) → Fin (X.halfWidth u i.1 i.2) → Bool)
    (dst : ℕ) (fit : dst + length X u slots < 2 ^ w)
    (c : Config w p r) (names : source.Valid M c) (hc : c.pc = first s ret slots)
    (hd : c.reg (reg 2) = (dst : Word w))
    (hone : c.reg (reg 3) = 1) (hi : c.reg (reg 6) = T.actualIn) (hw : c.reg (reg 7) = T.width)
    (hp : c.reg (reg 8) = IncidenceDirectory.actualPort X (u, 0)) :
    ∃ d, d.pc = ret ∧
      d.privateMem = PrivateFields.storeBits dst (bits X u data slots) c.privateMem ∧
      d.persistent = c.persistent ∧ d.reg (reg 2) = ((dst + length X u slots : ℕ) : Word w) ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 2 → i ≠ reg 4 → i ≠ reg 5 → d.reg i = c.reg i) ∧
      ∀ fuel tail, execute M.program (fuel + (events X u T m data slots).length) c m
        (bits X u data slots ++ tail) = (execute M.program fuel d m tail).map
          (fun q ↦ ⟨events X u T m data slots ++ q.events,q.result⟩) := by
  induction slots generalizing dst c with
  | nil => exact ⟨c,hc,rfl,rfl,by simpa [length] using hd,fun _ _ _ _ _ _ ↦ rfl,
      fun fuel tail ↦ by simp [bits,events]⟩
  | cons i rest ih =>
    obtain ⟨setupCode, header, guess, more⟩ := hl
    obtain ⟨mid,hm,midPort,midReg,midMem,midState,pre⟩ :=
      address_prefix (m := m) i setupCode c names hc hp
    let n := X.halfWidth u i.1 i.2
    have fit' : dst+n+length X u rest < 2 ^ w := by simpa [n,length,Nat.add_assoc] using fit
    have keeps (j : Fin 9) (hj : j ≠ 5) := midReg (reg j) (reg.injective.ne hj)
    obtain ⟨back,hback,backMem,backState,hnext,frame,run⟩ := FieldGuess.guess_slot X u dst
      i.1 i.2 (data i) T m rep header guess mid hm ((keeps 6 (by decide)).trans hi)
      ((keeps 7 (by decide)).trans hw) midPort ((keeps 2 (by decide)).trans hd)
      ((keeps 3 (by decide)).trans hone) (by omega)
    have kept (j : Fin 9) (h₀ : j ≠ 0) (h₁ : j ≠ 1) (h₂ : j ≠ 2) (h₄ : j ≠ 4) (h₅ : j ≠ 5) :=
      (frame (reg j) (reg.injective.ne h₀) (reg.injective.ne h₁) (reg.injective.ne h₂)
        (reg.injective.ne h₄)).trans (keeps j h₅)
    obtain ⟨d,hpc,hmem,hstate,hdst,hreg,hret⟩ := ih more (dst+n) fit' back
      (names.transfer apart (fun j hn => (frame j (hn 0) (hn 1) (hn 2) (hn 4)).trans
        (midReg j (hn 5)))) hback hnext
      ((kept 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hone)
      ((kept 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi)
      ((kept 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw)
      ((kept 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
    refine ⟨d,hpc,?_,hstate.trans (backState.trans midState),?_,?_,?_⟩
    · rw [hmem,backMem,midMem]
      simp [bits,append_store,n]
    · simpa [n,length,Nat.add_assoc] using hdst
    · intro j h₀ h₁ h₂ h₄ h₅
      exact (hreg j h₀ h₁ h₂ h₄ h₅).trans ((frame _ h₀ h₁ h₂ h₄).trans (midReg _ h₅))
    · intro fuel tail
      change mid.reg (guessRegs reg 5) = _ at midPort
      rw [midPort] at run
      let es := FieldGuess.headerEvents T m i.1 (IncidenceDirectory.actualPort X (u, i.2)) ++
        PrivateFields.events (w := w) .guess (List.ofFn (data i))
      let fs := events X u T m data rest
      change execute _ (fuel + (([.tick,.tick] : List (Event w)) ++ es ++ fs).length) c m
        ((List.ofFn (data i) ++ bits X u data rest) ++ tail) = _
      have enter := ReadPrefix.execute pre ((fuel+fs.length)+es.length)
        ((List.ofFn (data i) ++ bits X u data rest) ++ tail)
      change execute _ (_+2) _ _ _ = _ at enter
      have body := run (fuel+fs.length) (bits X u data rest ++ tail)
      change execute _ (_+es.length) _ _ _ = _ at body
      have more := hret fuel tail
      change execute _ (fuel+fs.length) _ _ _ = _ at more
      rw [show fuel+(([.tick,.tick] : List (Event w)) ++ es ++ fs).length =
        ((fuel+fs.length)+es.length)+2 by simp; omega, enter, List.append_assoc, body, more]
      simp [events, Option.map_map, Function.comp_def, List.append_assoc]

theorem scan (slots : List (Bool × Fin (2 ^ a))) (hl : Linked M s reg port ret slots)
    (names : ∀ j, M.publicData (port j) = (j.val : Word w)) (rep : T.ActualColumns X m)
    (data : (i : Bool × Fin (2 ^ a)) → Fin (X.halfWidth u i.1 i.2) → Bool)
    (dst : ℕ) (fit : dst + length X u slots < 2 ^ w)
    (c : Config w p r) (hc : c.pc = first s ret slots) (hd : c.reg (reg 2) = (dst : Word w))
    (hone : c.reg (reg 3) = 1) (hi : c.reg (reg 6) = T.actualIn) (hw : c.reg (reg 7) = T.width)
    (hp : c.reg (reg 8) = IncidenceDirectory.actualPort X (u, 0)) :
    ∃ d, d.pc = ret ∧
      d.privateMem = PrivateFields.storeBits dst (bits X u data slots) c.privateMem ∧
      d.persistent = c.persistent ∧ d.reg (reg 2) = ((dst + length X u slots : ℕ) : Word w) ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 2 → i ≠ reg 4 → i ≠ reg 5 → d.reg i = c.reg i) ∧
      ∀ fuel tail, execute M.program (fuel + (events X u T m data slots).length) c m
        (bits X u data slots ++ tail) = (execute M.program fuel d m tail).map
          (fun q ↦ ⟨events X u T m data slots ++ q.events,q.result⟩) :=
  scanWith slots hl trivial rep data dst fit c names hc hd hone hi hw hp

/-- All outgoing and then all incoming slots, including slots of width zero. -/
def slots (n : ℕ) : List (Bool × Fin n) :=
  List.ofFn (fun i ↦ (false,i)) ++ List.ofFn (fun i ↦ (true,i))

theorem bits_all (h : X.network.Half u) :
    bits X u (fun i ↦ fieldBits X u h i.1 i.2) (slots (2 ^ a)) = packed X u h := by
  simp [bits,slots,packed,fields,List.flatMap_def,Function.comp_def]

/-- The complete old site buffer exactly fills the cursor range. -/
theorem length_all : length X u (slots (2 ^ a)) = ∑ dir : Bool, ∑ j, X.halfWidth u dir j := by
  simp [length,slots,Function.comp_def,List.sum_ofFn,Nat.add_comm]

/-- With too few bits some header eventually reaches an incomplete field. No
native suffix returns, regardless of the accepted bits in all earlier slots. -/
theorem reject_shortWith (slots : List (Bool × Fin (2 ^ a)))
    (hl : LinkedWith M s reg source ret slots)
    (apart : source.Apart reg) (rep : T.ActualColumns X m)
    (dst : ℕ) (fit : dst + length X u slots < 2 ^ w) (c : Config w p r) (names : source.Valid M c)
    (hc : c.pc = first s ret slots) (hd : c.reg (reg 2) = (dst : Word w))
    (hone : c.reg (reg 3) = 1) (hi : c.reg (reg 6) = T.actualIn) (hw : c.reg (reg 7) = T.width)
    (hp : c.reg (reg 8) = IncidenceDirectory.actualPort X (u, 0)) (bs : List Bool)
    (short : bs.length < length X u slots) : ¬ DFS.Returns M c m bs := by
  induction slots generalizing c dst bs with
  | nil => simp [length] at short
  | cons i rest ih =>
    obtain ⟨setupCode, header, guess, more⟩ := hl
    obtain ⟨mid,hm,midPort,midReg,_,_,pre⟩ := address_prefix (m := m) i setupCode c names hc hp
    let n := X.halfWidth u i.1 i.2
    have fit' : dst+n+length X u rest < 2 ^ w := by simpa [n,length,Nat.add_assoc] using fit
    have short' : bs.length < n+length X u rest := by simpa [n,length] using short
    have keeps (j : Fin 9) (hj : j ≠ 5) := midReg (reg j) (reg.injective.ne hj)
    intro accept
    have reach := (returns_prefix (fun f ↦ ReadPrefix.execute pre f bs)).mp accept
    by_cases full : n ≤ bs.length
    · let f (j : Fin n) := bs[j.val]'(j.isLt.trans_le full)
      have read : List.ofFn f ++ bs.drop n = bs := by
        have take : List.ofFn f = bs.take n := by
          apply List.ext_getElem (by simp [full])
          intros; simp [f]
        rw [take,List.take_append_drop]
      obtain ⟨back,hback,_,_,hnext,frame,run⟩ := FieldGuess.guess_slot X u dst
        i.1 i.2 f T m rep header guess mid hm ((keeps 6 (by decide)).trans hi)
        ((keeps 7 (by decide)).trans hw) midPort ((keeps 2 (by decide)).trans hd)
        ((keeps 3 (by decide)).trans hone) (by omega)
      have kept (j : Fin 9) (h₀ : j ≠ 0) (h₁ : j ≠ 1) (h₂ : j ≠ 2) (h₄ : j ≠ 4) (h₅ : j ≠ 5) :=
        (frame (reg j) (reg.injective.ne h₀) (reg.injective.ne h₁) (reg.injective.ne h₂)
          (reg.injective.ne h₄)).trans (keeps j h₅)
      apply ih more (dst+n) fit' back
        (names.transfer apart (fun j hn => (frame j (hn 0) (hn 1) (hn 2) (hn 4)).trans
          (midReg j (hn 5)))) hback hnext
        ((kept 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hone)
        ((kept 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi)
        ((kept 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw)
        ((kept 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
        (bs.drop n) (by simp; omega)
      rw [← read] at reach
      exact (returns_prefix (fun fuel ↦ run fuel (bs.drop n))).mp reach
    · exact FieldGuess.reject_short X u dst i.1 i.2 T m rep header guess mid hm
        ((keeps 6 (by decide)).trans hi) ((keeps 7 (by decide)).trans hw) midPort
        ((keeps 2 (by decide)).trans hd) ((keeps 3 (by decide)).trans hone)
        (by omega) bs (Nat.lt_of_not_ge full) reach

theorem reject_short (slots : List (Bool × Fin (2 ^ a))) (hl : Linked M s reg port ret slots)
    (names : ∀ j, M.publicData (port j) = (j.val : Word w)) (rep : T.ActualColumns X m)
    (dst : ℕ) (fit : dst + length X u slots < 2 ^ w) (c : Config w p r)
    (hc : c.pc = first s ret slots) (hd : c.reg (reg 2) = (dst : Word w))
    (hone : c.reg (reg 3) = 1) (hi : c.reg (reg 6) = T.actualIn) (hw : c.reg (reg 7) = T.width)
    (hp : c.reg (reg 8) = IncidenceDirectory.actualPort X (u, 0)) (bs : List Bool)
    (short : bs.length < length X u slots) : ¬ DFS.Returns M c m bs :=
  reject_shortWith slots hl trivial rep dst fit c names hc hd hone hi hw hp bs short

end PairSimulation.NodeArguments.ChildSlots

end VPVNP
end Computability
end OAI
