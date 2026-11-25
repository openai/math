import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Embedding external-memory instruction tables in a caller RAM -/

namespace ThreeFlat.RAM.NativeRelocate

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w p r k P R K : ℕ}

/-- Rename the operands of one instruction in the caller's table. -/
def relocate (pc : Fin p ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) :
    Instr w p r k → Instr w P R K
  | .constant a v n => .constant (reg a) v (pc n)
  | .publicWord a b n => .publicWord (reg a) (pub b) (pc n)
  | .stateWord a n => .stateWord (reg a) (pc n)
  | .copy a b n => .copy (reg a) (reg b) (pc n)
  | .binary op a b d n => .binary op (reg a) (reg b) (reg d) (pc n)
  | .loadPrivate a b n => .loadPrivate (reg a) (reg b) (pc n)
  | .storePrivate a b n => .storePrivate (reg a) (reg b) (pc n)
  | .jumpEq a b n m => .jumpEq (reg a) (reg b) (pc n) (pc m)
  | .jumpLt a b n m => .jumpLt (reg a) (reg b) (pc n) (pc m)
  | .choose n m => .choose (pc n) (pc m)
  | .readExternal a b n => .readExternal (reg a) (reg b) (pc n)
  | .writeExternal a b n => .writeExternal (reg a) (reg b) (pc n)
  | .returnState b => .returnState (reg b)
  | .accept => .accept
  | .reject => .reject

/-- Instructions independent of the persistent word and private memory. -/
def ExternalOnly : Instr w p r k → Prop
  | .stateWord .. | .loadPrivate .. | .storePrivate .. => False
  | _ => True

variable (pc : Fin p ↪ Fin P) (reg : Fin r ↪ Fin R)

private def Agrees (c : Config w P R) (s : Config w p r) : Prop :=
  c.pc = pc s.pc ∧ ∀ j, c.reg (reg j) = s.reg j

private theorem agrees_put {c : Config w P R} {s : Config w p r}
    (h : Agrees pc reg c s) (n : Fin p) (a : Fin r) (v : Word w) :
    Agrees pc reg (c.put (pc n) (reg a) v) (s.put n a v) := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases e : j = a
  · subst j
    simp [Config.put]
  · simp [Config.put, Function.update_of_ne e, Function.update_of_ne (reg.injective.ne e), h.2]

private theorem agrees_at {c : Config w P R} {s : Config w p r}
    (h : Agrees pc reg c s) (n : Fin p) :
    Agrees pc reg {c with pc := pc n} {s with pc := n} := ⟨rfl, h.2⟩

variable {F : Type*} [Semiring F]

private def afterAction {C : Type*} (code : FieldCode F w)
    (cont : C → Memory w → F) (m : Memory w) : CallAction w C → F
  | .localStep c => cont c m
  | .branch c => cont (c false) m + cont (c true) m
  | .read a c => cont (c (m a.val)) m
  | .write a v c => cont c (writeMemory m a v)
  | .finish v => code.terminal v
  | .reject => 0

private theorem mass_succ {C : Type*} (code : FieldCode F w) (P : Program w C)
    (t : ℕ) (c : C) (m : Memory w) :
    mass code P (t+1) c m = afterAction code (mass code P t) m (P.step c) := by
  rw [mass]; cases P.step c <;> rfl

private theorem after_relocate (pub : Fin k → Fin K) (param : Fin k → Word w)
    (callerParam : Fin K → Word w) (hpub : ∀ i, callerParam (pub i) = param i)
    (code : FieldCode F w) (f : Config w P R → Memory w → F)
    (g : Config w p r → Memory w → F)
    (ih : ∀ c s m, Agrees pc reg c s → f c m = g s m)
    (c : Config w P R) (s : Config w p r) (m : Memory w) (h : Agrees pc reg c s)
    (i : Instr w p r k) (hi : ExternalOnly i) :
    afterAction code f m ((relocate pc reg pub i).run callerParam c) =
      afterAction code g m (i.run param s) := by
  cases i <;> first | contradiction | skip
  all_goals simp only [relocate, Instr.run, afterAction, hpub, h.2, Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | rfl
    | exact ih _ _ _ (agrees_put pc reg h _ _ _)
    | exact ih _ _ _ (agrees_at pc reg h _)
    | exact congrArg₂ (· + ·) (ih _ _ _ (agrees_at pc reg h _)) (ih _ _ _ (agrees_at pc reg h _))
    | split <;> exact ih _ _ _ (agrees_at pc reg h _)


/-- Installing every row preserves the weighted value from matching counters
and registers, with arbitrary persistent words and private memories. -/
theorem mass_eq (pub : Fin k → Fin K) (native : Machine w p r k) (caller : Machine w P R K)
    (allowed : ∀ i, ExternalOnly (native.code i))
    (rows : ∀ i, caller.code (pc i) = relocate pc reg pub (native.code i))
    (params : ∀ i, caller.publicData (pub i) = native.publicData i)
    (code : FieldCode F w) (fuel : ℕ) (c : Config w P R) (s : Config w p r)
    (m : Memory w) (atPC : c.pc = pc s.pc) (regs : ∀ i, c.reg (reg i) = s.reg i) :
    mass code caller.program fuel c m = mass code native.program fuel s m := by
  suffices sim : ∀ t (C : Config w P R) (S : Config w p r) (mem : Memory w),
      Agrees pc reg C S → mass code caller.program t C mem = mass code native.program t S mem by
    exact sim fuel c s m ⟨atPC, regs⟩
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro C S mem h
    calc
      _ = afterAction code (mass code caller.program t) mem ((caller.code C.pc).run caller.publicData C) :=
        mass_succ code caller.program t C mem
      _ = afterAction code (mass code native.program t) mem ((native.code S.pc).run native.publicData S) := by
        rw [h.1, rows]
        exact after_relocate pc reg pub native.publicData caller.publicData params code _ _ ih
          C S mem h _ (allowed S.pc)
      _ = _ := (mass_succ code native.program t S mem).symm

/-- The injected register bank is initially zero at the installed entry
counter. The caller may carry other registers, private memory and a persistent word. -/
theorem mass_eq_value (pub : Fin k → Fin K) (native : Machine w p r k) (caller : Machine w P R K)
    (allowed : ∀ i, ExternalOnly (native.code i))
    (rows : ∀ i, caller.code (pc i) = relocate pc reg pub (native.code i))
    (params : ∀ i, caller.publicData (pub i) = native.publicData i)
    (code : FieldCode F w) (fuel : ℕ) (c : Config w P R) (state : Word w) (m : Memory w)
    (atEntry : c.pc = pc native.entry) (zero : ∀ i, c.reg (reg i) = 0) :
    mass code caller.program fuel c m = value code native fuel state m :=
  mass_eq pc reg pub native caller allowed rows params code fuel c (native.program.start state) m
    atEntry zero

end ThreeFlat.RAM.NativeRelocate

end OAI
