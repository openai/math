import OAI.Computability.VPVNP.PrimedInputRAMOpcodes
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.PrimedInputRAMLayoutExecution
import OAI.Computability.VPVNP.PrimedInputRAMDispatch

/-!
# Loading the parameters and decoding the persistent rectangle cursor

The three cut-length words are fetched from external memory on every data
call. Group numbers are only row selectors here: the bits of the actual
large group index are fetched at the designated header addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

private abbrev lit (w k : ℕ) : Word w := Fin.ofNat (2^w) k

/-- Trace of parameter loading, with eighteen private ticks followed by reads of the left,
middle and right cut lengths at addresses 0, 1 and 2. -/
def parameterEvents (w : ℕ) (mem : Memory w) : List (Event w) :=
  List.replicate 18 .tick ++ [.read (lit w 0) (mem (lit w 0).val),
    .read (lit w 1) (mem (lit w 1).val), .read (lit w 2) (mem (lit w 2).val)]

/-- Register state after the parameter loads. -/
structure Loaded (pub : Pub → Word w) (state : Word w) (mem : Memory w) (rs : Regs w 48) : Prop where
  zero : rs 0 = lit w 0
  one : rs 1 = lit w 1
  two : rs 2 = lit w 2
  three : rs 3 = lit w 3
  cursor : rs 4 = state
  cells : rs 5 = pub 0
  rowWidth : rs 6 = pub 1
  sites : rs 7 = pub 2
  siteBits : rs 8 = pub 3
  wordWidth : rs 9 = pub 4
  bucket : rs 10 = pub 5
  base : rs 11 = pub 6
  prefixWidth : rs 12 = pub 7
  incident : rs 13 = pub 8
  indexWidth : rs 14 = pub 9
  adviceWidth : rs 15 = pub 10
  cutCapacity : rs 16 = pub 11
  prefixWord : rs 17 = pub 12
  left : rs 18 = mem (lit w 0).val
  middle : rs 19 = mem (lit w 1).val
  right : rs 20 = mem (lit w 2).val

private def loadedRegs (pub : Pub → Word w) (state : Word w) (mem : Memory w) (rs : Regs w 48) : Regs w 48 :=
  let cells : List (Reg × Word w) :=
    [(0,lit w 0),(1,lit w 1),(2,lit w 2),(3,lit w 3),(4,state),
      (5,pub 0),(6,pub 1),(7,pub 2),(8,pub 3),(9,pub 4),(10,pub 5),(11,pub 6),
      (12,pub 7),(13,pub 8),(14,pub 9),(15,pub 10),(16,pub 11),(17,pub 12),
      (18,mem (lit w 0).val),(19,mem (lit w 1).val),(20,mem (lit w 2).val)]
  cells.foldl (fun regs j ↦ Function.update regs j.1 j.2) rs

private theorem extendOps {pub : Pub → Word w} {state : Word w} {rs ra : Regs w 48} {m ma : Memory w}
    {a : Code} {es : List (Event w)} (h : Flow.Exec pub state a rs m es ra ma)
    (ops : List (Op 48 16)) {fs rb mb}
    (ht : trace pub state ops ra ma = some (fs,rb,mb)) :
    Flow.Exec pub state (ops.foldl (fun c op ↦ .seq c (.line op)) a) rs m (es++fs) rb mb := by
  induction ops generalizing es a ra ma fs with
  | nil =>
    have he : ([],ra,ma) = (fs,rb,mb) := Option.some.inj ht
    cases he
    simpa using h
  | cons o ops ih =>
    simp only [trace, bind, Option.bind_eq_some_iff] at ht
    obtain ⟨⟨e,rc,mc⟩,ho,⟨ts,rd,md⟩,hr,hf⟩ := ht
    cases hf
    simpa [List.append_assoc] using ih (h.seq (.line ho)) hr

theorem loadParameters_exec (pub : Pub → Word w) (state : Word w) (mem : Memory w) (rs : Regs w 48) :
    ∃ out, Flow.Exec pub state loadParameters rs mem (parameterEvents w mem) out mem ∧
      Loaded pub state mem out := by
  let ra := Function.update rs (0 : Reg) (lit w 0)
  let out := loadedRegs pub state mem rs
  have head : Flow.Exec pub state (set 0 0) rs mem [.tick] ra mem := .line rfl
  have ht : trace pub state parameterTail ra mem =
      some (List.replicate 17 .tick ++
        [.read (lit w 0) (mem (lit w 0).val), .read (lit w 1) (mem (lit w 1).val),
          .read (lit w 2) (mem (lit w 2).val)], out, mem) := rfl
  exact ⟨out, extendOps head parameterTail ht, by constructor <;> rfl⟩

/-- Register state after decoding the persistent cursor into the rectangle index, row, group,
site, bit offset, successor cursor and destination address. -/
def cursorRegs (rs : Regs w 48) : Regs w 48 :=
  let i := BinaryOp.mod.eval (rs 4) (rs 5)
  let row := BinaryOp.div.eval i (rs 6)
  let g := BinaryOp.div.eval row (rs 7)
  let v := BinaryOp.mod.eval row (rs 7)
  let j := BinaryOp.mod.eval i (rs 6)
  let next := BinaryOp.add.eval (rs 4) (rs 1)
  let dest := BinaryOp.add.eval (rs 11) (rs 4)
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update rs (21 : Fin 48) i) 31 row) 22 g) 23 v) 24 j) 29 next) 30 dest

theorem unpackCursor_exec (pub : Pub → Word w) (state : Word w) (mem : Memory w) (rs : Regs w 48) :
    Flow.Exec pub state unpackCursor rs mem (List.replicate 7 .tick) (cursorRegs rs) mem :=
  (Flow.once_sound pub state false unpackCursor rs mem rfl).1

/-- Rectangle coordinates in the bounded output registers. -/
structure Cursor (n r base : ℕ) (state : Word w) (rs : Regs w 48) : Prop where
  index : (rs 21).val = state.val % positions n r
  group : (rs 22).val = state.val % positions n r / n / (2^r)
  site : (rs 23).val = state.val % positions n r / n % (2^r)
  bit : (rs 24).val = state.val % positions n r % n
  next : (rs 29).val = state.val + 1
  dest : (rs 30).val = base + state.val

private theorem div_val (x y : Word w) : (BinaryOp.div.eval x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) x.isLt)

private theorem mod_val (x y : Word w) : (BinaryOp.mod.eval x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le ..) x.isLt)

theorem cursorRegs_spec {n r base : ℕ} (rs : Regs w 48) (state : Word w)
    (h₁ : (rs 1).val = 1) (hs : rs 4 = state) (hN : (rs 5).val = positions n r)
    (hn : (rs 6).val = n) (hR : (rs 7).val = 2^r) (hb : (rs 11).val = base)
    (hnext : state.val + 1 < 2^w) (hdest : base + state.val < 2^w) :
    Cursor n r base state (cursorRegs rs) := by
  have hne : (rs 4).val + (rs 1).val < 2^w := by simpa [hs, h₁] using hnext
  have hde : (rs 11).val + (rs 4).val < 2^w := by simpa [hb, hs] using hdest
  have addVal (a b : Word w) (h : a.val+b.val < 2^w) :
      (BinaryOp.add.eval a b).val = a.val + b.val := Fin.val_add_eq_of_add_lt h
  constructor
  · change (BinaryOp.mod.eval (rs 4) (rs 5)).val = _
    rw [mod_val, hs, hN]
  · change (BinaryOp.div.eval (BinaryOp.div.eval (BinaryOp.mod.eval (rs 4) (rs 5)) (rs 6)) (rs 7)).val = _
    rw [div_val, div_val, mod_val, hs, hN, hn, hR]
  · change (BinaryOp.mod.eval (BinaryOp.div.eval (BinaryOp.mod.eval (rs 4) (rs 5)) (rs 6)) (rs 7)).val = _
    rw [mod_val, div_val, mod_val, hs, hN, hn, hR]
  · change (BinaryOp.mod.eval (BinaryOp.mod.eval (rs 4) (rs 5)) (rs 6)).val = _
    rw [mod_val, mod_val, hs, hN, hn]
  · change (BinaryOp.add.eval (rs 4) (rs 1)).val = _
    rw [addVal _ _ hne, hs, h₁]
  · change (BinaryOp.add.eval (rs 11) (rs 4)).val = _
    rw [addVal _ _ hde, hb, hs]

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
