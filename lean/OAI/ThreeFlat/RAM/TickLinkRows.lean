import OAI.ThreeFlat.RAM.OrdinalOpLoop

namespace OAI
/-! # Three fixed row kernels for streaming the raw tick predecessor links -/

namespace ThreeFlat.RAM.TickLinkRows

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM PhysicalProcedure
open scoped Fin.CommRing

structure Plan where
  cells : ℕ
  sources : ℕ
  rawBase : ℕ
  lastBase : ℕ
  prevBase : ℕ
  dstBase : ℕ

def Plan.sockets (P : Plan) := 3*P.cells

def Plan.data (P : Plan) (w : ℕ) : Fin 9 → Word w :=
  ![(P.sources : Word w), (P.sockets : Word w), (P.rawBase : Word w),
    (P.lastBase : Word w), (P.prevBase : Word w), (P.dstBase : Word w),
    ((P.cells+P.sources : ℕ) : Word w), ((P.cells+P.sources+P.sockets : ℕ) : Word w), 11]

inductive Phase where | init | socket | tail

def Phase.limit : Phase → Fin 9
  | .socket => 1
  | _ => 0

def Phase.count (P : Plan) : Phase → ℕ
  | .socket => P.sockets
  | _ => P.sources

private def bump : List (Op 8 9) := [.constant 7 1, .binary .add 0 0 7]

/-- Registers zero and one are the ordinal and exclusive bound. Registers two
through seven are scratch. All size-dependent constants come from public data. -/
def Phase.ops : Phase → List (Op 8 9)
  | .init => [.publicWord 2 3, .binary .add 2 2 0, .write 2 0] ++ bump
  | .socket =>
    [.constant 4 3, .binary .div 2 0 4, .publicWord 3 8, .binary .mul 2 3 2,
     .binary .mod 4 0 4, .binary .add 2 2 4, .publicWord 3 2, .binary .add 2 3 2,
     .read 2 2, .publicWord 5 3, .binary .add 5 5 2, .read 4 5,
     .publicWord 6 4, .binary .add 6 6 0, .write 6 4,
     .publicWord 6 5, .binary .add 6 6 4, .publicWord 3 6, .binary .add 3 3 0, .write 6 3,
     .publicWord 3 0, .binary .add 3 3 0, .write 5 3] ++ bump
  | .tail =>
    [.publicWord 2 3, .binary .add 2 2 0, .read 2 2, .publicWord 3 5,
     .binary .add 2 3 2, .publicWord 3 7, .binary .add 3 3 0, .write 2 3] ++ bump

variable {w r k : ℕ}

def action (ph : Phase) (v : Fin 9 → Word w) (i : Word w) (m : Memory w) : Memory w :=
  match ph with
  | .init => writeMemory m (v 3 + i) i
  | .socket =>
    let raw := v 2 + (v 8 * BinaryOp.eval .div i 3 + BinaryOp.eval .mod i 3)
    let ptr := v 3 + m raw.val
    let old := m ptr.val
    let a := writeMemory m (v 4 + i) old
    let b := writeMemory a (v 5 + old) (v 6 + i)
    writeMemory b ptr (v 0 + i)
  | .tail => writeMemory m (v 5 + m (v 3 + i).val) (v 7 + i)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem trace_row (ph : Phase) (reg : Fin 8 ↪ Fin r) (pub : Fin 9 → Fin k)
    (data : Fin k → Word w) (state : Word w) (rs : Regs w r) (m : Memory w) :
    ∃ es out, trace data state (ph.ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out, action ph (data ∘ pub) (rs (reg 0)) m) ∧
      out (reg 0) = rs (reg 0)+1 ∧ out (reg 1) = rs (reg 1) := by
  cases ph <;> simp [Phase.ops,bump,OrdinalOpLoop.relocate,trace,Op.effect,action,BinaryOp.eval,
    Function.update,reg.injective.eq_iff]

def image (ph : Phase) (P : Plan) (start : Memory w) : ℕ → Memory w
  | 0 => start
  | i+1 => action ph (P.data w) (i : Word w) (image ph P start i)

def procedure (w : ℕ) (P : Plan) (ph : Phase) : Procedure w where
  labels := 3+ph.ops.length
  registers := 8
  slots := 9
  block := OrdinalOpLoop.block w ph.ops 0 1 ph.limit
  publicData := P.data w

def cost (P : Plan) (ph : Phase) := 3+ph.count P*(1+ph.ops.length)

theorem phase_spec (P : Plan) (ph : Phase) (fit : ph.count P < 2^w) :
    (procedure w P ph).Spec (fun _ => True)
      (fun m out => out = image ph P m (ph.count P)) (cost P ph) := by
  intro pcs regs pubs M pc reg pub exit installed data cfg m entry _
  change Fin 9 → Fin pubs at pub
  change Fin 8 ↪ Fin regs at reg
  change ∀ i : Fin 9, M.publicData (pub i) = P.data w i at data
  have params : M.publicData ∘ pub = P.data w := funext data
  have count : M.publicData (pub ph.limit) = ((ph.count P : ℕ) : Word w) := by
    exact (data ph.limit).trans (by cases ph <;> rfl)
  obtain ⟨out,act,atExit⟩ := OrdinalOpLoop.advance_block ph.ops 0 1 (by decide) ph.limit
    M pc reg pub exit installed (ph.count P) fit count (image ph P m) (by
      intro i _ state rs cur bd
      obtain ⟨es,out,tr,inc,kept⟩ := trace_row ph reg pub M.publicData state rs (image ph P m i)
      refine ⟨es,out,?_,?_,kept.trans bd⟩
      · simpa only [image,params,cur] using tr
      · simpa [cur] using inc) cfg entry
  exact ⟨_,le_rfl,out,_,act,atExit,rfl⟩

def builder (w : ℕ) (P : Plan) := ((procedure w P .init).seq (procedure w P .socket)).seq (procedure w P .tail)

@[simp] theorem builder_labels (P : Plan) : (builder w P).labels = 49 := rfl
@[simp] theorem builder_registers (P : Plan) : (builder w P).registers = 24 := rfl
@[simp] theorem builder_slots (P : Plan) : (builder w P).slots = 27 := rfl

def output (P : Plan) (m : Memory w) :=
  image .tail P (image .socket P (image .init P m P.sources) P.sockets) P.sources

/-- All three loops have constant program size and total runtime linear in cells and sources. -/
theorem builder_spec (P : Plan) (sfit : P.sources < 2^w) (kfit : P.sockets < 2^w) :
    (builder w P).Spec (fun _ => True) (fun m o => o = output P m)
      (9+17*P.sources+26*P.sockets) := by
  have a : (procedure w P .init).Spec _ _ _ := @phase_spec w P .init sfit
  have b : (procedure w P .socket).Spec _ _ _ := @phase_spec w P .socket kfit
  have d : (procedure w P .tail).Spec _ _ _ := @phase_spec w P .tail sfit
  apply Procedure.Spec.mono (Procedure.Spec.seq (Procedure.Spec.seq a b (fun _ _ _ => trivial))
    d (fun _ _ _ => trivial)) (fun _ _ => trivial)
  · rintro m out ⟨mid,⟨old,rfl,rfl⟩,rfl⟩
    rfl
  · change (3+P.sources*6)+(3+P.sockets*26)+(3+P.sources*11) ≤ _
    omega

end ThreeFlat.RAM.TickLinkRows

end OAI
