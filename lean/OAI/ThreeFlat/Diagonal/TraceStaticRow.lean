import OAI.ThreeFlat.Diagonal.TraceStaticPorts
import OAI.ThreeFlat.Diagonal.TraceStaticMemory
import OAI.ThreeFlat.Diagonal.TraceUniformPackets
import OAI.ThreeFlat.Diagonal.TracePacketArray
import OAI.ThreeFlat.Diagonal.TraceUniformEntry

namespace OAI
/-! # One polynomial Boolean gate table for every physical row -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM TraceWords TraceRows TraceBanks TraceCompose
open TraceRowPackets TraceProgram TraceUniformRow
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

noncomputable def liftPort {α β : Type*} [Fintype α] (inc : α → β) (z : Packet α) : Packet β :=
  substituteFintype (fun a => read (inc a)) z.2

@[simp] theorem liftPort_eval {α β : Type*} [Fintype α] (inc : α → β) (z : Packet α) (x : β → Bool) :
    (liftPort inc z).2.eval x = z.2.eval (x ∘ inc) := substituteFintype_eval ..

@[simp] theorem liftPort_count {α β : Type*} [Fintype α] (inc : α → β) (z : Packet α) :
    (liftPort inc z).1 = z.1 := by simp [liftPort,substituteFintype_size,TraceRowPackets.read]

private def selectFormula : Expr (Fin 3) := Expr.mux (.input 0) (.input 1) (.input 2)

noncomputable def select {σ : Type*} (flag yes no : Packet σ) : Packet σ :=
  substituteFintype ![flag,yes,no] (TracePair.formulaPacket selectFormula).2

@[simp] theorem select_eval {σ : Type*} (flag yes no : Packet σ) (x : σ → Bool) :
    (select flag yes no).2.eval x = if flag.2.eval x then yes.2.eval x else no.2.eval x := by
  by_cases h : flag.2.eval x = true <;> simp [select,selectFormula,Expr.eval_mux,Expr.eval,h]

theorem select_count {σ : Type*} (flag yes no : Packet σ) :
    (select flag yes no).1 ≤ flag.1 + yes.1 + no.1 + 100 := by
  have h := TracePair.formulaPacket_size_le selectFormula
  have hs : 4*selectFormula.size ≤ 100 := by decide
  rw [select,substituteFintype_size,Fin.sum_univ_three]
  change flag.1 + yes.1 + no.1 + _ ≤ _
  omega

def flag (c : Outer w p k) : Packet (Port w p r k d) := read (.inr (.inr c))

def cpuArg (s : Fin 2) (j : Fin ((5+r)*(w+1))) : Port w p r k d := .inl (.inl (cpuPin s.castSucc j))

def memoryPort : LocalPort w r d ⊕ MemoryControl w d → Port w p r k d
  | .inl j => .inl (.inl j)
  | .inr j => .inr (.inl j)

def ordinaryPort (j : TraceUniformRow.Port w p r k d) : Port w p r k d := .inl j

/-- This packet table depends only on the public lengths, never on a row
number or a setting of the program/data pins. All per-row control is
concentrated in the public input bits in ctrlAt. -/
noncomputable def template (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base f : ℕ) (st : Word w) : Check F w p k → Packet (Port w p r k d)
  | .inl (.inl ()) => liftPort memoryPort (staticMemory hw)
  | .inl (.inr (s,.inl j)) =>
    match j.val with
    | 0 => select (flag (.inl s))
      (substituteFintype (fun jk => read (cpuArg s (finProdFinEquiv jk))) ((canonicalFrame hw hp).circuit ())) (literal true)
    | 1 => select (flag (.inl s))
      (liftPort ordinaryPort (substituteFintype (joint s) (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).2)) (literal true)
    | _ => select (flag (.inr (.inl s))) (liftPort ordinaryPort (TracePair.formulaPacket
      (startFromText hp textExpr (fun j => .const (bits (wide st) j)) (cpuExpr' s)))) (literal (decide (0 < f)))
  | .inl (.inr (s,.inr i)) => select (flag (.inl s))
      (substituteFintype (fun j => read (cpuArg s j)) ((TraceTerminal.rowFrame hF hw r).circuit i)) (literal i.isNone)
  | .inr (.inl ()) => select (flag (.inr (.inr (.inl false))))
      (liftPort (fun j => ordinaryPort (copyPin false j)) (headerCircuit w p k)) (literal true)
  | .inr (.inr (j,true)) =>
    select (flag (.inr (.inr (.inl true)))) (TracePair.formulaPacket
      (same (.input (.inl (copyPin false j))) (.input (.inl (copyPin true j))))) (literal true)
  | .inr (.inr (j,false)) =>
    let s : Fin 2 := ⟨(base+(finProdFinEquiv j).val)%2,Nat.mod_lt _ (by decide)⟩
    select (flag (.inr (.inr (.inr j)))) (TracePair.formulaPacket
      (same (.input (.inl (copyPin false j))) (.input (.inl (.inl (.inr (.inl (s,⟨0,by omega⟩)))))))) (literal true)

@[simp] theorem flag_at (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (base : ℕ)
    (v : Fin (2^d)) (x : TraceUniformRow.Port w p r k d → Bool) (j : Outer w p k) :
    (flag j).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) = outerAt base S f v j := rfl

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
