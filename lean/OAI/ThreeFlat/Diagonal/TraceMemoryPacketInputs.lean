import OAI.ThreeFlat.Diagonal.TraceInputCircuit
import OAI.ThreeFlat.Diagonal.TracePhysicalAddress
import OAI.ThreeFlat.Diagonal.TraceClockSites
import OAI.ThreeFlat.Diagonal.TraceMemoryCircuit
import OAI.ThreeFlat.Diagonal.TraceFormulaPacket

namespace OAI
/-! # Raw CPU, header, and shared sorting pins feeding one memory-check site -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM RAMSerialization BooleanTranscript
open TraceBanks TraceWords TraceSlots TraceRows TraceCompose
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w r f S d : ℕ}

abbrev LocalPort := TracePhysical.Port

def literal {σ : Type*} (v : Bool) : Packet σ := ⟨0,.mk .nil (.const v)⟩
def read {σ : Type*} (i : σ) : Packet σ := ⟨0,.mk .nil (.var i)⟩

def cpuPin (s : Fin 3) (j : Fin ((5+r)*(w+1))) : LocalPort w r d := .inl (s,j)
def cpuExpr (s : Fin 3) (jk : CodePin w r) : Expr (LocalPort w r d) :=
  .input (cpuPin s (finProdFinEquiv jk))

def headerExpr (s : Fin 2) (j : Fin (w+1)) : Expr (LocalPort w r d) :=
  Fin.snoc (α := fun _ => Expr (LocalPort w r d))
    (fun k => .input (.inr (.inl (s,k)))) (.const false) j

/-- First-layer record bit or neighboring shared send bit at a particular
memory-check circuit input. The formulas depend only on the public slot
number and the raw header or CPU bits local to that position. -/
noncomputable def memoryInput (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (v : Fin (2^d)) :
    TraceMemoryCircuit.Port d (w+1) → Packet (LocalPort w r d)
  | .inl (s,field,j) =>
    if h : slotAddress d v s < S then
      TracePair.formulaPacket (initKey (wide (⟨slotAddress d v s, h.trans_le hs⟩ : Word w))
        (headerExpr s) field j)
    else if hstep : slotAddress d v s-S < f then
      TracePair.formulaPacket (probeKey hw (cpuExpr s.castSucc) ⟨slotAddress d v s-S,hstep.trans_le hf⟩
        field j)
    else literal (bits (fields (by omega) (none : Option (WordRecord (w+1))) field) j)
  | .inr (.inl (l,b,s,field,j)) => read (.inr (.inr (.inl (l,b,s,finProdFinEquiv (field,j)))))
  | .inr (.inr (b,field,j)) => read (.inr (.inr (.inr (b,finProdFinEquiv (field,j)))))

/-- Observe the whole dependent packet before reducing the choice of record form.
The number of gates depends on that choice. -/
theorem initialInput_eval (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (s : Fin 2) (g : Fin 7) (j : Fin (w+1)) (x : LocalPort w r d → Bool) :
    (memoryInput hw hs hf v (.inl (s,g,j))).2.eval x =
      if h : slotAddress d v s < S then
        (initKey (wide (⟨slotAddress d v s,h.trans_le hs⟩ : Word w)) (headerExpr s) g j).eval x
      else if h : slotAddress d v s-S < f then
        (probeKey hw (cpuExpr s.castSucc) ⟨slotAddress d v s-S,h.trans_le hf⟩ g j).eval x
      else bits (fields (by omega) (none : Option (WordRecord (w+1))) g) j := by
  let observe := fun z : Packet (LocalPort w r d) => z.2.eval x
  change observe (memoryInput hw hs hf v (.inl (s,g,j))) = _
  by_cases h : slotAddress d v s < S
  · rw [dite_eq_left h]
    simp only [memoryInput, dite_eq_left h]
    exact TracePair.formulaPacket_eval ..
  · rw [dite_eq_right h]
    simp only [memoryInput,dite_eq_right h]
    by_cases t : slotAddress d v s-S < f
    · simp only [dite_eq_left t]
      exact TracePair.formulaPacket_eval ..
    · simp only [dite_eq_right t]
      rfl

noncomputable def memoryPacket (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (v : Fin (2^d)) :
    Packet (LocalPort w r d) :=
  substituteFintype (memoryInput hw hs hf v) ((TraceMemoryCircuit.row (by omega) v).circuit ())

@[simp] theorem memoryPacket_eval (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (x : LocalPort w r d → Bool) :
    (memoryPacket hw hs hf v).2.eval x = ((TraceMemoryCircuit.row (by omega) v).circuit ()).eval
      (fun i => (memoryInput hw hs hf v i).2.eval x) :=
  substituteFintype_eval ..

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
