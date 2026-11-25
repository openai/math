import OAI.ThreeFlat.Diagonal.TraceUniformAddress
import OAI.ThreeFlat.Diagonal.TraceUniformEntry
import OAI.ThreeFlat.Diagonal.TraceUniformCircuit
import OAI.ThreeFlat.Diagonal.TraceRowPackets

namespace OAI
/-! # A single row verifier with no instruction contents built into its gates -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization BooleanTranscript
open Computability.VPVNP.VerifierNetwork (Frame)
open TraceWords TraceRows TraceBanks TraceCompose TraceRowPackets TraceProgram
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} [Fintype F] [CommRing F] {w p r k d S f : ℕ}

def zeroPc (h : 0 < p) : Fin p := ⟨0,h⟩

private def dummy (hp0 : 0 < p) : Machine w p r k :=
  ⟨zeroPc hp0, fun _ => .reject, fun _ => 0⟩

noncomputable def ordinary (x : Packet (LocalPort w r d)) : Packet (Port w p r k d) :=
  substituteFintype (fun a => read (.inl a)) x.2

@[simp] theorem ordinary_eval (a : Packet (LocalPort w r d)) (x : Port w p r k d → Bool) :
    (ordinary a).2.eval x = a.2.eval (x ∘ Sum.inl) := substituteFintype_eval ..

def copyPin (future : Bool) (j : Text w p k) : Port w p r k d := Sum.inr (future,j)

def textExpr (j : Fin w) : Expr (Port w p r k d) := .input (copyPin false (⟨0,by omega⟩,j))

def cpuExpr' (s : Fin 2) (j : CodePin w r) : Expr (Port w p r k d) :=
  .input (.inl (cpuPin s.castSucc (finProdFinEquiv j)))

noncomputable def joint (s : Fin 2) : Input w p r k → Packet (Port w p r k d)
  | .inl j => ordinary (pairRead s j)
  | .inr j => read (copyPin false j)

/-- Every local factor outside instruction dispatch and initial counter
validation uses the identical text-independent circuit as the fixed program. -/
noncomputable def dynamic (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (a : Factor F) : Packet (Port w p r k d) :=
  match a with
  | .inr (s,.inl j) =>
    match j.val with
    | 1 =>
      if S ≤ slotAddress d v s ∧ slotAddress d v s-S < f then
        substituteFintype (joint s) (uniformPair (w:=w) (r:=r) (p:=p) (k:=k)).2
      else literal true
    | 2 =>
      if slotAddress d v s = S ∧ 0 < f then
        TracePair.formulaPacket (startFromText hp textExpr (fun j => .const (bits (wide st) j)) (cpuExpr' s))
      else literal (decide (0 < f))
    | _ => ordinary (packet hF hw hp (dummy (w:=w) (r:=r) (k:=k) hp0) st hs hf v a)
  | _ => ordinary (packet hF hw hp (dummy (w:=w) (r:=r) (k:=k) hp0) st hs hf v a)

/-- A copy bundle supplies the physical input values at this row. On the
last row future-copy wires have the fixed value false. -/
def valuation (hw : 2 ≤ w+1) (v : Fin (2^d)) (header : Fin S → Word w)
    (cpu : CpuBits w r f) (z : SortBits d (w+1)) (copies : Fin (2^d) → Text w p k → Bool) :
    Port w p r k d → Bool :=
  Sum.elim (TracePhysical.valuation hw v header cpu z) (fun q =>
    if q.1 then if h : v.val+1 < 2^d then copies ⟨_,h⟩ q.2 else false else copies v q.2)

/-- An independently invalid program entry contributes zero. All rows with
positive index use the unit weight for this validity check. -/
noncomputable def programHeader (v : Fin (2^d)) : Packet (Port w p r k d) :=
  if v.val = 0 then substituteFintype (fun j => read (copyPin false j)) (headerCircuit w p k).2
  else literal true

/-- Each text bit is anchored at the physical row that contains its low
word bit. A second test relays that bit to the next physical row. -/
noncomputable def relay (hw : 0 < w) (base : ℕ) (v : Fin (2^d)) (j : Text w p k)
    (outgoing : Bool) : Packet (Port w p r k d) :=
  let idx := base+(finProdFinEquiv j).val
  let own : Expr (Port w p r k d) := .input (copyPin false j)
  if outgoing then
    if v.val+1 < 2^d then TracePair.formulaPacket (same own (.input (copyPin true j)))
    else literal true
  else if idx/2 = v.val then
    let h : Fin 2 := ⟨idx%2,Nat.mod_lt _ (by decide)⟩
    TracePair.formulaPacket (same own (.input (.inl (.inr (.inl (h,⟨0,hw⟩))))))
  else literal true

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
