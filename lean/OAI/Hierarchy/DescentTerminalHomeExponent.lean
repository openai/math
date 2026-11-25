import OAI.Hierarchy.DescentTerminalHomePrefix
import OAI.Hierarchy.DescentPrivateExponentRAM
import OAI.Hierarchy.ProtocolRAMStaticSlotCheap

namespace OAI
/-! # Resolve the terminal field exponent from the measured home and path counts -/
namespace Hierarchy.DescentTerminalVertexFields.PrivateCounter
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A p groups blocks homes bw : ℕ} (C : Banks (blocks:=blocks)) (O : DescentPrivateExponentRAM.Banks)
local notation "capacity" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "cells" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) C.layout
local notation "low" => (C.base+capacity)+homes
local notation "counted" => prefixImage (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C
local notation "cost" => prefixTicks homes blocks capacity
local notation "countCode" => «prefix» (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C bw homes

def machine := (countCode).seq (O.program bw p)

def final (m : Memory bw) :=
  O.result p (∑i : Fin homes,privateHome (cells m i)) (counted m)

/-- The actual native scans leave every older word intact except their two
named scalar registers. This also covers higher memory outside their arena. -/
theorem final_frame (m : Memory bw) (x : ℕ) (old : x<C.base ∨ low+homes<x)
    (temp : x≠O.usedBits) (out : x≠O.deadBits) :
    final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C O m x=m x :=
  (O.frame p _ (counted m) x temp out).trans (prefix_frame C m x old)

private theorem append_exponent (P : Procedure bw) (m after : Memory bw) (ticks used : ℕ)
    (run : P.Exec m after ticks) (cheap : CheapCode P) (scale : O.Room bw)
    (seen : after O.usedWords=(used : Word bw)) :
    (P.seq (O.program bw p)).Exec m (O.result p used after) (ticks+(56+4*ProtocolRAMPortScale.bitWidth p)) ∧
      CheapCode (P.seq (O.program bw p)) := by
  constructor
  · rw [←DescentPrivateExponentRAM.steps_eq O p]
    exact @Procedure.Exec.then bw P (O.program bw p) m after (O.result p used after) ticks (O.steps p)
      (@run) (@DescentPrivateExponentRAM.Banks.run bw O p used after scale seen)
  · exact @cheap_seq bw P (O.program bw p) (@cheap)
      (@cheap_seq bw _ _
        (@ProtocolRAMStaticPortCheap.base bw O.usedBits 1 p (DescentPrivateEdgeCounter.cell O.usedWords))
        (@scan_cheap bw O.deadBits 1 O.minus))

/-- Regardless of values in any primitive cohort, a physically mounted
shift table and the static address room give a complete fixed-time run. -/
theorem any (m : Memory bw)
    (space : Room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C bw)
    (shift : Shift (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C.layout m)
    (room : low+homes+1<2^bw) (scale : O.Room bw) (dest : O.usedWords=low+homes) :
    let code:=machine (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) (bw:=bw) C O
    let out:=final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C O m
    code.Exec m out (cost+(56+4*ProtocolRAMPortScale.bitWidth p)) ∧ CheapCode code := by
  let occupied := ∑ i : Fin homes, privateHome (cells m i)
  obtain ⟨first,used,_,cheap⟩ := @prefix_run q t H N A p groups blocks homes bw C m space shift room
  have seen : counted m O.usedWords = (occupied : Word bw) := by
    rw [dest]
    exact used
  exact append_exponent (p:=p) O countCode m (counted m) cost occupied (@first) (@cheap) scale seen

theorem exponent (m : Memory bw) (allBits : ℕ)
    (space : Room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C bw)
    (shift : Shift (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C.layout m)
    (room : low+homes+1<2^bw) (scale : O.Room bw) (header : O.totalBits<C.base)
    (dest : O.usedWords=low+homes) (held : m O.totalBits=(allBits:Word bw))
    (enough : (∑i : Fin homes,privateHome (cells m i))*p≤allBits) :
    let code:=machine (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) (bw:=bw) C O
    let out:=final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C O m
    code.Exec m out (cost+(56+4*ProtocolRAMPortScale.bitWidth p)) ∧ CheapCode code ∧
    out O.deadBits=((allBits-(∑i : Fin homes,privateHome (cells m i))*p:ℕ):Word bw) := by
  obtain ⟨ran, cheap⟩ := any C O m space shift room scale dest
  have preserved : counted m O.totalBits = (allBits : Word bw) :=
    (prefix_frame C m O.totalBits (.inl header)).trans held
  exact ⟨@ran, @cheap, O.read p _ allBits (counted m) scale preserved enough⟩


end
end Hierarchy.DescentTerminalVertexFields.PrivateCounter

end OAI
