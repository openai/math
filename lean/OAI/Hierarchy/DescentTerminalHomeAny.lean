import OAI.Hierarchy.DescentTerminalHomeExponent
import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentPrivateHomeClock

namespace OAI
/-! # Terminal execution on an arbitrary initial RAM -/
namespace Hierarchy.DescentTerminalVertexFields.PrivateCounter
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {q t H N A p groups blocks homes bw : ℕ} (C : Banks (blocks:=blocks))
local notation "capacity" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "tab" => menu (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C
local notation "phase" => program (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C tab
local notation "written" => output (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C tab
local notation "bounds" => Room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C
local notation "shifted" => Shift (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C.layout
local notation "cells" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) C.layout
local notation "counts" => C.base+capacity
local notation "starts" => (C.base+capacity)+homes

local notation "code" => machine (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) (bw:=bw) C
local notation "price" => DescentCompiler.TerminalScale.privateHomeClock capacity homes blocks p

def nativePrefix (m : Memory bw) (n : ℕ) :=
  ∑i∈Finset.range n,(written homes counts m (counts+i)).val
local notation "pref" => nativePrefix (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C

def rawPrefix (m : Memory bw) := ProtocolRAMEndpointPrefix.image starts (pref m) (written homes counts m) homes
local notation "prefixMem" => rawPrefix (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C

def rawFinal (O : DescentPrivateExponentRAM.Banks) (m : Memory bw) :=
  O.result p (prefixMem m O.usedWords).val (prefixMem m)
local notation "out" => rawFinal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C

private theorem three_runs (P Q R : Procedure bw) (m₀ m₁ m₂ m₃ : Memory bw) (a b c bill : ℕ)
    (one : P.Exec m₀ m₁ a) (two : Q.Exec m₁ m₂ b) (three : R.Exec m₂ m₃ c)
    (fee : a+b+c=bill) (cheapP : CheapCode P) (cheapQ : CheapCode Q) (cheapR : CheapCode R) :
    ((P.seq Q).seq R).Exec m₀ m₃ bill ∧ CheapCode ((P.seq Q).seq R) := by
  subst bill
  exact ⟨@Procedure.Exec.then bw (P.seq Q) R m₀ m₂ m₃ (a+b) c
      (@Procedure.Exec.then bw P Q m₀ m₁ m₂ a b (@one) (@two)) (@three),
    @cheap_seq bw (P.seq Q) R (@cheap_seq bw P Q (@cheapP) (@cheapQ)) (@cheapR)⟩

/-- The fixed CPU works on all memory images. At this level even the
older dictionary, its shift words, and the original budget can be arbitrary. -/
theorem any_raw (O : DescentPrivateExponentRAM.Banks) (m : Memory bw)
    (space : bounds bw) (room : starts+homes+1<2^bw) (scale : O.Room bw) :
    (code O).Exec m (out O m) price ∧ CheapCode (code O) := by
  have one := @run q t H N A p groups blocks homes bw C m space counts le_rfl (by omega)
  have two := @ProtocolRAMEndpointPrefix.run bw counts starts homes (pref m) (written homes counts m)
    le_rfl room (by simp [nativePrefix]) (by intro i _; simp [nativePrefix,Finset.sum_range_succ])
  have three := @DescentPrivateExponentRAM.Banks.run bw O p (prefixMem m O.usedWords).val (prefixMem m)
    scale (by simp)
  have time : (((4+10*capacity)+(4+homes*(16+234*blocks)))+(10+(3+12*homes)))+O.steps p=price := by
    rw [DescentPrivateExponentRAM.steps_eq]
    unfold DescentCompiler.TerminalScale.privateHomeClock
    omega
  exact three_runs (phase bw homes counts) (ProtocolRAMEndpointPrefix.exclusive bw counts starts homes)
    (O.program bw p) m (written homes counts m) (prefixMem m) (out O m) _ _ _ price
    (@one) (@two) (@three) time
    (@cheap_seq bw (install (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C bw)
      (scan bw counts homes (lookup C tab)) (@DescentStaticWordColumn.cheap bw C.base _ capacity)
      (@scan_cheap bw counts homes (lookup C tab)))
    (@ProtocolRAMRankCheap.exclusive_cheap bw counts starts homes)
    (@cheap_seq bw (ProtocolRAMStaticPorts.program bw O.usedBits 1 p (DescentPrivateEdgeCounter.cell O.usedWords))
      (scan bw O.deadBits 1 O.minus) (@ProtocolRAMStaticPortCheap.base bw O.usedBits 1 p (DescentPrivateEdgeCounter.cell O.usedWords))
      (@scan_cheap bw O.deadBits 1 O.minus))

theorem raw_eq_final (O : DescentPrivateExponentRAM.Banks) (m : Memory bw) (space : bounds bw)
    (room : starts+homes+1<2^bw) (scale : O.Room bw) (shift : shifted m) (dest : O.usedWords=starts+homes) :
    out O m=final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C O m :=
  ProtocolRAM.exec_unique _ _ _ _ (any_raw C O m space room scale).1 (any C O m space shift room scale dest).1


end
end Hierarchy.DescentTerminalVertexFields.PrivateCounter

end OAI
