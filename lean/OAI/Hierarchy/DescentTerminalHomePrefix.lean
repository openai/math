import OAI.Hierarchy.DescentTerminalHomeCounter

namespace OAI
/-! # Sum the measured private reference counts over the original common hosts -/
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

def charge (i : ℕ) (m : Memory bw) :=
  if h : i<homes then privateHome (cells m (⟨i,h⟩:Fin homes)) else 0

def partialCount (m : Memory bw) (k : ℕ) :=
  ∑j∈Finset.range k,charge (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C j m

local notation "pref" => partialCount (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C

def «prefix» (bw homes : ℕ) := (phase bw homes counts).seq (ProtocolRAMEndpointPrefix.exclusive bw counts (counts+homes) homes)

def prefixImage (m : Memory bw) :=
  ProtocolRAMEndpointPrefix.image starts (pref m) (written homes counts m) homes

def prefixTicks (homes blocks «capacity» : ℕ) :=
  ((4+10*«capacity»)+(4+homes*(16+234*blocks)))+(10+(3+12*homes))

local notation "machine" => «prefix» (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C bw homes
local notation "result" => prefixImage (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) C

theorem prefix_frame (m : Memory bw) (addr : ℕ) (away : addr<C.base ∨ starts+homes<addr) :
    result m addr=m addr := by
  rw [prefixImage,ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (by omega),output,
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)]
  exact DescentStaticWordColumn.frame _ _ _ _ _ (by omega)

theorem prefix_run (m : Memory bw) (room : bounds bw) (shift : shifted m) (fit : starts+homes+1<2^bw) :
    (machine).Exec m (result m) (prefixTicks homes blocks capacity) ∧
    (result m (starts+homes)=(∑i : Fin homes,privateHome (cells m i):ℕ)) ∧
    (∀addr,addr<C.base ∨ starts+homes<addr → result m addr=m addr) ∧ CheapCode machine := by
  have printed:=@run q t H N A p groups blocks homes bw C m room counts le_rfl
    (show counts+homes<2^bw by omega)
  have read (i : Fin homes) : written homes counts m (counts+i.val)=(privateHome (cells m i):Word bw) :=
    (ProtocolRAMGeneratedWrite.read_image counts homes (lookup C tab) _ i).trans
      (masked_score C m room shift i)
  have step (i : ℕ) (live : i<homes) :
      (pref m (i+1):Word bw)=(pref m i:Word bw)+written homes counts m (counts+i) := by
    rw [partialCount,Finset.sum_range_succ,Nat.cast_add]
    change (pref m i:Word bw)+(if h : i<homes then (privateHome (cells m (⟨i,h⟩:Fin homes)):ℕ) else 0:ℕ)=_
    rw [dite_eq_left live]
    exact congrArg ((pref m i:Word bw)+·) (read ⟨i,live⟩).symm
  have total:=@ProtocolRAMEndpointPrefix.run bw counts starts homes (pref m) (written homes counts m)
    le_rfl fit (by simp [partialCount]) step
  refine ⟨@Procedure.Exec.then bw (phase bw homes counts) (ProtocolRAMEndpointPrefix.exclusive bw counts starts homes)
    m (written homes counts m) (result m) _ _ (@printed) (@total),?_,?_,?_⟩
  · rw [prefixImage,ProtocolRAMEndpointPrefix.read _ _ _ _ _ le_rfl]
    congr 1
    rw [partialCount,←Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _=>by simp [charge,i.isLt]
  · exact prefix_frame C m
  · exact cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap bw C.base _ capacity)
      (@scan_cheap bw counts homes (lookup C tab))) (@ProtocolRAMRankCheap.exclusive_cheap bw counts starts homes)

/-- This form is directly payable by the physical terminal host tariff. -/
theorem prefix_clock (pos : 0<blocks) : prefixTicks homes blocks capacity ≤ 21+10*capacity+262*(homes*blocks) := by
  unfold prefixTicks
  have dom:=Nat.le_mul_of_pos_right homes pos
  nlinarith only [dom]

end
end Hierarchy.DescentTerminalVertexFields.PrivateCounter

end OAI
