import OAI.Computability.BorderVNP.CubeLabelISAScan

/-! # Fixed ISA calculation of a cable or delivery bin in §8.1

Ordered cable bins occupy the first `Z²` positions in row-major order. The next
`Z` positions hold the delivery bins. Every numerator, including delivery, has
the common denominator `Z²`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM

/-- Dimensions and the six arrays used during the trial and commit passes. -/
structure Frame where
  /-- Alphabet size. -/
  Z : ℕ
  /-- Number of cells in public order. -/
  cells : ℕ
  /-- Output label array. -/
  labels : ℕ
  /-- One-based heads of the incident lists. -/
  heads : ℕ
  /-- Four-word incidence nodes. -/
  nodes : ℕ
  /-- Total delivery width per cell. -/
  demands : ℕ
  /-- Scaled ordered cable-bin means. -/
  cables : ℕ
  /-- Scaled delivery-bin means. -/
  data : ℕ

/-- Load the sparse layout already constructed in the public frame. -/
def Frame.decode (b : ℕ) (m : ℕ → ℕ) : Frame :=
  ⟨m (b+56),m (b+11),m (b+48),m (b+49),m (b+50),m (b+51),m (b+52),m (b+53)⟩

/-- The common 13 parameters preserved by all trials. -/
def params : List Reg := [0,19,20,21,23,28,29,30,34,35,36,38,39]

/-- Value of a fixed parameter register. -/
def Frame.param (p : Frame) : ℕ → ℕ
  | 0 => p.Z | 19 => p.cells | 20 => 1 | 21 => p.labels | 23 => 0
  | 28 => p.heads | 29 => p.nodes | 30 => 4 | 34 => p.demands | 35 => p.cables
  | 36 => p.data | 38 => p.Z^2 | 39 => p.Z^2+p.Z | _ => 0

/-- The common layout is in the physical register bank. -/
def Frame.loaded (p : Frame) (z : NatState) := ∀ k ∈ params, z.reg k = p.param k.val

/-- Register 37 ranges over all bins for the particular cell and label in 1 and 2. -/
def Frame.ready (p : Frame) (c v i : ℕ) (z : NatState) := p.loaded z ∧
  z.reg 1 = c ∧ z.reg 2 = v ∧ z.reg 37 = i

/-- Physical cache address for one bin ordinal. -/
def Frame.cacheAddr (p : Frame) (i : ℕ) := if i < p.Z^2 then p.cables+i else p.data+(i-p.Z^2)

/-- Cable query associated to a row-major bin. -/
def Frame.query (p : Frame) (c v i : ℕ) : Query :=
  ⟨p.Z,c,v,i/p.Z,i%p.Z,p.labels,p.nodes⟩

/-- Total contribution of the incident rows before and after assigning this label. -/
def Frame.incident (p : Frame) (c v i : ℕ) (m : ℕ → ℕ) (es : List Incident) : ℕ × ℕ :=
  if i < p.Z^2 then (p.query c v i).sums m es else
    let old := m (p.demands+c)*p.Z
    (old, if v = i-p.Z^2 then old*p.Z else 0)

/-- The linked list has this physical image, the probes are in address space,
and the scaled incident masses fit the selected word width. -/
def Frame.room (p : Frame) (w c v i : ℕ) (m : ℕ → ℕ) (es : List Incident) : Prop :=
  0 < p.Z ∧ p.cacheAddr i < 2^w ∧
  (if i < p.Z^2 then
     let q := p.query c v i
     let ptr := m (p.heads+c)
     p.heads+c < 2^w ∧ Chain m p.nodes ptr es ∧ q.room w m ptr es ∧
       (q.sums m es).1 < 2^w ∧ (q.sums m es).2 < 2^w
   else p.demands+c < 2^w ∧ m (p.demands+c)*p.Z^2 < 2^w)

/-- Compute both indices, fetch the head, and clear the incident sum registers. -/
def cableStart : Code := .block [.binary .div 3 37 0, .binary .mod 4 37 0,
  .binary .add 31 35 37, .binary .add 25 28 1, .load 24 25, .copy 26 23, .copy 27 23]

/-- A data bin needs one aggregated data word and no traversal. -/
def dataBin : Code := .block [.binary .sub 3 37 38, .binary .add 31 36 3,
  .binary .add 25 34 1, .load 26 25, .binary .mul 26 26 0,
  .ifEq 2 3 (.binary .mul 27 26 0) (.copy 27 23)]

/-- Obtain a true cache address and the two sums of its incident contributions. -/
def binContrib : Code := .ifLt 37 38 (.seq cableStart scan) dataBin

/-- The per-bin scan is deterministic and read-only. -/
theorem binContrib_deterministic : binContrib.deterministic = true := by decide

/-- Parameters and the surrounding loop cursors survive each bin. -/
theorem binContrib_keeps : ∀ k ∈ params ++ [1,2,16,17,18,37], binContrib.keeps k = true := by decide

private theorem cable_start (p : Frame) (w c v i : ℕ) (z : NatState) (pub : Arg → ℕ)
    (h : p.ready c v i z) (hz : 0 < p.Z) (hc : i < p.Z^2)
    (addr : p.cacheAddr i < 2^w) (head : p.heads+c < 2^w) :
    let t := cableStart.fixedEval pub z
    cableStart.fixedSafe w pub z ∧ (p.query c v i).loaded t ∧ t.reg 31 = p.cacheAddr i ∧
      t.reg 24 = z.mem (p.heads+c) ∧ t.reg 26 = 0 ∧ t.reg 27 = 0 ∧ t.mem = z.mem := by
  obtain ⟨l,h₁,h₂,h₃₇⟩ := h
  have h₀ := l 0 (by decide)
  have h₂₀ := l 20 (by decide)
  have h₂₁ := l 21 (by decide)
  have h₂₃ := l 23 (by decide)
  have h₂₈ := l 28 (by decide)
  have h₂₉ := l 29 (by decide)
  have h₃₀ := l 30 (by decide)
  have h₃₅ := l 35 (by decide)
  simp [Frame.param] at h₀ h₂₀ h₂₁ h₂₃ h₂₈ h₂₉ h₃₀ h₃₅
  simp [Frame.cacheAddr,hc] at addr
  simp [cableStart, Code.block, Code.fixedSafe, Code.fixedEval, Code.evalNat, Code.safeReadOnly,
    addressOp, addressOpFits, Function.update, Frame.query, Frame.cacheAddr, Query.loaded,
    h₀,h₁,h₂,h₂₀,h₂₁,h₂₃,h₂₈,h₂₉,h₃₀,h₃₅,h₃₇,hz,hc,head,addr]

private theorem data_bin (p : Frame) (w c v i : ℕ) (z : NatState) (pub : Arg → ℕ)
    (h : p.ready c v i z) (hz : 0 < p.Z) (hc : ¬ i < p.Z^2) (es : List Incident)
    (addr : p.cacheAddr i < 2^w) (dat : p.demands+c < 2^w)
    (fit : z.mem (p.demands+c)*p.Z^2 < 2^w) :
    let t := dataBin.fixedEval pub z
    dataBin.fixedSafe w pub z ∧ t.reg 31 = p.cacheAddr i ∧ t.reg 26 = (p.incident c v i z.mem es).1 ∧
      t.reg 27 = (p.incident c v i z.mem es).2 ∧ t.mem = z.mem := by
  obtain ⟨l,h₁,h₂,h₃₇⟩ := h
  have h₀ := l 0 (by decide)
  have h₂₃ := l 23 (by decide)
  have h₃₄ := l 34 (by decide)
  have h₃₆ := l 36 (by decide)
  have h₃₈ := l 38 (by decide)
  simp [Frame.param] at h₀ h₂₃ h₃₄ h₃₆ h₃₈
  simp [Frame.cacheAddr,hc] at addr
  rw [pow_two, ← Nat.mul_assoc] at fit
  have partFit := (Nat.le_mul_of_pos_right _ hz).trans_lt fit
  by_cases hv : v = i - p.Z^2 <;>
    simp [dataBin, Code.block, Code.fixedSafe, Code.fixedEval, Code.evalNat, Code.safeReadOnly,
      addressOp, addressOpFits, Function.update, Frame.incident,Frame.cacheAddr,
      h₀,h₁,h₂,h₂₃,h₃₄,h₃₆,h₃₇,h₃₈,hc,hv,le_of_not_gt hc,addr,dat,partFit,fit]

/-- One complete physical bin calculation returns both scaled sums and the correct
cache address. Its only nonconstant work is a walk along this cell's incidence list. -/
theorem binContrib_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (p : Frame) (c v i : ℕ) (s : Bank w) (m : Memory w) (es : List Incident)
    (ready : p.ready c v i (.ofWords s m)) (room : p.room w c v i (readings m) es) :
    ∃ tr t, Runs pub macros binContrib s m tr t m ∧ traceCost tr ≤ 24*es.length+12 ∧
      (t 31).val = p.cacheAddr i ∧ (t 26).val = (p.incident c v i (readings m) es).1 ∧
      (t 27).val = (p.incident c v i (readings m) es).2 := by
  obtain ⟨hz,addr,space⟩ := room
  have h₃₇ : (s 37).val = i := ready.2.2.2
  have h₃₈ : (s 38).val = p.Z^2 := ready.1 38 (by decide)
  by_cases hc : i < p.Z^2
  · have guard : s 37 < s 38 := show (s 37).val < (s 38).val by omega
    simp only [hc,ite_true] at space
    obtain ⟨head,chain,fit,lo,hi⟩ := space
    obtain ⟨safe,qload,h31,ptr,h26,h27,hm⟩ := cable_start p w c v i _ (readings pub) ready hz hc addr head
    obtain ⟨gs,b,mb,start,cs,he⟩ := cableStart.runFixed pub macros s m safe
    rw [← he] at qload h31 ptr h26 h27 hm
    have hmem : mb = m := funext fun k => Fin.ext (congrFun hm k)
    subst mb
    change (b 26).val = 0 at h26
    change (b 27).val = 0 at h27
    obtain ⟨fs,t,run,cost,a,d⟩ := scan_run pub macros (p.query c v i) hz b m qload ptr chain fit
      (by simpa [h26] using lo) (by simpa [h27] using hi)
    refine ⟨_,t,.ifLt (by simpa [guard] using start.seq run),?_,?_,?_,?_⟩
    · change 1 + traceCost (gs++fs) ≤ _
      rw [show traceCost (gs++fs) = traceCost gs + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
      change traceCost gs ≤ 7 at cs
      omega
    · rw [run.keepsReg (k := 31) (by decide)]; exact h31
    · simpa [Frame.incident,hc,h26] using a
    · simpa [Frame.incident,hc,h27] using d
  · have guard : ¬ s 37 < s 38 := show ¬ (s 37).val < (s 38).val by omega
    simp only [hc,ite_false] at space
    obtain ⟨safe,h31,h26,h27,hm⟩ := data_bin p w c v i _ (readings pub) ready hz hc es addr space.1 space.2
    obtain ⟨gs,t,mt,run,cost,he⟩ := dataBin.runFixed pub macros s m safe
    rw [← he] at h31 h26 h27 hm
    have hmem : mt = m := funext fun k => Fin.ext (congrFun hm k)
    subst mt
    refine ⟨_,t,.ifLt (by simpa [guard] using run),?_,h31,h26,h27⟩
    change 1 + traceCost gs ≤ _
    change traceCost gs ≤ 8 at cost
    omega

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
