import OAI.Hierarchy.DescentMeasuredLoadRAM
import OAI.Hierarchy.DescentMeasuredPortProof

namespace OAI
/-! # Joint native row preparation from actual preceding depth, load and neighbor tapes -/
namespace Hierarchy.DescentMeasuredHeader
open DescentMeasuredWeights DescentPackedExchange DescentColonies DescentGL DescentLinearLayouts
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}
def origin (start H k Δ : ℕ) := start+3*(H*(k+1)+H*Δ)+1
def emit (L : Tape) (D : DataTape) (w start H k Δ : ℕ) : Procedure w :=
  (headerProgram L w start H k Δ).seq (scan w (origin start H k Δ) ((H*(k+1)+H*Δ)*2^k) (payloadExpr D))
def primed (L : Tape) (D : DataTape) (start H k Δ : ℕ) (m : Memory w) :=
  image (origin start H k Δ) ((H*(k+1)+H*Δ)*2^k) (payloadExpr D) (headerMem L start H k Δ m)
def clocks (L : Tape) (H k Δ : ℕ) := headerTime L H k Δ + (4+(H*(k+1)+H*Δ)*2^k*100)

variable {H k Δ : ℕ}
local notation "N" => H*(k+1)+H*Δ
local notation "R" => Rows H k Δ

private theorem seq_receipt {a b : Procedure w} {m ready out : Memory w} {ha hb ticks : ℕ}
    (first : a.Exec m ready ha ∧ CheapCode a) (second : b.Exec ready out hb ∧ CheapCode b)
    (total : ha + hb = ticks) : (a.seq b).Exec m out ticks ∧ CheapCode (a.seq b) := by
  subst ticks
  obtain ⟨p, pc⟩ := first
  obtain ⟨q, qc⟩ := second
  exact ⟨@Procedure.Exec.then w a b m ready out ha hb (@p) (@q), @cheap_seq w a b pc qc⟩

set_option maxHeartbeats 1200000 in
theorem emit_exec (L : Tape) (D : DataTape) (start : ℕ) (m : Memory w) (safe : Fits L w H k Δ start)
    (data : DataFits D w H k Δ (origin start H k Δ)) (room : origin start H k Δ+N*2^k<2^w) :
    (emit L D w start H k Δ).Exec m (primed L D start H k Δ m) (clocks L H k Δ) ∧ CheapCode (emit L D w start H k Δ) := by
  unfold emit primed
  apply seq_receipt (a := headerProgram L w start H k Δ)
    (b := scan w (origin start H k Δ) (N*2^k) (payloadExpr D))
    (ready := headerMem L start H k Δ m) (ha := headerTime L H k Δ)
    (hb := 4+(N*2^k)*(2*(payloadExpr D).work+4))
  · exact header_exec L m safe (by unfold origin at room; omega)
  · exact data_program D data room (headerMem L start H k Δ m)
  · simp only [clocks, payload_work, show 2*48+4=100 by decide]

theorem clock_bound (L : Tape) (H k Δ : ℕ) : clocks L H k Δ ≤ 16+780*(H*(k+1)+H*Δ)+(H*(k+1)+H*Δ)*2^k*100 := by
  have:=header_time L H k Δ;unfold clocks;omega

def fixedData (D : DataTape) := [D.row,D.tag,D.addr,D.sites,D.traffic]
structure Before (D : DataTape) (start : ℕ) : Prop where
  bound : ∀z∈fixedData D,z.base+z.size≤ start
  flag : D.live.base=start

theorem primed_frame (L : Tape) (D : DataTape) (start : ℕ) (m : Memory w) {a : ℕ} (low : a<start) :
    primed L D start H k Δ m a=m a := by
  unfold primed
  rw [image_frame _ _ (by unfold origin; omega)]
  exact header_frame L m low

variable {V : Type} [Fintype V] [DecidableEq V]
variable (idx : V≃Fin H) (near : V→Finset V) (cap : ∀v,(near v).card≤Δ) (b : V→ℕ) (hk : ∀v,b v≤k)
local notation "loc" => portRow (k:=k) idx near cap b
local notation "nxt" => neighborSlot (degree:=Δ) idx near
local notation "levels" => inputLevels (k:=k) b
local notation "locOrd" => rowOrd H k Δ

include hk

omit [DecidableEq V] in
theorem primed_heads (L : Tape) (D : DataTape) (start : ℕ) (safe : Fits L w H k Δ start) (f B K : ℕ)
    (m : Memory w) (head : contents (k:=k) L (b∘idx.symm) nxt f B K m) (width : H<2^w) (wide : 2*k+1<2^w)
    (i : Fin N) :
    (let tab := mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ) i
     let out:=primed L D start H k Δ m
     out tab.depth=((padded loc (level levels (inputDepth b) (pairDepth near b)) 0 i : ℕ) : Word w) ∧
     out tab.gain=((padded loc (gain levels f B K) 0 i : ℕ) : Word w)) := by
  obtain ⟨t,rfl⟩:=(locOrd).surjective i
  have hi:=(locOrd t).isLt
  have read:=header_read L safe (b∘idx.symm) nxt f B K m head width wide (fun _=>hk _)
  constructor
  · change image _ _ _ _ (start+N+(locOrd t).val)=_
    rw [image_frame _ _ (by unfold origin;omega)]
    simpa only [fieldNumber,Nat.one_mul,value,depth_padded idx near cap b hk] using read .depth t
  · change image _ _ _ _ (start+2*N+(locOrd t).val)=_
    rw [image_frame _ _ (by unfold origin;omega)]
    simpa only [fieldNumber,value,gain_padded idx near cap b hk] using read .gain t

omit [DecidableEq V] in
theorem primed_values (L : Tape) (D : DataTape) (start : ℕ) (safe : Fits L w H k Δ start)
    (data : DataFits D w H k Δ (origin start H k Δ)) (previous : Before D start)
    (f B K : ℕ) (site : Fin H→Fin (2^k)→ℕ) (traffic : Port H Δ→Fin (2^k)→ℕ)
    (x : V→Bits k→ℕ) (y : Contacts near→Bits k→ℕ)
    (siteRead : ∀v, (fun z=>site (idx v) (DescentColonies.address k z))=x v)
    (flowRead : ∀c, (fun z=>traffic (atPort idx near cap c) (DescentColonies.address k z))=y c)
    (m : Memory w) (head : contents (k:=k) L (b∘idx.symm) nxt f B K m) (width : H<2^w)
    (wide : 2*k+1<2^w) (pointers : dataStatic (H:=H) (k:=k) (Δ:=Δ) D m)
    (prior : oldLoads D site traffic m) (i : Fin N) (d : Fin (2^k)) :
    primed L D start H k Δ m ((mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ) i).payload+d.val)=
      ((padded loc (load levels x y) (fun _=>0) i (DescentGLScoreRAM.vec d) : ℕ) : Word w) := by
  let ready := headerMem L start H k Δ m
  have keep (z : Bank) (hz : z ∈ fixedData D) (a : ℕ) (ha : a < z.size) :
      ready (z.base + a) = m (z.base + a) := by
    have high := previous.bound z hz
    exact header_frame L m (by omega)
  have staticRead : dataStatic (H := H) (k := k) (Δ := Δ) D ready := by
    intro t j
    let i := outputOrdinal (H := H) (k := k) (Δ := Δ) t j
    have col (z : Bank) (hz : z ∈ [D.row, D.tag, D.addr]) :
        ready (z.base + i.val) = m (z.base + i.val) := by
      have below : i.val < z.size := i.isLt.trans_le (data.«meta» z hz)
      have fixed : z ∈ fixedData D := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> simp [fixedData]
      exact keep z fixed i.val below
    obtain ⟨row, tag, addr⟩ := pointers t j
    exact ⟨(col D.row (by simp)).trans row, (col D.tag (by simp)).trans tag,
      (col D.addr (by simp)).trans addr⟩
  have offset_lt {n : ℕ} (u : Fin n) (j : Fin (2^k)) :
      u.val * 2^k + j.val < n * 2^k := by
    calc
      _ < (u.val + 1) * 2^k := by
        rw [Nat.succ_mul]
        exact Nat.add_lt_add_left j.isLt _
      _ ≤ _ := Nat.mul_le_mul_right _ u.isLt
  have old : oldLoads D site traffic ready := by
    constructor
    · intro v z
      have below : v.val * 2^k + z.val < D.sites.size :=
        (offset_lt v z).trans_le data.sites
      exact (keep D.sites (by simp [fixedData]) _ below).trans (prior.1 v z)
    · intro p z
      have below : (slot H Δ p).val * 2^k + z.val < D.traffic.size :=
        (offset_lt (slot H Δ p) z).trans_le data.traffic
      exact (keep D.traffic (by simp [fixedData]) _ below).trans (prior.2 p z)
  have flag (t : Rows H k Δ) :
      ready (D.live.base + (rowOrd H k Δ t).val) = (isLive (b ∘ idx.symm) nxt t : Word w) := by
    rw [previous.flag]
    simpa only [ready, value, fieldNumber, Nat.zero_mul, Nat.add_zero] using
      header_read L safe (b ∘ idx.symm) nxt f B K m head width wide (fun v => hk (idx.symm v)) .live t
  obtain ⟨t, rfl⟩ := (rowOrd H k Δ).surjective i
  have s := payload_read D data (b ∘ idx.symm) nxt site traffic ready (by omega) staticRead old flag t d
  have actual := congrFun (load_padded idx near cap b hk (fun v z => site v (DescentColonies.address k z))
    (fun p z => traffic p (DescentColonies.address k z)) x y siteRead flowRead t) (DescentGLScoreRAM.vec d)
  change image (origin start H k Δ) _ (payloadExpr D) ready
    ((origin start H k Δ + (rowOrd H k Δ t).val * 2^k) + d.val) = _
  rw [Nat.add_assoc, ← outputOrdinal_val t d]
  exact (image_val (payloadExpr D) ready (outputOrdinal t d)).trans
    (s.trans (congrArg (fun n : ℕ => (n : Word w)) actual))

end
end Hierarchy.DescentMeasuredHeader

end OAI
