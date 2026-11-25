import OAI.Hierarchy.HistorySelectedSeedRun
import OAI.ThreeFlat.RAM.HistorySeedControl
import OAI.ThreeFlat.RAM.HistorySeedWindow

namespace OAI
/-! # Retained seed caches and their chronological record pointers -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.PhysicalProcedure RAM.HistoryReadyTape RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

variable {F : Type*} {W k p : ℕ}

/-- The proof of the four addressed words needs just an evaluation theorem
at valid (gate, column) operands, which the receiver proves for every actual
virtual leaf. The two cursor families can use different compiled networks. -/
theorem metadata_reads (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (tag : ((Fin 3→ Bool)→ F)→ℕ) (N : BitNetwork F p) (src : Memory W)
    (count : N.cells=z.rows A) (four : 4<2^W)
    (operand : ∀ m : Memory W,z.retains A m src →
      ∀ i : Fin N.cells,∀ j : Fin 4,∀ v : Fin 4→ Word W,
        (v 0).val=i.val → (v 1).val=j.val → v 2=(z.lane:Word W) → v 3=(z.stage:Word W) →
        dec.eval pub m v=(HistoryCompiledRows.metadata tag N i j:Word W)) :
    RawReads A z dec pub src (recordAt tag N (z.stream A)) := by
  intro a m lo hi keep
  let n:=a.val-z.stream A
  have ir : n/4< N.cells := by dsimp [n];rw [count];omega
  let i : Fin N.cells:=⟨n/4,ir⟩
  let j : Fin 4:=⟨n%4,Nat.mod_lt _ (by decide)⟩
  let delta:=a-(z.stream A:Word W)
  have hcast : ((z.stream A):Word W).val=z.stream A:=Fin.val_cast_of_lt (lo.trans_lt a.isLt)
  have le : (z.stream A:Word W)≤ a := Fin.le_def.mpr (hcast.trans_le lo)
  have val : delta.val=n := by rw [show delta.val=_ from Fin.sub_val_of_le le,hcast]
  have denom : (4:Word W).val=4 := Fin.val_cast_of_lt four
  dsimp only
  change _=recordAt tag N (z.stream A) a.val
  rw [show recordAt (W:=W) tag N (z.stream A) a.val=(HistoryCompiledRows.metadata tag N i j:Word W)
    from dite_eq_left ir]
  apply operand m keep i j _ _ _ rfl rfl
  · change (Fin.ofNat (2^W) (delta.val/(4:Word W).val)).val=i.val
    rw [val,denom]
    exact Fin.val_cast_of_lt ((Nat.div_le_self n 4).trans_lt (by dsimp [n];exact (Nat.sub_le ..).trans_lt a.isLt))
  · change (Fin.ofNat (2^W) (delta.val%(4:Word W).val)).val=j.val
    rw [val,denom]
    exact Fin.val_cast_of_lt ((Nat.mod_lt n (by decide : 0<4)).trans four)

def node (net : BitNetwork F p) (ext slot stream ends : ℕ) : NodeValue F :=
  ⟨p,net,ext,fun i => 2+slot+i.val,stream,ends⟩

/-- Issue all rows, all local endpoint pointers and the six-word returned result. -/
theorem publish {u count kernel : ℕ} (shape : TraceBucketAtom.Layout)
    (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (tag : ((Fin 3→ Bool)→ F)→ℕ) (N : BitNetwork F p) (src : Memory W) (slot : ℕ)
    (control : ControlImage (initial u shape) z kernel src)
    (separate : Separated (initial u shape) z)
    (room : (initial u shape).ctrl+42<2^W)
    (_four : 4<2^W) (early : z.index< count)
    (arity : p=z.extPins+2*shape.bank) (cells : N.cells=z.rows (initial u shape))
    (hidden : N.internal=z.bits (initial u shape))
    (headerFit : ∀ j : Fin 6,z.words (initial u shape) ⟨36+j.val,by omega⟩<2^W)
    (fit : (initial u shape).intervals+4*z.lane+3<2^W)
    (safe : ¬z.writes (initial u shape) ((initial u shape).intervals+4*z.lane+3))
    (offset : src ((initial u shape).intervals+4*z.lane+3)=(slot:Word W))
    (size : 4*z.rows (initial u shape)≤ volume u) (ext : z.extPins≤ volume u)
    (v : 2≤ volume u) (scratch : volume u+42≤ stride u)
    (raw : RawReads (initial u shape) z dec pub src
      (recordAt tag N (z.stream (initial u shape)))) :
    let A := initial u shape
    let value := node N z.extPins slot (streamAt u count z.index) (endsAt u count z.index)
    ∃ out, (procedure A dec pub).Exec src out (ticks A z dec) ∧
      value.Cached tag u z.index out ∧ ∀ a,OutsideNode u z.index a → out a=src a := by
  let A := initial u shape
  let record := recordAt (W:=W) tag N (z.stream A)
  let endpoint := endpointAt (W:=W) slot (z.extBase A)
  let out := z.output A record endpoint src
  have fits := separate.jobs record endpoint room
  have run : (procedure A dec pub).Exec src out (ticks A z dec) := by
    intro P R K M
    exact execute_leaf A z dec pub src record slot room fits.1 fits.2 (control.seeded room)
      raw fit safe offset M
  have small : A.ctrl<2^W := by
    change (initial u shape).ctrl<2^W
    omega
  have emitted := z.read_output A record endpoint src small separate
  have header := z.read_result A record endpoint src small separate headerFit
  have rows := z.records_output A tag N record endpoint src small separate cells
    (recordAt_word tag N (z.stream A))
  have loc := initial_addresses u count shape z early
  have ports : z.extPins+2*(initial u shape).trace.bank=p := arity.symm
  refine ⟨out,run,⟨?_,?_,?_⟩,seed_outside shape z record endpoint src small size ext v scratch⟩
  · change HistoryStageRoot.atResult (fun k=>(out k).val) (base u 13+8*z.index) =
      ⟨z.stream A,z.extPins+2*A.trace.bank,z.rows A,z.bits A,z.extBase A,z.extPins⟩ at header
    rw [loc.1,loc.2,ports,←cells,←hidden] at header
    exact header
  · change HistoryCompiledRows.Records tag N (streamAt u count z.index) out
    rw [←loc.1]
    exact rows
  · intro j
    change out (endsAt u count z.index+j.val)=((2+slot+j.val : ℕ):Word W)
    rw [←loc.2]
    exact (emitted.2.1 j).trans (by simp [endpoint,endpointAt])

/-- Charge from the collected node's own unit mass and source sizes. -/
theorem ticks_le (A : Layout) (z : Site) (dec : Term W k 4) {mass : ℕ}
    (positive : 1≤ mass) (rows : z.rows A≤ mass) (ext : z.extPins≤ mass) :
    ticks A z dec ≤
      (4+42*(2*(formula A).work+4)+63+11*(2*(words A (liftDecoder dec)).binds+4))*mass := by
  let rate := 2*(words A (liftDecoder dec)).binds+4
  let overhead := 4+42*(2*(formula A).work+4)+63
  have ct : 4*z.rows A+z.extPins+6≤11*mass := by omega
  have copies := Nat.mul_le_mul_right rate ct
  have fixed := Nat.mul_le_mul_left overhead positive
  unfold ticks
  rw [←Nat.add_assoc (4+42*(2*(formula A).work+4)) 63]
  change overhead+(4*z.rows A+z.extPins+6)*rate≤(overhead+11*rate)*mass
  nlinarith only [copies,fixed]

end
end Hierarchy.HistorySelectedSeed

end OAI
