import OAI.Computability.BorderVNP.FragmentRowsPass
import OAI.Computability.BorderVNP.FragmentRowsStep

/-! # The complete native sparse external fragment directory producer

The three scans run in source-endpoint, destination-endpoint, and data-delivery
order. Word 29 of the indirect control table publishes the resulting row count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Diagonal.ExternalSew.Fragments VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open Packing.BottomReports.Writer (write write_read)

/-- Chronological quadruple stores followed by the published occupied row count. -/
def Layout.image (l : Layout) (m : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (write m l.quads ((l.stream m).flatMap Quad.words)) (l.control+29) (l.stream m).length

@[simp] theorem Layout.image_count (l : Layout) (m : ℕ → ℕ) :
    l.image m (l.control+29)=(l.stream m).length := Function.update_self ..

/-- Every scalar of every live quadruple survives the publication of the count. -/
theorem Layout.image_quads (l : Layout) (m : ℕ → ℕ) {w : ℕ} (fit : l.Fits w m) :
    CellPacket.WordsAt (l.image m) l.quads ((l.stream m).flatMap Quad.words) := by
  intro i
  have len : (l.stream m).length ≤ 2*l.host.count+l.count := by
    simpa [Layout.stream] using stream_length l.host m (fun c => m (l.supplied+c)) ((List.range l.count).map (l.row m))
  have bound := i.isLt.trans_le (quadWords_length (l.stream m)).le
  have ne : l.quads+i.val ≠ l.control+29 := by rcases fit.controlOutside with h|h <;> omega
  rw [Layout.image,Function.update_of_ne ne]
  exact write_read _ _ _ i

private theorem finish_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before)
    (ready : l.Emitted before (l.stream before) (.ofWords s m)) :
    BoundedRun pub mac finish s m finish.slots (fun z => z.mem=l.image before) := by
  let z := NatState.ofWords s m
  have ctl : z.reg 12=l.control := ready.1 _ (by decide)
  have used : z.reg 14=(l.stream before).length := ready.2.1
  have mem : z.mem=write before l.quads ((l.stream before).flatMap Quad.words) := ready.2.2
  have hc := fit.control
  have safe : finish.fixedSafe w (readings pub) z := by
    simp [finish,Code.block,Code.fixedSafe,Code.fixedEval,Code.evalNat,Code.safeReadOnly,addressOpFits,ctl]
    omega
  apply (finish.runFixed pub mac s m safe).mono le_rfl
  rintro _ rfl
  change (finish.fixedEval (readings pub) z).mem=_
  simp [finish,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update,ctl,used,mem,Layout.image]

/-- All three native passes produce the specified stable stream, using at most
256 ticks per potential input row including fixed setup and publication. -/
theorem program_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout)
    (layout : l=Layout.fromFrame (readings pub 0) (readings m)) (fit : l.Fits w (readings m)) :
    BoundedRun pub mac program s m (256*(2*l.host.count+l.count+1)) (fun z => z.mem=l.image (readings m)) := by
  let before := readings m
  let a := Pass.cable false
  let b := Pass.cable true
  let d := Pass.data
  let qs := a.rows l before l.host.count
  let rs := b.rows l before l.host.count
  have aSize : qs.length≤l.host.count := a.rows_length l before l.host.count
  have bSize : rs.length≤l.host.count := b.rows_length l before l.host.count
  have complete : (qs++rs)++d.rows l before l.count=l.stream before := by
    simp [qs,rs,a,b,d,Pass.rows,Pass.row,Layout.stream,stream,List.filterMap_map]
    rfl
  have pass (p : Pass) (prior : List Quad) (r : Bank w) (mr : Memory w)
      (input : l.Emitted before prior (.ofWords r mr)) (room : prior.length+p.count l≤2*l.host.count+l.count) :=
    pass_run pub mac r mr l before p prior fit input room
      (fun t mt i used h₁ h₂ h₃ h₄ h₅ h₆ => step_run pub mac t mt l before p i used fit h₁ h₂ h₃ h₄ h₅ h₆)
  have start := setup_run pub mac s m l layout fit
  have first (r : Bank w) (mr : Memory w) (input : l.Emitted before [] (.ofWords r mr)) :
      BoundedRun pub mac (FragmentBucket.forEach 15 7 (cableStep false)) r mr (2+l.host.count*((cableStep false).slots+1))
        (l.Emitted before qs) := by
    simpa [a,qs,Pass.count,Pass.boundReg,Pass.step] using pass a [] r mr input (by change 0+l.host.count≤_; omega)
  have whole := start.seq fun r mr hr =>
    (first r mr hr).seq fun t mt ht =>
      (pass b qs t mt ht (by change qs.length+l.host.count≤_; omega)).seq fun u mu hu =>
        (pass d (qs++rs) u mu hu (by change (qs++rs).length+l.count≤_; simp only [List.length_append]; omega)).seq
          fun v mv hv => finish_run pub mac v mv l before fit (complete ▸ hv)
  apply whole.mono _ (fun _ h => h)
  change setup.slots + ((2+l.host.count*((cableStep false).slots+1)) +
    ((2+l.host.count*((cableStep true).slots+1)) + ((2+l.count*(dataStep.slots+1))+finish.slots))) ≤ _
  have hs : setup.slots≤200 := by decide
  have ha : (cableStep false).slots+1≤256 := by decide
  have hb : (cableStep true).slots+1≤256 := by decide
  have hd : dataStep.slots+1≤256 := by decide
  have hf : finish.slots≤20 := by decide
  have h₁ := Nat.mul_le_mul_left l.host.count ha
  have h₂ := Nat.mul_le_mul_left l.host.count hb
  have h₃ := Nat.mul_le_mul_left l.count hd
  omega

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
