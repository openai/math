import OAI.Hierarchy.DescentDatedOperandReadPipeline

namespace OAI
/-! # Reading each nested selector back from the memory on which the previous one ran -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry)
abbrev Values (a : ℕ) := Fin g.hosts → Fin g.groups → Cell a
local notation "A" => Values g g.digitBits
local notation "J" => g.jobs
local notation "M" => g.lanes
local notation "a" => g.digitBits

structure Held {w t : ℕ} (base : ℕ) (m : Memory w) (e : Expr) (v : Values g t) : Prop where
  fits : e.Fits w base
  read : Source e v M m

structure Step {w : ℕ} (l h : ℕ) (p : NativePhase w) (m : Memory w) : Prop where
  order : l≤h
  run : p.Runs m
  frame : ∀i,i<l ∨ h ≤ i → p.image m i=m i

namespace Step
variable {w l k h : ℕ} {p q : NativePhase w} {m : Memory w}
theorem thenStep (one : Step l k p m) (two : Step k h q (p.image m)) : Step l h (p.seq q) m :=by
  refine ⟨one.order.trans two.order,NativePhase.seq_runs _ _ m one.run two.run,?_⟩
  intro i side
  rcases side with prior|later
  · exact (two.frame i (.inl (prior.trans_le one.order))).trans (one.frame i (.inl prior))
  · exact (two.frame i (.inr later)).trans (one.frame i (.inr (two.order.trans later)))

theorem keep {t : ℕ} {expr : Expr} {v : Values g t}
    (receipt : Step l h p m) (previous : Held g l m expr v) : Held g h (p.image m) expr v :=
  ⟨ProtocolRAMGeneratedWrite.fits_mono _ receipt.order previous.fits,fun j=>
    (ProtocolRAM.eval_below _ _ m (p.image m) previous.fits (fun i hi=>receipt.frame i (.inl hi))).trans (previous.read j)⟩
end Step

def picked {cols count n : ℕ} (law : Fin 1 → (Fin n → Cell a) → Cell (keyWidth count))
    (x : Fin J → Fin n → A) (y : Fin J → Fin cols → Fin count → A) (j : Fin J) (f : Fin cols) : A :=
  fun h r=>DescentResetStemMux.pick (law 0 (fun i=>x j i h r)) (fun i=>y j f i h r)

theorem selection {cols count n base w : ℕ} (law : Fin 1 → (Fin n → Cell a) → Cell (keyWidth count))
    (args : Fin J → Fin n → Expr) (head : Fin J → Fin cols → Fin count → Expr)
    (x : Fin J → Fin n → A) (y : Fin J → Fin cols → Fin count → A) (m : Memory w)
    (blank : ∀f,law f (fun _=>0)=0)
    (inputs : ∀j i,Held g base m (args j i) (x j i))
    (table : ∀j f i,Held g base m (head j f i) (y j f i)) (space : after g n cols count base<2^w) :
    let stage:=readStage g law args head base w
    Step base (after g n cols count base) stage m ∧
      ∀j f,Held g (after g n cols count base) (stage.image m) (lookup g n cols count base j f) (picked g law x y j f) :=by
  intro stage
  let L:=layout g cols count
  let js:=fun (r:Fin (J*cols))=>(finProdFinEquiv.symm r : Fin J×Fin cols)
  let src:=fun r=>args (js r).1
  let hd:=fun r=>head (js r).1 (js r).2
  let z:=fun r h k i=>x (js r).1 i h k
  let v:=fun r=>y (js r).1 (js r).2
  have fit (r i) : (src r i).Fits w base:=(inputs (js r).1 i).fits
  have good (r i) : (hd r i).Fits w base:=(table (js r).1 (js r).2 i).fits
  have paid:=DescentDatedOperandSelectionRun.any L law (fun _=>0) src hd fit good space m
  have initial:base≤DescentDatedOperandSelectionRun.nextAddress L 1 n a base:=Nat.le_add_right ..
  have order:base≤after g n cols count base:=initial.trans (DescentDatedOperandSelectionRun.reaches L base)
  refine ⟨⟨order,paid.1,paid.2⟩,?_⟩
  intro j f
  let idx:=finProdFinEquiv (j,f)
  have stored:=DescentDatedOperandSelectionRun.emitted L law (fun _=>0) src hd fit good space m blank z v
    (fun r i=>(inputs (js r).1 i).read) (fun r i=>(table (js r).1 (js r).2 i).read) idx
  have room:=DescentDatedOperandMux.bank_room L (DescentDatedOperandSelectionRun.nextAddress L 1 n a base) space idx
  refine ⟨⟨room.1,trivial⟩,?_⟩
  apply source_column _ _ room.1 _ _ room.2
  let result := fun (h : Fin g.hosts) (k : Fin g.groups) =>
    DescentResetStemMux.pick (law 0 (fun i=>x j i h k)) (fun i=>y j f i h k)
  have actual : DescentPackedColony.Reads (DescentDatedOperandSelectionRun.bank L 1 n a base idx)
      result L.lanes ((DescentDatedOperandSelectionRun.phase L law (fun _=>0) src hd base w).image m) := by
    simpa only [idx,js,z,v,result,L,layout,Equiv.symm_apply_apply] using stored
  change DescentPackedColony.Reads (DescentDatedOperandSelectionRun.bank L 1 n a base idx)
    result L.lanes ((DescentDatedOperandSelectionRun.phase L law (fun _=>0) src hd base w).image m)
  exact actual

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
