import OAI.Hierarchy.DescentRecordedControlWords
import OAI.Hierarchy.DescentResetControlPackedSources

namespace OAI
/-! # The reset operand sources through the padded edge of the host array -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentDenseHostOrder DescentSIMDLookup DescentPackedZip
open DescentPackedColony DescentVenueQuantityPlanes DescentResetControlRegisters
open Computability.VPVNP.BurstRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {old : Reached W G q ε S k i z D wire hist} {rates : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset old rates) {oldH H oldM M w a : ℕ}
    (previous : Fintype.card old.V ≤ oldH) (next : Fintype.card B.next.V ≤ H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "J" => S.groupCount (i+1)
local notation "cap" => old.placement.cap
local notation "chosen" => B.next.vertex.trans (Fin.castLEEmb next)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb previous)
local notation "shapeId" v => ((Z).hostFields T rank v).2.val
local notation "depthAt" v => (Z).placement.b (position (Z).graph (v).val)
local notation "dims" => quantityDims B 1 oldH H oldM M
local notation "c" => (⟨dims,a⟩ : Chart)
local notation "values" x => fun h g=>actualBit B next h g x

def controlReceiver (h : Fin H) : Option B.next.V :=
  if got : ∃v,chosen v=h then some got.choose else none

theorem control_receiver_at (h : Fin H) (v : B.next.V) (present : controlReceiver B next h=some v) : chosen v=h := by
  unfold controlReceiver at present
  split at present
  next got=>exact Option.some.inj present ▸ got.choose_spec
  next=>contradiction

theorem control_receiver_none (h : Fin H) (absent : controlReceiver B next h=none) :
    ∀g x,actualBit B next h g x=0 := by
  intro g x
  have gone : ¬∃v,chosen v=h:=by
    intro got
    unfold controlReceiver at absent
    rw [dite_eq_left got] at absent
    contradiction
  unfold actualBit
  apply ite_eq_right
  rintro ⟨u,atHost,_,_⟩
  exact gone ⟨(B.next.placement.pos u).2,atHost⟩

def controlScalar (j : Fin 4) (h : Fin H) : ℕ :=
  (controlReceiver B next h).elim 0 (fun v=>![cap,(depthAt v)-cc+1,0,shapeId v] j)

/-- The attained mask, inverse and original depth read on occupied receivers
determine the full readback of all four source columns, including every empty row. -/
theorem recorded_control_sources (start : ℕ) (inverse depth levels : Bank) (m : Memory w)
    (resident : (c).Resident start m) (roof : (c).endAddress start < 2^w)
    (fitsI : inverse.Fits w ((c).endAddress start)) (fitsD : depth.Fits w ((c).endAddress start))
    (fitsL : levels.Fits w ((c).endAddress start))
    (active : ∀x : Block k,Source ((c).active start x.val) (values x) M m)
    (read : ∀(v : B.next.V) (x : Block k) (j : Fin (chunks J M)),let p : Row H J M:=(chosen v,j)
      ; let mask:=data (values x) p
      ; ((c).live start x.val).eval m ((row H J M p).val:Word w)=(((c).withMask mask 1).val:Word w) ∧
      ∀i : Fin 4,((c).ports start cap x.val inverse depth levels i).eval m ((row H J M p).val:Word w)=
        (((c).withMask mask (![cap,(depthAt v)-cc+1,0,shapeId v] i)).val:Word w)) :
    ∀x : Block k,(((c).live start x.val).Fits w ((c).endAddress start) ∧
      Source ((c).live start x.val) ((c).enabled (values x) (fun _=>1)) M m) ∧
      ∀j,((c).ports start cap x.val inverse depth levels j).Fits w ((c).endAddress start) ∧
        Source ((c).ports start cap x.val inverse depth levels j) ((c).enabled (values x) (controlScalar B previous next j)) M m := by
  intro x
  apply (c).source_ports_read start x cap inverse depth levels m resident roof fitsI fitsD fitsL (values x) (active x)
    (controlReceiver B next) (fun v=>(depthAt v)-cc+1) (fun v=>shapeId v)
  · intro h absent g
    exact control_receiver_none B next h absent g x
  · rintro ⟨h,chunk⟩ v present
    have same := control_receiver_at B next h v present
    subst h
    exact read v x chunk

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
