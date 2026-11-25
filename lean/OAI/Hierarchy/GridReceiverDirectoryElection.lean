import OAI.Hierarchy.GridReceiverDirectory
import OAI.Hierarchy.GridReceiverTickDirectory
import OAI.Hierarchy.GridSelectorHistory
import OAI.Hierarchy.GridSimulationHistories

namespace OAI
/-! # Electing the published terminal roots at the selected receiving tick -/

noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing

namespace Hierarchy.GridReceiverDirectory

open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution TraceAdmission GridRegisteredSetting
open GridReceiverTickDirectory

variable {F : Type} [Field F] [Fintype F] {w pc rr pp size base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "W" => (64*w)
local notation "par" => parameters D l
local notation "N" => (par).roots
local notation "d" => ((l.dimension+1)+2)
local notation "T" => ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)
local notation "text" => SelfAdvice.textSize W pc pp
local notation "args" => GridNativeImage.parameterCount D l
local notation "u" => TraceAdmission.receiverAge w
local notation "radix" => (20*(w+1)+2)
local notation "units" => D.issuedUnit w l.degree l.stageRate l.rootRate

structure ElectionRoom : Prop where
  pos : 0<w
  teams_pos : 0<T
  rows : N*d ≤ GridPinArena.slab w
  thresholds : 20*(w+1)+1 ≤ GridPinArena.slab w
  items : N ≤ GridPinArena.slab w
  groups : radix^d ≤ GridPinArena.slab w
  steps : N*d*(20*(w+1)+1) < 2^W
  dim : d < 2^W
  ticks : T < 2^W
  low : (2+text)+(args+1)*W+W*GridReceiverHeader.count w ≤ GridDescription.sector w
  room : GridReceiverTickDirectory.Room (banks w u) W (2+text) N (radix^d*N)

local notation "bits" => GridPhysicalSelector.bits D.run
local notation "cut" => (2^(3*w/5))
local notation "cap" => l.selectorCap

/-- The register parser in T chooses precisely the history of the already
installed setting, including when the encoded prefix is shorter than its allowance. -/
theorem selected_registered (safe : GridNativeDispatch.WordRoom D)
    (fit : GridSelector.Room D.run.plan (GridNativeDispatch.actualTable D safe).codes bits cap)
    (z : D.trace) (sel : Fin (cap+1) → Bool)
    (encoded : sel=GridSelector.encode D.run.plan (GridNativeDispatch.actualTable D safe).codes
      bits cap fit (some z)) (room : cut≤cap)
    (bound : (stageCounts D.block D.passes (axes+1)).sum*D.block.alphabetCap*W≤cut)
    (h : D.run.plan.History) (tail : List Bool)
    (read : D.run.plan.read (GridNativeDispatch.actualTable D safe).codes
      (List.ofFn (fun j : Fin cut => GridStructuralHeader.selectorBit cap sel j.val)) = some (h,tail)) :
    h=z.1 := by
  let C:=GridNativeDispatch.actualTable D safe
  have sizeBound (v : D.run.plan.History) : (D.run.plan.write C.codes v).length≤cut := by
    rw [C.write_size]
    exact bound
  have decoded:=GridSelector.decode_encode D.run.plan C.codes bits cap fit (some z)
  rw [←encoded] at decoded
  apply GridSelector.recovered_eq D.run.plan C.codes bits cap sel cut sizeBound z decoded h tail
  have window := GridSelector.take_window (GridStructuralHeader.selectorBit cap sel) room
  have body : List.ofFn (Fin.tail sel) =
      List.ofFn (fun i : Fin cap => GridStructuralHeader.selectorBit cap sel i.val) :=
    (GridStructuralHeader.selector_body cap sel).symm
  rw [body, window]
  exact read

/-- The receiving classifier runs on the actual T resource matrix. Its output
list is the same ordered list of physical terminal ordinals charged by E. -/
theorem elect (geometry : ElectionRoom D l) (h : D.run.plan.History)
    (count : D.roots h=N) {addr : ℕ} (mem : Memory W)
    (reg :
      let idx:=Resources.indexEquiv D.run h count
      Resources.Registered addr (14*GridDescription.sector w) par
        (fun j => idx (D.run.plan.destination h (GridPhysicalAdmission.initialLane (Nat.succ_pos axes) j)))
        (fun v => units*D.run.chargeAt h D.issuedCharges
          (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) (idx.symm v)) mem)
    (t : Fin T) (textFit : text≤w^2) (self : Fin (w^2)→Bool) (words : Fin args→Word W)
    (sel : Fin (cap+1)→Bool)
    (header : let hdr:=GridReceiverHeader.header text textFit self (t.val : Word W) words sel
      ∀ i : Fin hdr.length,mem (2+i.val)=((hdr[i.val]).toNat:Word W)) :
    let cost:=D.costs (GridNativeImage.resources D l) h l.dimension l.sideMinusOne l.bank D.issuedCharges units
    (receiver w u text args N d T).Spec (·=mem)
      (fun _ out => ∃ mid, GridSimulation.Assigned geometry.teams_pos cost mem mid ∧
        Ticked (banks w u) (FactorAllocation.factors w cost (List.finRange (D.roots h)) t)
          (t.val:Word W) mid out)
      (GridSimulation.assignTime w N d+clock W (radix^d*N)) := by
  intro cost
  have registered:=GridRegisteredOrder.registered D par h D.issuedCharges units l.dimension l.sideMinusOne l.bank count reg
  let p:=D.parameters par h l.dimension l.sideMinusOne l.bank
  have rootCount : p.roots=N:=count
  have directions : p.directions = l.dimension + 1 := rfl
  have code_eq : receiver w u text args N d T = receiver w u text args p.roots (p.directions+2) T := by
    rw [rootCount, directions]
  have time_eq : GridSimulation.assignTime w N d + clock W (radix^d*N) =
      GridSimulation.assignTime w p.roots (p.directions+2) + clock W (radix^(p.directions+2)*p.roots) := by
    rw [rootCount, directions]
  rw [code_eq, time_eq]
  intro P R K machine
  exact receiver_registered (v:=u) geometry.pos geometry.teams_pos textFit self words sel p
    (D.dest h) (D.work h D.issuedCharges units) t mem registered
    (by simpa only [rootCount, directions] using geometry.rows) geometry.thresholds
    (by simpa only [rootCount] using geometry.items) geometry.groups
    (by simpa only [rootCount, directions] using geometry.steps) geometry.dim geometry.ticks geometry.low
    (by simpa only [rootCount, directions] using geometry.room) header machine

end Hierarchy.GridReceiverDirectory
end

end OAI
