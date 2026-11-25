import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentDatedOrdinaryOperands
import OAI.Hierarchy.DescentDatedPriorOperandRate
import OAI.Hierarchy.DescentOrdinaryFinalRate

namespace OAI
/-! # Finite address rates for the three ordinary operand books at their actual pitches -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup Filter
noncomputable section
set_option quotPrecheck false

namespace PhysicalOrdinary
variable {F P : Type} [Field F]

structure OperandWidths (v : PhysicalOrdinary F P) (h : ℕ) : Prop where
  state : v.vector.stateBits≤h
  book : (v.vector.bookBits*v.vector.radix)*v.vector.lanes≤h
  prior : ((v.resolver.size+2)*v.resolver.nodes)*v.resolver.lanes≤h
  resolve : (11*(v.resolver.size+2))*v.resolver.lanes≤h
  finalBook : v.operandBook.lookupUnit*v.operandBook.layout.lanes≤h

structure OperandRooms {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i : ι h),PhysicalOrdinary F (Pins h i)) where
  vector : DescentOperandVectorArena.Layout.ScalarRoom (fun h i=>(v h i).vector)
  resolver : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i=>(v h i).resolver)
  finalBook : DescentOrdinaryFinal.Chart.ScalarRoom (fun h i=>(v h i).operandBook)

theorem operand_rooms {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i : ι h),PhysicalOrdinary F (Pins h i))
    (width : ∀ᶠ h in atTop,∀i,(v h i).OperandWidths h)
    (geometry : ∀h i,(v h i).VectorShape)
    (final : ∀h i,(v h i).operandBook=(v h i).finalChart)
    (norm : ∀h i,(v h i).vector.normalizedRows=0)
    (oldH : Bounded (fun h i=>(v h i).vector.hosts)) (low : Bounded (fun h i=>(v h i).vector.lows))
    (nodes : Bounded (fun h i=>(v h i).resolver.nodes)) (args : Bounded (fun h i=>(v h i).vector.operands))
    (blocks : Bounded (fun h i=>(v h i).vector.radix)) (groups : Bounded (fun h i=>(v h i).vector.groups))
    (lanes : Bounded (fun h i=>(v h i).vector.lanes)) :
    OperandRooms v := by
  let V : DescentOperandVectorArena.Layout.ScalarRoom (fun h i=>(v h i).vector) :=
    ⟨args,(Bounded.const 0).of_le (fun h i=>(norm h i).le),oldH,low,groups,blocks,lanes,1,by
      filter_upwards [width] with h hw
      simpa only [one_mul] using fun i=>And.intro (hw i).state (hw i).book⟩
  have H : Bounded (fun h i=>(v h i).resolver.hosts) :=
    (oldH.mul low).of_le (fun h i=>(geometry h i).hosts.le)
  have G₀ : Bounded (fun h i=>(v h i).resolver.groups) :=groups.of_le (fun h i=>(geometry h i).groups.le)
  have M₀ : Bounded (fun h i=>(v h i).resolver.lanes) :=lanes.of_le (fun h i=>(geometry h i).lanes.le)
  let R : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i=>(v h i).resolver) :=
    ⟨blocks.of_le (fun h i=>(geometry h i).blocks.le),nodes,args.of_le (fun h i=>(geometry h i).operands.le),
      H,G₀,M₀,1,by
      filter_upwards [width] with h hw
      simpa only [one_mul] using fun i=>And.intro (hw i).prior (hw i).resolve⟩
  have batch : Bounded (fun h i=>chunks (v h i).resolver.groups (v h i).resolver.lanes) :=
    (G₀.add M₀).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows : Bounded (fun h i=>(v h i).resolver.rows):=H.mul batch
  refine ⟨V,R,?_,?_,?_,?_,1,?_⟩
  · exact nodes.of_le fun h i=>by rw [final h i];rfl
  · exact R.arities.of_le fun h i=>by rw [final h i];rfl
  · exact R.blocks.of_le fun h i=>by rw [final h i];rfl
  · exact rows.of_le fun h i=>by rw [final h i];rfl
  · filter_upwards [width] with h hw
    intro i
    change (v h i).operandBook.lookupUnit*(v h i).operandBook.layout.lanes ≤ 1*h
    simpa only [one_mul] using (hw i).finalBook

end PhysicalOrdinary
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

theorem ordinary_operand_widths : (v).OperandWidths payload := by
  let A:=(base).registeredEntry prior floor
  have bounds:=((base).registered_width prior floor).1
  have lane : (v).resolver.lanes≤A.clip.working:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have smaller (j : Fin 16) : (v).argumentWidths A j*(v).resolver.lanes≤payload :=
    ((Nat.mul_le_mul_left _ lane).trans (bounds j)).trans (Nat.div_le_self ..)
  refine ⟨Nat.zero_le _,?_,smaller 8,smaller 10,smaller 13⟩
  rw [Nat.mul_assoc,Nat.mul_comm (v).vector.radix (v).vector.lanes]
  exact (bounds 7).trans (Nat.div_le_self ..)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
