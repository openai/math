import OAI.Hierarchy.DescentDatedPriorOperandRate
import OAI.Hierarchy.DescentDatedOperandProgram

namespace OAI
/-! # Uniform cost of the literal all-slot shape and clock in each ordinary date -/
namespace Hierarchy.DescentDatedPriorOperand.Layout
open DescentDatedAddressBook DescentSIMDLookup Filter
variable {ι : ℕ→Type*}

theorem cost_rates (l : ∀h,ι h→Layout) (b : ScalarRoom l) :
    Bounded (fun h i=>(l h i).clockBudget) ∧ Bounded (fun h i=>(l h i).hardwareBudget) :=by
  obtain ⟨K,fit⟩:=b.width
  have dt:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).1)
  have dict : Bounded (fun h i=>(l h i).dictionary):=b.nodes.mul dt
  have decoder : Bounded (fun h i=>(l h i).resolverPage):=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2)
  have span : Bounded (fun h i=>(l h i).splicePage):=by
    apply decoder.of_le
    intro h i;apply Nat.pow_le_pow_right (by decide);apply Nat.mul_le_mul_right;omega
  have batch : Bounded (fun h i=>chunks (l h i).groups (l h i).lanes):=
    (b.groups.add b.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rs : Bounded (fun h i=>(l h i).rows):=b.hosts.mul batch
  have jobs_ : Bounded (fun h i=>(l h i).jobs):=b.blocks.mul (b.nodes.mul b.arities)
  have cols : Bounded (fun h i=>(l h i).columns):=((Bounded.const 7).mul b.arities).mul b.nodes
  constructor <;> simp only [clockBudget,hardwareBudget,clockPer,textPer] <;>
    repeat' first | assumption | exact Bounded.const _ | apply Bounded.add | apply Bounded.mul

theorem clock_rate (l : ∀h,ι h→Layout) (b : ScalarRoom l) : Bounded (fun h i=>(l h i).clockBudget):=(cost_rates l b).1

theorem hardware_rate (l : ∀h,ι h→Layout) (b : ScalarRoom l) : Bounded (fun h i=>(l h i).hardwareBudget):=(cost_rates l b).2

theorem program_rates (l : ∀h,ι h→Layout) (b : ScalarRoom l) (t : ∀h i,Banks (l h i)) (floor width : ∀h,ι h→ℕ) :
    Bounded (fun h i=>(t h i).ticks (floor h i)) ∧
    Bounded (fun h i=>DescentStaticWordColumn.names ((t h i).program (width h i) (floor h i))) :=
  ⟨(clock_rate l b).of_le (fun h i=>((t h i).priced (width h i) (floor h i)).1),
   (hardware_rate l b).of_le (fun h i=>((t h i).priced (width h i) (floor h i)).2)⟩
end Hierarchy.DescentDatedPriorOperand.Layout

end OAI
