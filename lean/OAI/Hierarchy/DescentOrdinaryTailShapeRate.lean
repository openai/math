import OAI.Hierarchy.DescentSelectedMaterialRates
import OAI.Hierarchy.DescentResetRetainedCalendarWidths
import OAI.Hierarchy.DescentReturnTailRate
import OAI.Hierarchy.DescentPublicDegreeNumbers

namespace OAI
/-! # Residual-date rate of the actual host growth, degree, capacity, node count, and arity -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem shape_rates (t f gain reset : ℕ) : ∃rate : ℕ,∀J D cap : ℕ,
    D≤ maximumDegree t → cap≤2^(8+capRate G t gain*((t+1)*J)) →
    let k:=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)
    2*(2^hostRate t reset*2^k)+2^k+ordinaryDegree D+2^gainExponent 20 D*G.b*cap≤ scale J rate :=by
  let I:=MaterialPoint t (capRate G t gain) (maximumDegree t)
  let age : I→ℕ:=MaterialPoint.age
  let num:=AgeBound.const age
  have table (func : ℕ→ℕ) : AgeBound age (fun x:I=>func x.degree):=by
    apply (num (∑j : Fin (maximumDegree t+1),func j.val)).mono
    intro x
    let j:Fin (maximumDegree t+1):=⟨x.degree,Nat.lt_succ_of_le x.deg⟩
    exact Finset.single_le_sum (f:=fun j:Fin (maximumDegree t+1)=>func j.val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have rad:=AgeBound.radix (age:=age) t (hostRate t reset) (capRate G t gain) (cutRate t f gain)
  have caps : AgeBound age (fun x:I=>x.cap):=AgeBound.dated_cap (i:=fun x=>(t+1)*age x) (fun _=>le_rfl) (fun x=>x.capacity)
  have gath:=((num 2).mul ((num (2^hostRate t reset)).mul rad)).add rad
  have lots:=(table (fun D=>2^gainExponent 20 D)).mul (num G.b) |>.mul caps
  obtain ⟨e,all⟩:=(gath.add (table ordinaryDegree)).add lots
  exact ⟨e,fun J D cap hd hc=>all (⟨J,D,cap,hd,hc⟩:I)⟩

def tailLayoutRate (t f gain reset driftWidth unitWidth : ℕ) :=
  let zero:=stageNumbers G t 0 f gain reset 0 0
  (shape_rates G t f gain reset).choose+zero.localTokenExponent+(driftWidth+operandExponent G zero)+unitWidth

theorem layout_widths (t f gain reset J M tail D cap drift driftWidth u unitWidth n a : ℕ)
    (hd : D≤ maximumDegree t) (hc : cap≤2^(8+capRate G t gain*((t+1)*J)))
    (dr : drift+1≤ scale J driftWidth) (cost : u≤ scale J unitWidth) :
    let S:=stageNumbers G t J f gain reset M tail
    let k:=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)
    n≤S.retainedNodes → a≤S.retainedArgumentsAt G drift →
    ∀j∈[2*(2^S.hostGain*2^k),u,2^k,ordinaryDegree D,2^gainExponent 20 D*G.b*cap,n,a],
      j≤ scale J (tailLayoutRate G t f gain reset driftWidth unitWidth) :=by
  intro S k nodes args j hj
  let zero:=stageNumbers G t 0 f gain reset 0 0
  let shape:=(shape_rates G t f gain reset).choose
  let rate:=tailLayoutRate G t f gain reset driftWidth unitWidth
  have mono {s t : ℕ} (le : s≤t) : scale J s≤ scale J t:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  have cluster:=(shape_rates G t f gain reset).choose_spec J D cap hd hc
  change 2*(2^S.hostGain*2^k)+2^k+ordinaryDegree D+2^gainExponent 20 D*G.b*cap≤ scale J shape at cluster
  have sh : scale J shape≤ scale J rate:=mono (by dsimp [rate,tailLayoutRate,shape];omega)
  have un : u≤ scale J rate:=cost.trans (mono (by dsimp [rate,tailLayoutRate];omega))
  have c:=S.capacities_at_scale G drift driftWidth dr
  have nd : n≤ scale J rate:=nodes.trans (c.1.trans (mono (by
    change zero.localTokenExponent≤rate;dsimp [rate,tailLayoutRate,zero];omega)))
  have ar : a≤ scale J rate:=args.trans (c.2.trans (mono (by
    change driftWidth+operandExponent G zero≤rate;dsimp [rate,tailLayoutRate,zero];omega)))
  change j ≤ scale J rate
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  have total := cluster.trans sh
  have firstThree := Nat.le_of_add_right_le total
  have firstTwo := Nat.le_of_add_right_le firstThree
  rcases hj with h|h|h|h|h|h|h <;> subst j
  · exact Nat.le_of_add_right_le firstTwo
  · exact un
  · exact Nat.le_of_add_left_le firstTwo
  · exact Nat.le_of_add_left_le firstThree
  · exact Nat.le_of_add_left_le total
  · exact nd
  · exact ar

end
end Hierarchy.DescentSixParty.Chronology

end OAI
