import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentPackedColumnBatch

namespace OAI
/-! # Native output pages for the eight ordinary route fields and shared ninth column -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Working memory before the output raster. It starts at the physical vector
end; the raster has five varying side fields and three varying route fields. -/
structure OriginPlan (l : Layout) where
  preparationWords : ℕ

namespace OriginPlan
variable {l : Layout} (o : OriginPlan l)

def grainBase (base : ℕ) :=base+o.preparationWords
def outputBase (base : ℕ) :=o.grainBase base+l.span
def routeWords :=o.preparationWords+l.span+(l.jobs*8)*l.span
def endAddress (base : ℕ) :=base+o.routeWords
def grain (base : ℕ) : Bank :=⟨o.grainBase base,Nat.clog 2 l.rows⟩
def page (base : ℕ) (j : Fin l.jobs) (f : Fin 8) : Bank :=
  ⟨o.outputBase base+(finProdFinEquiv (j,f)).val*l.span,Nat.clog 2 l.rows⟩

def side (base : ℕ) (j : Fin l.jobs) (f : Fin 6) : Bank :=
  if h:f.val<5 then o.page base j ⟨f.val,by omega⟩ else o.grain base

def route (base : ℕ) (j : Fin l.jobs) (f : Fin 3) :=o.page base j (Fin.natAdd 5 f)

theorem affine (base : ℕ) : o.endAddress base=o.outputBase base+(l.jobs*8)*l.span := by
  simp [endAddress,outputBase,grainBase,routeWords,Nat.add_assoc]
theorem positive : 0<o.routeWords := by
  have pos : 0<l.span:=Nat.two_pow_pos _
  unfold routeWords;omega

theorem page_room (base w : ℕ) (space : o.endAddress base<2^w) (j : Fin l.jobs) (f : Fin 8) :
    (o.page base j f).Fits w (o.endAddress base) ∧ l.rows≤(o.page base j f).size := by
  let t : Fin (l.jobs*8):=finProdFinEquiv (j,f)
  have high:=(Nat.mul_le_mul_right l.span (Nat.succ_le_of_lt t.isLt))
  rw [Nat.succ_mul] at high
  change (0<l.span ∧ l.span<2^w ∧ o.outputBase base+t.val*l.span+l.span≤_) ∧ _
  have pos : 0<l.span:=Nat.two_pow_pos _
  rw [o.affine] at space ⊢
  exact ⟨⟨pos,by omega,by omega⟩,Nat.le_pow_clog (by decide) _⟩

theorem grain_room (base w : ℕ) (space : o.endAddress base<2^w) :
    (o.grain base).Fits w (o.endAddress base) ∧ l.rows≤(o.grain base).size := by
  rw [o.affine] at space ⊢
  change (0<l.span ∧ l.span<2^w ∧ o.grainBase base+l.span≤_) ∧ _
  change o.grainBase base+l.span+_<2^w at space
  exact ⟨⟨Nat.two_pow_pos _,by omega,Nat.le_add_right ..⟩,Nat.le_pow_clog (by decide) _⟩

theorem ports_fit (base w : ℕ) (space : o.endAddress base<2^w) :
    (∀j f,(o.side base j f).Fits w (o.endAddress base) ∧ l.rows≤(o.side base j f).size) ∧
      ∀j f,(o.route base j f).Fits w (o.endAddress base) ∧ l.rows≤(o.route base j f).size := by
  refine ⟨?_,fun j f=>o.page_room base w space j _⟩
  intro j f
  unfold side
  split
  · exact o.page_room base w space j _
  · exact o.grain_room base w space

variable (source : Fin l.jobs→Fin 8→Expr)
def expression (i : ℕ) : Expr :=
  if h:i<l.jobs*8 then
    let indices : Fin l.jobs×Fin 8:=finProdFinEquiv.symm ⟨i,h⟩
    source indices.1 indices.2
  else .row

theorem real_expr (j : Fin l.jobs) (f : Fin 8) :
    expression source (finProdFinEquiv (j,f)).val=source j f := by
  simp only [expression,dite_eq_left (finProdFinEquiv (j,f)).isLt,Fin.eta,Equiv.symm_apply_apply]

def outputs (base : ℕ) :=DescentPackedFlowBatch.passes (o.outputBase base) l.rows l.span
  (expression source) 0 (l.jobs*8)

/-- Only earlier attained RAM expressions supply the raster. The same emitted
rows serve the true scalar resolver and every site of the public vector. -/
theorem publish {w : ℕ} (base : ℕ) (m : Memory w) (space : o.endAddress base<2^w)
    (before : ∀j f,(source j f).Fits w (o.outputBase base)) :
    let ps:=o.outputs source base
    (program w ps).Exec m (result ps m) (clock ps) ∧
      (∀(j : Fin l.jobs) (f : Fin 8) (i : Fin l.rows),
        result ps m ((o.page base j f).base+i.val)=(source j f).eval m (i.val:Word w)) ∧
      (∀a,a<o.outputBase base ∨ o.endAddress base≤ a→ result ps m a=m a) ∧ CheapCode (program w ps) := by
  intro ps
  have inputs : ∀i<l.jobs*8,(expression source i).Fits w (o.outputBase base) :=by
    intro i hi
    simp only [expression,dite_eq_left hi];exact before _ _
  have rows : l.rows≤ l.span:=Nat.le_pow_clog (by decide) _
  have valid:=DescentPackedFlowBatch.execute (o.outputBase base) l.rows l.span (l.jobs*8)
    (expression source) m inputs (o.affine base ▸ space) rows
  refine ⟨valid.1,?_,?_,program_cheap w ps⟩
  · intro j f i
    simpa only [ps,outputs,page,real_expr] using valid.2.1 (finProdFinEquiv (j,f)) i
  · intro i hi
    rcases hi with low|high
    · exact valid.2.2 i low
    · rw [o.affine] at high
      exact DescentPackedFlowBatch.above (o.outputBase base) l.rows l.span (expression source) m 0 _ i rows
        (by simpa only [Nat.zero_add] using high)

end OriginPlan
end
end Hierarchy.DescentDatedPriorOperand

end OAI
