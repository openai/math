import OAI.Hierarchy.DescentResetFlowColumns
import OAI.Hierarchy.DescentResetMeasuredFields
import OAI.Hierarchy.DescentResetPortLevels

namespace OAI
/-! # The two signed directions use one measured old cable column -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentColonies DescentGL DescentIssuedFallbackPanel DescentPlainTerminal.Suffix
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k m c H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (hosts : V≃Fin H) (digits : Block m≃J×Block k)
    (small : c≤ m) (sym : ∀v u,u∈A.near v→v∈A.near u)
    (b : V→ℕ) (L : DescentGL.Layout m) (f B K cap : ℕ)
local notation "T" => A.resetFlow digits
private theorem reciprocal (v u : V) (h : u∈A.mutual v) : v∈A.mutual u :=
  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).2,(Finset.mem_filter.mp h).1⟩

local notation "recip" => reciprocal A
local notation "vec" => ContactRoster.dart A.mutual (portAt A hosts) (actual_ports A hosts sym) recip

/-- The genuine predecessor amount bank already stores zero at an unused socket. -/
theorem raw_port (v : V) (i : Fin A.degree) (x : Block m) :
    raw A hosts digits i (hosts v) x=(portAt A hosts v i).elim 0 (fun u=>T v u x) := by
  unfold raw portAt
  cases got : next A hosts (hosts v) i with
  | none=>rfl
  | some u=>simp [Equiv.symm_apply_apply,GroupStage.resetFlow]

def half (p : Fin A.degree ⊕ Fin A.degree) := Sum.elim id id p

def portData (v : V) (hi : Block c) (i : Fin A.degree) (j : Fin 2⊕Block (m-c)) :=
  match j with
  | .inl s=>(portAt A hosts v i).elim 0 (fun u=>
      let depth:=max (b v) (b u)
      if s.val=0 then depth-c else threshold K (2^f*B) depth (∑x,T v u x) (2^(m-c)*cap))
  | .inr x=>raw A hosts digits i (hosts v) ((rearrange L).symm (join small hi x))

theorem signed_port (v : V) (hi : Block c) (p : Fin A.degree⊕Fin A.degree) (j : Fin 2⊕Block (m-c)) :
    Stencil.edgeWords small A.mutual b L T f B K cap hi (vec v p) j=
      portData A hosts digits small b L f B K cap v hi (half (A:=A) p) j := by
  cases p with
  | inl i=>
    cases result : portAt A hosts v i with
    | none=>cases j <;> simp [half,portData,ContactRoster.dart,Stencil.edgeWords,raw_port,result]
    | some u=>cases j <;> simp [half,portData,ContactRoster.dart,Stencil.edgeWords,raw_port,result,edgeLevel]
  | inr i=>
    cases result : portAt A hosts v i with
    | none=>cases j <;> simp [half,portData,ContactRoster.dart,Stencil.edgeWords,raw_port,result]
    | some u=>
      have flipped (x : Block m) : T u v x=T v u x:=A.mutual_reset_flow digits u v x
      cases j <;> simp [half,portData,ContactRoster.dart,Stencil.edgeWords,raw_port,result,edgeLevel,
        max_comm (b u) (b v),flipped]

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
