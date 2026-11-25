import OAI.Hierarchy.TaggedWireMatrixTrace

namespace OAI
/-! # Signed chronological expansion proved only at actual reachable prefixes -/

noncomputable section
set_option maxHeartbeats 800000
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar Tagged LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped BigOperators Classical
variable {X : Type} {slot : Event→Slot X} {events : List Event} {x₀ : X}

def finish : ∀ {tail x},Prefix slot events x₀ tail x→(p : Path slot tail x)→Prefix slot events x₀ [] (terminal slot tail x p)
  | [],_,h,_=>h
  | _::_,_,h,p=>finish (.advance h p.1) p.2

variable {S : ℕ} {F : Type*} [Field F] (width : ∀{tail x},Prefix slot events x₀ tail x→Widths S)
    (operator : ∀ {e tail x} (h : Prefix slot events x₀ (e::tail) x) (c : (slot e).choice x),
      SiteMatrix (State (width h)) (State (width (advance h c))) F)

def matrix (width : ∀ {tail x},Prefix slot events x₀ tail x→Widths S)
    (operator : ∀ {e tail x} (h : Prefix slot events x₀ (e::tail) x) (c : (slot e).choice x),
      SiteMatrix (State (width h)) (State (width (advance h c))) F) : ∀{tail x},(h : Prefix slot events x₀ tail x)→(j : Path slot tail x)→
    SiteMatrix (State (width h)) (State (width (finish h j))) F
  | [],_,h,_=>SiteMatrix.identity (State (width h))
  | _::_,_,h,p=>SiteMatrix.compose (operator h p.1) (matrix (width:=@width) (operator:=@operator) (advance h p.1) p.2)

theorem matrix_sum
    (law : ∀{e tail x} (h : Prefix slot events x₀ (e::tail) x) (v : ∀s,State (width h) s),(raw F (width h)).coeff v=
      ∑c,SiteMatrix.act (operator h c) (raw F (width (advance h c))).coeff v)
    {tail : List Event} {x : X} (h : Prefix slot events x₀ tail x) (v : ∀s,State (width h) s) :
    (raw F (width h)).coeff v=
      ∑p : Path slot tail x,SiteMatrix.act (Prefix.matrix (width:=@width) (operator:=@operator) h p)
        (raw F (width (finish h p))).coeff v := by
  induction tail generalizing x with
  | nil=>
    change _ = ∑ _ : Unit,SiteMatrix.act (SiteMatrix.identity (State (width h))) (raw F (width h)).coeff v
    simp only [Fintype.sum_unique]
    exact (SiteMatrix.act_id (B:=State (width h)) (raw F (width h)).coeff v).symm
  | cons e tail ih=>
    rw [law h v]
    change _=∑p : Σc:(slot e).choice x,Path slot tail ((slot e).next x c),_
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    let k:=advance h c
    have rest : (raw F (width k)).coeff=fun y=>∑p : Path slot tail ((slot e).next x c),
        SiteMatrix.act (Prefix.matrix (width:=@width) (operator:=@operator) k p) (raw F (width (finish k p))).coeff y :=
      funext fun y=>ih k y
    rw [rest,SiteMatrix.act_sum]
    exact Finset.sum_congr rfl (fun j _=>SiteMatrix.act_compose (operator h c)
      (Prefix.matrix (width:=@width) (operator:=@operator) k j) _ v)

def expansion {tail : List Event} {x : X}
    (h : Prefix slot events x₀ tail x) (law : ∀{e tail x} (p : Prefix slot events x₀ (e::tail) x) (v : ∀s,State (width p) s),(raw F (width p)).coeff v=
      ∑c,SiteMatrix.act (operator p c) (raw F (width (advance p c))).coeff v) :
    Expansion (raw F (width h)) (Path slot tail x) (fun j=>width (finish h j)) where
  part j v:=SiteMatrix.act (Prefix.matrix (width:=@width) (operator:=@operator) h j) (raw F (width (finish h j))).coeff v
  sum:=by
    funext v
    rw [Finset.sum_apply]
    exact Prefix.matrix_sum (width:=@width) (operator:=@operator) law h v
  image j:=by
    refine ⟨Prefix.matrix (width:=@width) (operator:=@operator) h j,fun v=>?_⟩
    exact state_sum_congr _ _ _

end Hierarchy.WireTelescope.CalendarTape.Prefix

end
end OAI
