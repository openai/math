import OAI.Computability.BorderVNP.RoutingISACellControlGather
import OAI.Computability.BorderVNP.RoutingISACellControlMemory
import OAI.Computability.BorderVNP.RoutingISATypedTaskStep

/-! # Emitting both sparse control tables in one ownership branch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellControlRows

open VPVNP.BurstRAM Packing.Directory.ISA TypedTaskBuilder
open private pushEval pushSafe from OAI.Computability.BorderVNP.RoutingISATypedTaskStep

private def written (z : NatState) (a : ℕ) (rs : List Reg) : NatState :=
  ⟨Function.update z.reg 20 (a+rs.length),putNat z.mem a (rs.map z.reg)⟩

private theorem pushAt_run (pub : Arg → ℕ) (z : NatState) (w : ℕ) (stride base : Reg) (rs : List Reg)
    (one : z.reg 1=1) (hb : base ≠ 20) (hr : ∀ r ∈ rs, r ≠ 20)
    (fit : z.reg base+z.reg stride*z.reg 19+rs.length < 2^w) :
    let a := z.reg base+z.reg stride*z.reg 19
    (pushAt stride base rs).fixedSafe w pub z ∧ (pushAt stride base rs).fixedEval pub z=written z a rs := by
  intro a
  let g : Code := .block [.binary .mul 20 stride 19,.binary .add 20 base 20]
  let u : NatState := ⟨Function.update z.reg 20 a,z.mem⟩
  have first : g.fixedEval pub z=u := by
    simp (config := {decide:=true}) [g,Code.block,Code.fixedEval,Code.evalNat,addressOp,hb,u,a]
  have safe : g.fixedSafe w pub z := by
    simp (config := {decide:=true}) [g,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,hb]
    omega
  change (g.fixedSafe w pub z ∧ (pushWords rs).fixedSafe w pub (g.fixedEval pub z)) ∧
    (pushWords rs).fixedEval pub (g.fixedEval pub z)=_
  rw [first]
  have h1 : u.reg 1=1 := by simp [u,one]
  have ptr : u.reg 20=a := by simp [u]
  have map : rs.map u.reg=rs.map z.reg := by apply List.map_congr_left; intro r h; exact Function.update_of_ne (hr r h) ..
  refine ⟨⟨safe,pushSafe rs pub u w h1 (by rwa [ptr])⟩,?_⟩
  rw [pushEval rs pub u a h1 ptr hr,map]
  simp only [written,u,Function.update_idem]

private abbrev rs6 : List Reg := [22,23,24,25,26,27]
private abbrev rs4 : List Reg := [28,29,30,31]

private def both (l : Layout) (mem : ℕ → ℕ) (i j : ℕ) (z : NatState) : NatState :=
  let a := l.six+6*j
  let b := l.four+4*j
  ⟨Function.update (Function.update z.reg 20 (b+4)) 19 (j+1),
    putNat (putNat z.mem a (l.rowSix mem i)) b (l.rowFour i)⟩

/-- The native branch writes exactly the six and four public fields in their designated spans. -/
private theorem emit_exact (l : Layout) (mem : ℕ → ℕ) (pub : Arg → ℕ) (w i j : ℕ)
    (z : NatState) (h : l.Gathered mem i j z) (hj : j < l.cells) (fit : l.Room w) :
    emit.fixedSafe w pub z ∧ emit.fixedEval pub z=both l mem i j z := by
  let u := written z (l.six+6*j) rs6
  have one : z.reg 1=1 := h.ready 1 (by decide)
  have jj : z.reg 19=j := h.ready 19 (by decide)
  have six : z.reg 17=l.six := h.ready 17 (by decide)
  have k6 : z.reg 4=6 := h.ready 4 (by decide)
  have x := pushAt_run pub z w 4 17 rs6 one (by decide) (by decide) (by
    rw [six,k6,jj]; change l.six+6*j+6 < 2^w; have := fit.result.2; omega)
  rw [six,k6,jj] at x
  have y4 : u.reg 3=4 := by simpa (config := {decide:=true}) [u,written,Layout.regValue] using h.ready 3 (by decide)
  have yb : u.reg 11=l.four := by simpa (config := {decide:=true}) [u,written,Layout.regValue] using h.ready 11 (by decide)
  have yj : u.reg 19=j := by simpa [u,written] using jj
  have y1 : u.reg 1=1 := by simpa [u,written] using one
  have y := pushAt_run pub u w 3 11 rs4 y1 (by decide) (by decide) (by
    rw [yb,y4,yj]; change l.four+4*j+4 < 2^w; have := fit.result.1; omega)
  rw [yb,y4,yj] at y
  let v := written u (l.four+4*j) rs4
  have finalJ : v.reg 19=j := by simpa [v,written] using yj
  have final1 : v.reg 1=1 := by simpa [v,written] using y1
  have map4 : rs4.map u.reg=l.rowFour i := by simpa (config := {decide:=true}) [rs4,u,written] using h.four
  let a := pushAt 4 17 rs6
  let b := pushAt 3 11 rs4
  change (a.fixedSafe w pub z ∧ b.fixedSafe w pub (a.fixedEval pub z) ∧
    (Code.binary .add 19 19 1).fixedSafe w pub (b.fixedEval pub (a.fixedEval pub z))) ∧
    (Code.binary .add 19 19 1).fixedEval pub (b.fixedEval pub (a.fixedEval pub z))=_
  have ax : a.fixedEval pub z=u := x.2
  have by' : b.fixedEval pub u=v := y.2
  rw [ax,by']
  refine ⟨⟨x.1,y.1,?_⟩,?_⟩
  · change v.reg 19+v.reg 1 < 2^w
    rw [finalJ,final1]; have := fit.result.1; omega
  · simp only [Code.fixedEval,Code.evalNat,addressOp,finalJ,final1]
    change NatState.mk (Function.update (Function.update u.reg 20 (l.four+4*j+rs4.length)) 19 (j+1))
      (putNat u.mem (l.four+4*j) (rs4.map u.reg)) = _
    rw [map4]
    simp only [both,u,written,h.six,Function.update_idem,rs4,List.length_cons,List.length_nil]

end RoutingISA.CellControlRows

end BorderVNP
end Computability
end OAI
