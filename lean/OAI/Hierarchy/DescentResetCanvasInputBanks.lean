import OAI.Hierarchy.DescentResetCanvasIngress

namespace OAI
namespace Hierarchy.DescentResetCanvasIngress.Layout
open DescentSIMDLookup ProtocolRAM

noncomputable def tokenAt (L : DescentResetCanvasIngress.Layout) (base x j : ℕ) : Bank :=
  if hx:x<2^L.k then if hj:j<2*L.cap then L.tokens base (⟨x,hx⟩,⟨j,hj⟩) else ⟨0,0⟩ else ⟨0,0⟩

@[simp] theorem tokenAt_slot (L : DescentResetCanvasIngress.Layout) (base : ℕ) (x : Fin (2^L.k)) (j : Fin (2*L.cap)) :
    L.tokenAt base x.val j.val=L.tokens base (x,j) := by simp [tokenAt,x.isLt,j.isLt]

theorem input_banks (L : DescentResetCanvasIngress.Layout) {w base : ℕ} (fit : L.endAddress base<2^w) :
    (L.source base).Fits w (L.endAddress base) ∧ L.hosts*chunks L.groups L.targetLanes≤(L.source base).size ∧
    ∀t,(L.tokens base t).Fits w (L.endAddress base) ∧ L.hosts*chunks L.groups L.targetLanes≤(L.tokens base t).size := by
  obtain ⟨_,one,two⟩:=L.order base
  have roof:=one.trans two
  have src:=(L.collector.bounds fit).2
  refine ⟨src.1,src.2,?_⟩
  intro t
  obtain ⟨bank,rows⟩:=(L.signed.room (roof.trans_lt fit)).2.2 t
  exact ⟨⟨bank.1,bank.2.1,bank.2.2.trans roof⟩,rows⟩

end Hierarchy.DescentResetCanvasIngress.Layout

end OAI
