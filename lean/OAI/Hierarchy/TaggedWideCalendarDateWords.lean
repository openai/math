import OAI.Hierarchy.TaggedWideCalendarDateRow

namespace OAI
/-! # The native per-role data ports before and after a clipping substep -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged Tagged.WideStack Tagged.WideControlJoin WireTelescope WireTelescope.CalendarTape
open ProtocolRAM.Calendar Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {R D Ex Sel : Type} [Fintype R] [Fintype D] [Fintype Ex] [Fintype Sel] (G : Gate)
    {K degree cap : ℕ} (es : List Event) (room : R→ℕ) (slots : R↪Fin (K*degree))
    (wire : Fin ((es.length+1)*Fintype.card ((r:R)×Fin (room r)))→D)
    (j : Fin es.length) (s : Fin K)
local notation "mid" => Fin (degree*cap)
local notation "V" => SitePins Ex Sel D G
local notation "aug" => SitePins Ex Sel (D⊕mid) G

/-- The old and the published new values come from their actual adjacent
chronological sheets. Each admissible position in the local middle bank is
shared by both the signed output and the spill input. -/
def outerWord (side : Bool) (q : Fin degree) (b : Fin cap) : V⊕Bool :=
  Sum.map (fun d=>Sum.inr (Sum.inr (Sum.inl d))) id (datedRole es room slots wire j s side q b.val)

def substepWord (clip side : Bool) (q : Fin degree) (b : Fin cap) : aug⊕Bool :=
  if clip=side then
    Sum.map (fun d=>Sum.inr (Sum.inr (Sum.inl (Sum.inl d)))) id (datedRole es room slots wire j s side q b.val)
  else .inl (.inr (.inr (.inl (.inr (finProdFinEquiv (q,b))))))

variable (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool) (out : Memory G.W)
    (h : Fin (degree*cap)→Bool)
local notation "v" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

omit [Fintype D] [Fintype Ex] [Fintype Sel] in
theorem outerWord_at (side : Bool) (q : Fin degree) (r : R) (atSlot : slots r=finProdFinEquiv (s,q))
    (b : Fin cap) (within : b.val<room r) :
    Sum.elim v id (outerWord G es room slots wire j s side q b)=
      data (wire (timeOrder es (if side then j.succ else j.castSucc,⟨r,b.val,within⟩))) := by
  rw [outerWord,datedRole_at es room slots wire j s side q r atSlot ⟨b.val,within⟩]
  rfl

omit [Fintype D] [Fintype Ex] [Fintype Sel] in
theorem substepWord_outer (side : Bool) (q : Fin degree) (b : Fin cap) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data h) (G.terminal out))))
      id (substepWord G es room slots wire j s side side q b)=
      Sum.elim v id (outerWord G es room slots wire j s side q b) := by
  simp only [substepWord,outerWord]
  cases datedRole es room slots wire j s side q b.val <;>rfl

omit [Fintype D] [Fintype Ex] [Fintype Sel] in
theorem substepWord_middle (clip : Bool) (q : Fin degree) (b : Fin cap) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data h) (G.terminal out))))
      id (substepWord G es room slots wire j s clip (!clip) q b)=h (finProdFinEquiv (q,b)) := by
  cases clip <;>rfl

theorem middle_at {B : Widths K} (place : SiteBit B s↪mid) (state : State B s)
    (a : SiteBit B s) : middle s place state (place a)=siteBits B s state a := by
  let e:=Equiv.ofInjective place place.injective
  have occupied : place a∈Set.range place:=⟨a,rfl⟩
  change WidePadding.pad _ (fun i=>siteBits B s state (e.symm i)) (place a)=_
  rw [WidePadding.pad,dite_eq_left occupied]
  exact congrArg (siteBits B s state) (e.symm_apply_apply a)

theorem middle_vacant {B : Widths K} (place : SiteBit B s↪mid) (state : State B s)
    (i : mid) (vacant : i∉Set.range place) : middle s place state i=false := by
  simp [middle,WidePadding.pad,vacant]

end Hierarchy.ProbeStage.CoreBoard.LedgerStep
end

end OAI
