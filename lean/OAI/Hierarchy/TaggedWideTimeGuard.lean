import OAI.Hierarchy.TaggedWideTimeOccupancy
import OAI.Hierarchy.TaggedWidePadding
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # A fixed physical zero-suffix test for every date and named site port -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing Diagonal TraceWords
open ProtocolRAM.Calendar Tagged.WidePadding Computability.VPVNP.BurstRAM
open scoped Classical BigOperators

variable {F H V : Type} [Field F] [Fintype H] [Fintype V] (cap : H→ℕ)
    (es : List Event) {b : ℕ} (fits : ∀p,cap p≤2^b)
local notation "Q" => (p:H) × Fin (cap p)
local notation "N" => (es.length+1)*Fintype.card Q
variable (widthPin : Fin (es.length+1) → H → Fin b → V) (data : Fin ((es.length+1)*Fintype.card ((p : H) × Fin (cap p))) → V)

def guardPorts : Ports (V⊕Bool) N b where
  col i := let q := ((timeOrder («Q»:=Q) es).symm i).2; q.2.castLE (fits q.1)
  live _ := .inr true
  width i j := let q := (timeOrder («Q»:=Q) es).symm i; .inl (widthPin q.1 q.2.1 j)
  payload i := .inl (data i)

def timeGuard : BitNetwork F (Fintype.card V) :=
  Tagged.WideHost.localFamily (A:=fun _ : Unit=>V⊕Bool) (fun _ : Unit=>(guardPorts cap es fits widthPin data).network (F:=F))
    (fun _ x=>x)

theorem timeGuard_cost :
    let net := timeGuard (F:=F) cap es fits widthPin data
    net.cells+net.internal ≤ N*(200*b+65) := by
  intro net
  rw [show net.cells+net.internal=_ from Tagged.WideHost.localFamily_size ..]
  simpa using (guardPorts cap es fits widthPin data).cost (F:=F)

variable {S : ℕ} {X : Type} (slot : Event → Slot X) (wire : X → Widths S)
    (cells : ∀ x,(Σs,SiteBit (wire x) s) ↪ ((p : H) × Fin (cap p)))

/-- Only the low logarithmic-width bits of each real native width are
fed to the gate. The true date, role, and digit agree with the original
calendar's half-edges, including permanently vacant and zero-width rows. -/
theorem timeGuard_value (start : X) (j : Path slot es start) (v : V → Bool)
    (words : Fin (es.length+1) → H → Word b)
    (reads : ∀t p d,v (widthPin t p d)=TraceWords.bits (words t p) d)
    (rows : ∀(t : Fin (es.length+1)) (q : Q),
      q∈Set.range (cells (boundaryState slot es start j t)) ↔ q.2.val<(words t q.1).val) :
    TypedWiring.value (timeGuard (F:=F) cap es fits widthPin data) v =
      if ∀i,v (data i)=true → i∈Set.range (timelineFin slot wire cells es start j) then 1 else 0 := by
  rw [timeGuard,Tagged.WideHost.localFamily_eval,Fintype.prod_unique]
  let q (i : Fin N) := (timeOrder («Q»:=Q) es).symm i
  rw [Ports.eval _ _ (fun i=>words (q i).1 (q i).2.1) (fun i d=>reads ..)]
  have exactRange (i : Fin N) := (timelineFin_range slot wire cells es start j i).trans (rows (q i).1 (q i).2)
  change (if ∀i,v (data i)=true → true=true ∧ (q i).2.2.val<(words (q i).1 (q i).2.1).val then (1:F) else 0)=_
  simp only [true_and,exactRange]

end Hierarchy.WireTelescope.CalendarTape

end
end OAI
