import OAI.Hierarchy.DescentExteriorArrival
import OAI.Hierarchy.DescentNativePacketHomeRows

namespace OAI
/-! # Numerical exterior-ancestry replay on the actual sequence of resets and ordinary steps -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorReplay
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail hwire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ i z D : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ hwire hist}
  {current : Reached W G q ε S k i z D hwire hist}
  (path : Path initial current)
  (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
  {bw count : ℕ} (slot : ℕ→Hop) (m : Memory bw) (pins : Fin count→P)

/-- The fixed calendar uses one digit at its original step number, on honest
paths. Per-hop receipts ask for that digit and the earlier public shape/host tables. -/
def Path.exteriorFields : Prop := by
  induction path with
  | here=>exact True
  | @ordinary A age zi Di zn Dn src prev fee he T c norm dst ticket ih =>
    exact ih ∧ ∃owned,ticket.Shelf (slot age) (stage slot count m age) pins base radix owned
  | @reset A age zi Di dim gh C₀ f₀ g₀ c₀ t₀ src prev ctl b ih=>
    exact ih ∧ ∃owned bank,b.Shelf (slot age) (stage slot count m age) pins owned bank

omit [Fintype P] in
theorem Path.exterior_held
    (cells : path.exteriorFields base radix slot m pins)
    (start : Holds m (slot 0).source (initial.vertex.trans Fin.valEmbedding) (host initial) pins)
    (join : ∀t < i,(slot t).dest=(slot (t+1)).source)
    (height : ∀t < i,count≤(slot t).dest.size ∧ (slot t).dest.size<2^bw) :
    Holds (stage slot count m i) (slot i).source (current.vertex.trans Fin.valEmbedding) (host current) pins := by
  induction path with
  | here=>exact start
  | ordinary prev ticket ih=>
    obtain ⟨«prefix»,owned,live⟩:=cells
    have old:=ih «prefix» (fun t ht=>join t (by omega)) (fun t ht=>height t (by omega))
    rw [←join _ (Nat.lt_succ_self _)]
    exact ticket.shelf_step _ _ _ base radix owned old live (height _ (Nat.lt_succ_self _)).1
      (height _ (Nat.lt_succ_self _)).2
  | reset prev b ih=>
    obtain ⟨«prefix»,owned,bank,live⟩:=cells
    have old:=ih «prefix» (fun t ht=>join t (by omega)) (fun t ht=>height t (by omega))
    rw [←join _ (Nat.lt_succ_self _)]
    exact b.shelf_step _ _ _ owned old bank live (height _ (Nat.lt_succ_self _)).1
      (height _ (Nat.lt_succ_self _)).2

end
end Hierarchy.DescentSixParty.Chronology

end OAI
