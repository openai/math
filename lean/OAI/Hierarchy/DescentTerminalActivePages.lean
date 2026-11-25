import OAI.Hierarchy.DescentTerminalMaskedRAM
import OAI.Hierarchy.DescentTerminalMaskedReached

namespace OAI
/-! # From the original reached group/block occupancy and authentic operand digits to the output page -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentTerminalGraphPositions DescentTerminalVertexFields DescentTerminalSiteShelves
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {world : MarkedWorld F d P bits}
    {G : PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist p : ℕ}
    (R:Reached world G price ε S k age z degree wire hist) (L : Order world.graph (S.hostSize age) p)
    (same : L.home=R.home)
variable {q t H N A w V B wb : ℕ}
local notation "cohorts" => S.groupCount age
local notation "blocks" => 2^k
local notation "shops" => S.hostSize age
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

omit [Fintype P] in
theorem active_pages (ranks : ∀u,L.nodeRank u=(R.placement.site R.vertex R.valid.coordinates u).val)
    (machine : MaskedShelf blocks) (m : Memory wb) (books : Fin shops→Raw)
    (sizes : ∀i,(books i).1.val=Fintype.card (L.Nodes i))
    (occupied : ∀i c,blankAt (measured machine m (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=cohorts) i) c≠0 ↔
      ∃u,chart R L same i u=c)
    (fit : V*span q t H N A w≤B) (bp : 0<B) (canonical : ∀i v,Zeros ((books i).2 v))
    (previous : ∀i v key,allows (fun j=>(value ((books i).2 v) j).val) key→
      venueField (q:=q) (t:=t) (w:=w)
        (cellAt (measured machine m i) (rawResident R L same i (v.cast (sizes i)))) key=(value ((books i).2 v) key).val)
    (i : Fin shops) : Source (books i) (i.val*B)
      (bitsAt (fun home : Fin shops=>homePage fit (measured machine m (groups:=cohorts) home)) bp) := by
  let mask (i : Fin shops):=blankAt (measured machine m (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=cohorts) i)
  have indices (i : Fin shops) (v : Fin (books i).1.val) :=
    raw_rank R L same ranks i (mask i) (occupied i) (v.cast (sizes i))
  exact masked_source books mask (fun i=>cellAt (measured machine m i)) (fun i v=>rawResident R L same i (v.cast (sizes i)))
    (fun i v=>(indices i v).1) (fun i v=>(indices i v).2) fit bp canonical previous i

end
end Hierarchy.DescentSixParty.Reached

end OAI
