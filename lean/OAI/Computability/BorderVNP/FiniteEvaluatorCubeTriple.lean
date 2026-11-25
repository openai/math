import OAI.Computability.BorderVNP.FiniteEvaluatorCubeVisits
import OAI.Computability.BorderVNP.CubeTeamOwnedRole
import OAI.Computability.BorderVNP.DiagonalTallyPacketEvidence

/-! # The selected cube lookup triple produced by the actual strict-side emitter

Dense packet-trial rank and local half-cube rank are the two physical loop
indices. The selector ordinal comes from the packet's freshly scattered bits.
The vertex ordinal includes the orientation bit of the grouping coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned BorderVNP.Cube.Physical.VertexIndex
open BorderVNP.Cube.Tally BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open VPVNP.BurstRAM VPVNP.MotifBase RoutingISA RoutingISA.OwnedStages RoutingISA.OwnedVertex
open DiagonalTallyPacketEmit (Visit)
open scoped Classical

variable {n d blocks b h K s w : ℕ}

/-- A lookup visit with the packet's absolute bank address, genuine selected
term, vertex, attached demand words and incident supply words. -/
def visit (base stride : ℕ) (select : Packet n d blocks → Selector n K h)
    (demand : Packet n d blocks → Ends n → Fin (h*b) → Bool)
    (supply : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (pv : Packet n d blocks × Vertex (n+1)) : Visit n b h K s :=
  ⟨bankAt base stride pv.1,select pv.1,pv.2,demand pv.1,supply pv.1⟩

/-- Every three-word record in a chronological list of concrete visits. -/
def Stored (mem : ℕ → ℕ) (base : ℕ) (xs : List (Visit n b h K s)) : Prop :=
  ∀ i : Fin xs.length, (xs[i.val]).tripleAt mem (base+3*i.val)

/-- Protecting the addressed triple interval suffices for preserving every visit. -/
theorem Stored.preserve {x y : ℕ → ℕ} {base : ℕ} {xs : List (Visit n b h K s)} (records : Stored x base xs)
    (keep : ∀ a, base ≤ a → a < base+3*xs.length → y a=x a) : Stored y base xs := by
  intro i
  have idx := i.isLt
  obtain ⟨bank,sel,ver⟩ := records i
  exact ⟨(keep _ (by omega) (by omega)).trans bank,(keep _ (by omega) (by omega)).trans sel,
    (keep _ (by omega) (by omega)).trans ver⟩

/-- Adjacent directories concatenate in their native order. -/
theorem Stored.append {mem : ℕ → ℕ} {base : ℕ} {xs ys : List (Visit n b h K s)}
    (first : Stored mem base xs) (second : Stored mem (base+3*xs.length) ys) : Stored mem base (xs++ys) := by
  intro i
  by_cases left : i.val < xs.length
  · rw [List.getElem_append_left left]
    exact first ⟨_,left⟩
  · have bound : i.val < xs.length+ys.length := by simpa only [List.length_append] using i.isLt
    let j : Fin ys.length := ⟨i.val-xs.length,by omega⟩
    rw [List.getElem_append_right (by omega)]
    have addr : base+3*i.val=base+3*xs.length+3*j.val := by dsimp [j]; omega
    rw [addr]
    exact second j

variable (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)
variable {pub : Arg → Word w} {src : Set ℕ} {r t : Bank w} {m mt : Memory w}

local notation "reading" => visit D.base D.stride D.select D.demand D.supply

/-- The three words of the actual emitted record at a given dense rank match
all three fields requested by the vertex-table lookup. -/
theorem side_rank (ready : SideReady D A pub src r m) (result : SideResult D A src r m t mt)
    (i : Fin (CubeVisits.packets n d blocks*2^n)) :
    (reading (CubeVisits.atRank D.axis D.pair D.high blocks i)).tripleAt (readings mt) (A.out+3*i.val) := by
  obtain ⟨⟨pidx,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  let trial := (densePacketEquiv D.axis D.pair).symm pidx
  let p := (packetRowEquiv D.axis D.pair trial).val
  let bank := bankAt D.base D.stride p
  let v := (owned p D.axis D.high j).val
  have positive : 1 < 2^w := by have := ready.singleFit.frameFit; omega
  have sel := (scattered_stored D A m positive ready.stride.ge ready.packetsBeforeSingletons p
    (packetRowEquiv D.axis D.pair trial).property).rank
  have index : selectedPrefix (blocks := blocks) D.axis D.pair trial.val.val = pidx.val :=
    (densePacketEquiv_val D.axis D.pair trial).symm.trans (congrArg Fin.val ((densePacketEquiv D.axis D.pair).apply_symm_apply pidx))
  have rank : (finProdFinEquiv (pidx,j)).val = pidx.val*2^n+j.val := by
    change j.val+2^n*pidx.val = _; ring
  have actual := rowImage_at D.axis D.pair D.high D.base D.stride (selectorWidth n K h) A.out
    (readings (scattered D A m)) trial.val trial.property j
  dsimp only at actual
  simp only [CubeVisits.atRank,Equiv.symm_apply_apply]
  change (reading (p,v)).tripleAt (readings mt) (A.out+3*(finProdFinEquiv (pidx,j)).val)
  rw [rank,result.image]
  rw [index] at actual
  exact ⟨actual.1,actual.2.1.trans sel,actual.2.2⟩

/-- The full half-cube directory written by one genuine strict-side native
return, including all real selectors, and including a possible empty packet row. -/
theorem side_stored (ready : SideReady D A pub src r m) (result : SideResult D A src r m t mt) :
    Stored (readings mt) A.out ((CubeVisits.row D.axis D.pair D.high blocks).map reading) := by
  intro i
  have hi : i.val < CubeVisits.packets n d blocks*2^n := by
    simpa only [List.length_map,CubeVisits.row,List.length_ofFn] using i.isLt
  simpa only [List.getElem_map,CubeVisits.row,List.getElem_ofFn] using side_rank D A ready result ⟨i.val,hi⟩

/-- The subsequent authentic declaration check preserves the directory. It
touches only its subtotal and temporary descriptor before the emitted records. -/
theorem strict_stored {actual : ℕ} (ready : SideReady D A pub src r m)
    (ret : StrictReturn D A src actual r m t mt)
    (subtotal : actual+(n+1) ≤ A.out) (scratch : LocalRow.head (layout D A.power A.header) n b h K s+8+h ≤ A.out) :
    Stored (readings mt) A.out ((CubeVisits.row D.axis D.pair D.high blocks).map reading) := by
  obtain ⟨u,mu,side,verified⟩ := ret.stages
  exact (side_stored D A ready side).preserve fun a lo _ =>
    verified.outside a ⟨.inr (subtotal.trans lo),.inr (scratch.trans lo)⟩

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
