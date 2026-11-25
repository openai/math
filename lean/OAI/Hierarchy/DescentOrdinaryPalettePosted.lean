import OAI.Hierarchy.DescentOrdinaryPaletteHead

namespace OAI
/-! The durable checkpoint selects from the physically gathered primitive pool with the original one-based stamp. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {w : ℕ} (L : Layout) (base : ℕ) (B : L.Inputs)
local notation "v" => L.originStart base
local notation "s₀" => L.spreadStart base
local notation "j" => L.joinStart base
local notation "d₀" => L.durableStart base

variable {L} in
def Stock.output (S : L.Stock) (x : Fin L.blocks) (h : Fin L.successors) (g : Fin L.groups) :
    Cell (L.primitiveBits * L.newNodes) :=
  select (S.origin x h g) (S.onBlock x h g)

theorem posted (e : L.Early base B w) (cap : L.Capacity B) (S : L.Stock)
    (m : Memory w) (seen : L.Observed B S m) (space : L.roof base<2^w) (x : Fin L.blocks) :
    Reads (L.bank base x) (S.output x) L.nextLanes ((L.phase base B w).image m):=by
  obtain ⟨_,_,_,hj,js,sj,jd,dr⟩:=L.cuts base
  have droom:=dr.trans_lt space
  have jroom:=jd.trans_lt droom
  have sroom:=sj.trans_lt jroom
  let m₁:=(L.head base B w).image m
  let m₂:=(L.poolPhase base B w).image m₁
  let m₃:=(L.chosen base w).image m₂
  have ready:=L.head_read base B e cap S m seen sroom
  have scan:=L.spread.framed s₀ (fun _=>L.pool base B) m₁ (fun _=>L.pool_fit base B e sroom) jroom
  have moved:=L.spread.originReturned s₀ (fun _=>L.pool base B) m₁ (fun _=>L.pool_fit base B e sroom)
    jroom cap.work_live (Nat.two_pow_pos _) (fun _=>S.pool) (fun _=>ready.1)
  have ids (x) :=L.origins.placed v (w:=w) (hj.trans_lt (js.trans_lt sroom)) x
  have pool (x) :=L.spread.returned_fits s₀ x jroom
  have fit x:=(widen (hj.trans (js.trans sj)) (ids x).1)
  have on x : Reads (L.origins.bank v x) (S.origin x) L.workLanes m₂:=
    carry_reads (widen (hj.trans js) (ids x).1) (ids x).2 (fun a ha=>scan.2 a (.inl ha)) (ready.2 x)
  have incoming:=L.join.posted j (L.origins.bank v) (L.spread.returned s₀) m₂
    (fun x=>⟨fit x,(pool x).1⟩) (fun x=>⟨(ids x).2,(pool x).2⟩) droom S.origin S.onBlock
    (fun x=>⟨on x,moved x⟩)
  have placed x:=L.join.bank_fits j x droom
  exact L.durable.reads d₀ (L.join.bank j) m₃ (fun x=>(placed x).1) space x (S.output x) cap.work_live
    (placed x).2 (incoming x)

section
variable {L}

theorem Stock.node (S : L.Stock) (x : Fin L.blocks) (h : Fin L.successors) (g : Fin L.groups)
    (n : Fin L.newNodes) (z : Fin L.candidates)
    (stamp : ((encode L.originBits L.newNodes).symm (S.origin x h g) n).val=z.val+1) :
    (encode L.primitiveBits L.newNodes).symm (S.output x h g) n=
      S.cells (finProdFinEquiv.symm h).1 (finProdFinEquiv (g,x)) z:=by
  simpa only [Stock.output,Stock.onBlock,DescentScalarBookReshape.book,Stock.pool,Equiv.symm_apply_apply] using
    selected (S.origin x h g) (S.onBlock x h g) n z stamp

theorem Stock.hole (S : L.Stock) (x : Fin L.blocks) (h : Fin L.successors) (g : Fin L.groups)
    (n : Fin L.newNodes) (stamp : ((encode L.originBits L.newNodes).symm (S.origin x h g) n).val=0) :
    (encode L.primitiveBits L.newNodes).symm (S.output x h g) n=0:=by
  apply padded (S.origin x h g) (S.onBlock x h g) n
  exact Fin.ext (by simpa only [Fin.val_zero] using stamp)

end

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI
