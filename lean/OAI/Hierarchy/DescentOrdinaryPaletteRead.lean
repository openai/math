import OAI.Hierarchy.DescentOrdinaryPaletteSelect
import OAI.Hierarchy.DescentPackedColumnHardware

namespace OAI
/-! Complete origin-indexed primitive books on the issued destination plate. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Shape
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {w : ℕ} (C : Shape) (base : ℕ) (ids pool : Fin C.blocks→Bank)
local notation "fn" => select (N:=C.donors) (K:=C.nodes) (b:=C.primitiveBits) (d:=C.originBits)
local notation "out" => C.output base
local notation "dst" m => (C.phase base ids pool w).image m

theorem posted (m : Memory w) (old : ∀x,(ids x).Fits w base ∧ (pool x).Fits w base)
    (sizes : ∀x,C.rows≤(ids x).size ∧ C.rows≤(pool x).size) (room : C.roof base<2^w)
    (origin : Fin C.blocks→Fin C.hosts→Fin C.groups→Cell (C.originBits*C.nodes))
    (labels : Fin C.blocks→Fin C.hosts→Fin C.groups→Cell (C.primitiveBits*C.donors))
    (incoming : ∀x,Reads (ids x) (origin x) C.lanes m ∧ Reads (pool x) (labels x) C.lanes m)
    (x : Fin C.blocks) :
    Reads (C.bank base x) (fun h g=>select (origin x h g) (labels x h g)) C.lanes (dst m):=by
  let P:=binary fn C.lanes
  let mid:=after P C.width base m
  have lut:=binary_mounted fn C.lanes P C.width base m C.pages_room id (fun _=>rfl)
  have low : base≤out:=Nat.le_add_right ..
  have limit : out+C.blocks*C.rows<2^w:=(Nat.le_add_right ..).trans_lt room
  have scoped_ (j : ℕ) (hj : j<C.blocks) : (C.term base ids pool j).Fits w out:=by
    have q:=C.fits ids pool old room ⟨j,hj⟩
    rw [term,dite_eq_left hj];exact ⟨q.apply,q.right,q.shift,q.left⟩
  have step:=DescentPackedFlowBatch.execute out C.rows C.rows C.blocks (C.term base ids pool) mid scoped_ limit le_rfl
  have preserved (v : ℕ) (early : v<base) : mid v=m v:=frame P C.width base m v (.inl early)
  have input {b : ℕ} (bank : Bank) (v : Fin C.hosts→Fin C.groups→Cell b)
      (fit : bank.Fits w base) (cap : C.rows≤bank.size) (got : Reads bank v C.lanes m) :
      Source (.lookup bank .row) v C.lanes mid:=by
    intro p
    exact (eval_below (.lookup bank .row) _ m mid ⟨fit,trivial⟩ preserved).trans ((source_column bank base fit m v cap got) p)
  have rank:=input (ids x) (origin x) (old x).1 (sizes x).1 (incoming x).1
  have words:=input (pool x) (labels x) (old x).2 (sizes x).2 (incoming x).2
  have emit:=read_data (C.lut base) _ _ out (C.fits ids pool old room x) fn dead mid lut _ _ rank words
  intro p
  have row_:=step.2.1 x (row C.hosts C.groups C.lanes p)
  simpa only [term,dite_eq_left x.isLt,Fin.eta,bank,phase,scans,mid,P] using row_.trans (by simpa only [term,dite_eq_left x.isLt,Fin.eta] using emit p)

theorem bank_fits (x : Fin C.blocks) (space : C.roof base<2^w) :
    (C.bank base x).Fits w (C.roof base) ∧ C.rows≤(C.bank base x).size:=by
  let n:=2^Nat.clog 2 (C.rows+1)
  have size : C.rows≤n:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have below : x.val*C.rows≤C.blocks*C.rows:=Nat.mul_le_mul_right _ x.isLt.le
  change (0<n ∧ n<2^w ∧ out+x.val*C.rows+n≤C.roof base) ∧ _
  change out+C.blocks*C.rows+n<2^w at space
  exact ⟨⟨Nat.two_pow_pos _,by omega,by unfold roof;omega⟩,size⟩

theorem clock_le : (C.phase base ids pool w).ticks≤4+10*(2*2^C.width)+
    (4+C.blocks*(4+C.rows*(2*25+4))) :=by
  apply Nat.add_le_add_left
  apply DescentPackedFlowBatch.tariff
  intro i hi
  rw [term,dite_eq_left hi,DescentPackedZip.work]
  simp [Expr.work]

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Shape

end OAI
