import OAI.Hierarchy.DescentResetOriginalDate

namespace OAI
/-! # Simultaneous measured operand readback for every mixed public original-word slot -/
namespace Hierarchy.DescentResetMixedWordRAM.OriginalDate.Date
open DescentPackedZip DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ROM DescentResetFieldAssembler OriginalBooks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w X J K H G : ℕ} (L : Date X J K)

def output (x : Fin X) (j : Fin J) : Bank:=DescentResetOriginalSlots.bank L.original L.rows K x.val (L.shelf j).val
theorem output_room (r : L.Room w) (x : Fin X) (j : Fin J) : (L.output x j).Fits w L.stop:=by
  let a : Fin (X*K):=finProdFinEquiv (x,L.shelf j)
  let n:=DescentResetOriginalSlots.stride L.rows
  have at_ : (L.output x j).base=L.original+a.val*n:=by simp [output,DescentResetOriginalSlots.bank,DescentResetOriginalSlots.offset,a,n,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have size : (L.output x j).size=n:=rfl
  have hi:=Nat.mul_le_mul_right n a.isLt
  rw [Nat.succ_mul] at hi
  have across : (L.output x j).base+(L.output x j).size≤L.stop:=by rw [at_,size];change _≤L.original+X*K*n;omega
  exact ⟨pow_pos (by decide) _,(Nat.le_add_left _ _).trans_lt (across.trans_lt r.endFits),across⟩

theorem posted (r : L.Room w) (m : Memory w) (x : Fin X) (j : Fin J) (rows : L.rows=H*chunks G L.lanes)
    (src : Fin H→Fin G→Meta) (zero : Fin H→Fin G→Bool)
    (halo : Fin H→Fin G→Cell L.haloBits) (arg : Fin H→Fin G→Cell L.argBits)
    (mb : 0<L.metaBits) (zb : 0<L.zeroBits) (noHit : L.fn (L.kind j) 0 0 0 0=0)
    (ms : Source (L.fields.meta (finProdFinEquiv (x,j))) (fun h g=>raw L.metaBits (src h g)) L.lanes m)
    (zs : Source (L.fields.zero (finProdFinEquiv (x,j))) (fun h g=>((zero h g).toNat:Cell L.zeroBits)) L.lanes m)
    (hs : Source (L.fields.halo (finProdFinEquiv (x,j))) halo L.lanes m)
    (ds : Source (L.fields.arg (finProdFinEquiv (x,j))) arg L.lanes m) :
    Source (.lookup (L.output x j) .row) (fun h g=>(L.fn (L.kind j) (src h g).live.toNat (zero h g).toNat
      (halo h g).val (arg h g).val:Cell L.wordBits)) L.lanes (L.dst m):=by
  let p:=finProdFinEquiv (x,j)
  obtain ⟨_,static_,keep,_,_⟩:=OriginalBooks.installed (b:=L.metaBits) (z:=L.zeroBits) (u:=L.haloBits) (t:=L.argBits)
    (o:=L.wordBits) (M:=L.lanes) L.fn L.header m (r.separate.trans_lt (L.space r))
  have old {a : ℕ} (e : Expr) (v : Fin H→Fin G→Cell a) (fit : e.Fits w L.header) (read : Source e v L.lanes m) : Source e v L.lanes (L.mounted m):=by
    intro row_
    exact (ProtocolRAM.eval_below e _ m (L.mounted m) fit (fun q hq=>keep q (.inl hq))).trans (read row_)
  have kind : L.kind (finProdFinEquiv.symm p).2=L.kind j:=by simp [p]
  obtain ⟨a,b,c⟩:=L.gate_room r p
  obtain ⟨tab₁,tab₂,tab₃⟩:=static_ (L.kind (finProdFinEquiv.symm p).2)
  have seen:=read_op (L.tables p) _ _ _ _ L.original (L.mounted m) (L.fn _) (by simpa only [kind] using noHit)
    src zero halo arg mb zb (old _ _ (r.meta p) ms) (old _ _ (r.zero p) zs) (old _ _ (r.halo p) hs) (old _ _ (r.arg p) ds)
    a b c tab₁ tab₂ tab₃
  apply source_column _ L.stop (L.output_room r x j) _ _ (by rw [←rows];exact DescentResetOriginalSlots.rows_le L.rows)
  intro row_
  change ProtocolRAM.result (DescentResetOriginalSlots.passes L.shelf L.original L.rows L.expr) (L.mounted m)
    (DescentResetOriginalSlots.offset L.original L.rows K x.val (L.shelf j).val+_) = _
  rw [rows]
  apply DescentResetOriginalSlots.slot_read L.shelf L.original L.expr (L.mounted m) x j _ (L.expr_fits r p)
  change Source (operation (L.tables p) (L.fields.meta p) (L.fields.zero p) (L.fields.halo p) (L.fields.arg p))
    _ L.lanes (L.mounted m)
  simpa only [kind] using seen

end
end Hierarchy.DescentResetMixedWordRAM.OriginalDate.Date

end OAI
