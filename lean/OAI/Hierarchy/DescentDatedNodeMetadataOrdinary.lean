import OAI.Hierarchy.DescentDatedNodeMetadataPack
import OAI.Hierarchy.DescentPackedNodeDigit

namespace OAI
/-! # Producing the next occupied-node and arity books from the ordinary span-vector tape -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w K : ℕ} (v : DescentDatedNodeMetadata.Chart)

abbrev Vectors (K : ℕ) :=Fin v.blocks→Fin K→Bank

def digitProgram (base spanBits w : ℕ) :=ROM.mount (ScalarOperand.pages spanBits v.nodes v.lanes) ((spanBits*v.nodes)*v.lanes) w base
def digitImage (base spanBits : ℕ) (m : Memory w) :=ROM.after (ScalarOperand.pages spanBits v.nodes v.lanes) ((spanBits*v.nodes)*v.lanes) base m
def scalarSpan (base b : ℕ) (src : v.Vectors K) : v.Spans K:= fun x n j=>
  ScalarOperand.project (ScalarOperand.chart base b v.nodes v.lanes) (.lookup (src x j) .row) n

def ordinaryProgram (base a b w : ℕ) (paid : v.Counts) (src : v.Vectors K) :=
  (v.digitProgram base b w).seq (v.metadataProgram (v.digitEnd base b) a b w paid (v.scalarSpan base b src))
def ordinaryTime (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) :=
  (4+10*(v.nodes*2^((b*v.nodes)*v.lanes)))+v.metadataTime (v.digitEnd base b) a b paid (v.scalarSpan base b src)
def ordinaryImage (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) (m : Memory w) :=
  v.metadataImage (v.digitEnd base b) a b paid (v.scalarSpan base b src) (v.digitImage base b m)

theorem digitRoom (base a b : ℕ) (room : v.ordinaryEnd base a b<2^w) : v.digitEnd base b<2^w:=by
  have lo : v.digitEnd base b≤v.inputsEnd (v.digitEnd base b) a b:=Nat.le_add_right ..
  have hi : v.inputsEnd (v.digitEnd base b) a b≤v.ordinaryEnd base a b:=by
    unfold ordinaryEnd metadataEnd;rw [v.translate];apply Nat.le_add_right
  exact (lo.trans hi).trans_lt room

theorem scalarFit (base b : ℕ) (src : v.Vectors K) (early : ∀x j,(src x j).Fits w base)
    (space : v.digitEnd base b<2^w) (x : Fin v.blocks) (n : Fin v.nodes) (j : Fin K) :
    (v.scalarSpan base b src x n j).Fits w (v.digitEnd base b) :=by
  have prior:=early x j
  exact ⟨ROM.bank_room (ScalarOperand.pages b v.nodes v.lanes) ((b*v.nodes)*v.lanes) base (v.digitEnd base b)
    n le_rfl le_rfl space,⟨prior.1,prior.2.1,prior.2.2.trans (Nat.le_add_right ..)⟩,trivial⟩

theorem ordinaryAny (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) (m : Memory w)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x j,(src x j).Fits w base)
    (room : v.ordinaryEnd base a b<2^w) :
    (v.ordinaryProgram base a b w paid src).Exec m (v.ordinaryImage base a b paid src m) (v.ordinaryTime base a b paid src) ∧
    (∀t,t<base ∨ v.ordinaryEnd base a b≤t→v.ordinaryImage base a b paid src m t=m t) ∧ CheapCode (v.ordinaryProgram base a b w paid src) :=by
  have limit:=v.digitRoom base a b room
  have lut:=ROM.run (ScalarOperand.pages b v.nodes v.lanes) ((b*v.nodes)*v.lanes) base m limit
  have run:=v.metadataAny (v.digitEnd base b) a b paid (v.scalarSpan base b src) (v.digitImage base b m)
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (payFits x)) (v.scalarFit base b src srcFits limit) room
  have last : v.digitEnd base b≤v.ordinaryEnd base a b:=by
    unfold ordinaryEnd metadataEnd
    rw [v.translate]
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  refine ⟨?_,?_,?_⟩
  · intro P R slots machine
    exact Procedure.Exec.then lut.1 run.1 machine
  · intro t ht
    exact (run.2.1 t (ht.imp_left (fun z=>z.trans_le (Nat.le_add_right ..)))).trans (ROM.frame _ _ _ _ _ (ht.imp_right (last.trans ·)))
  · unfold ordinaryProgram digitProgram
    apply cheap_seq
    · apply ROM.cheap
    · exact run.2.2

theorem ordinaryRead (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (words : Fin v.blocks→Fin K→Fin v.hosts→Fin v.groups→Cell (b*v.nodes))
    (arity : Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→ℕ) (bounded : ∀x n h g,arity x n h g≤K)
    (live : ∀x n j h g,ScalarOperand.take (a:=b) n (words x j h g)≠0 ↔ n.val<(amount x h g).val ∧ j.val<arity x n h g)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x j,(src x j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m)
    (roomRows : ∀x j,v.rows≤(src x j).size) (old : ∀x j,Reads (src x j) (words x j) v.lanes m)
    (room : v.ordinaryEnd base a b<2^w) (f : Fin 2) (x : Fin v.blocks) :
    Reads (v.bank (v.inputsEnd (v.digitEnd base b) a b) f x) (fun h g=>encode v.bits v.nodes (fun n=>
      if n.val<(amount x h g).val then if f=0 then (1:Cell v.bits) else (arity x n h g:Cell v.bits) else 0))
      v.lanes (v.ordinaryImage base a b paid src m) :=by
  have lim:=v.digitRoom base a b room
  let mid:=v.digitImage base b m
  have prior (t : ℕ) (lo : t<base) : mid t=m t:=ROM.frame _ _ _ _ t (.inl lo)
  have counts (x : Fin v.blocks) : Source (paid x) (amount x) v.lanes mid:=by
    intro u;exact (eval_below _ _ m mid (payFits x) prior).trans (payRead x u)
  have source (x : Fin v.blocks) (n : Fin v.nodes) (j : Fin K) : Source (v.scalarSpan base b src x n j)
      (fun h g=>ScalarOperand.take (a:=b) n (words x j h g)) v.lanes mid:=by
    have earlier:=source_column _ base (srcFits x j) m _ (roomRows x j) (old x j)
    have kept : Source (.lookup (src x j) .row) (words x j) v.lanes mid:=by
      intro u;exact (eval_below (.lookup (src x j) .row) _ m mid ⟨srcFits x j,trivial⟩ prior).trans (earlier u)
    exact ScalarOperand.fetched (ScalarOperand.chart base b v.nodes v.lanes) (.lookup (src x j) .row) n
      (v.digitEnd base b) mid (words x j) kept (v.scalarFit base b src srcFits lim x n j).1 rfl
      (ScalarOperand.initialized base b v.nodes v.lanes m n)
  exact v.metadataRead (v.digitEnd base b) a b paid (v.scalarSpan base b src) mid amount _ arity bounded live
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (payFits x))
    (v.scalarFit base b src srcFits lim) counts source room f x

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
