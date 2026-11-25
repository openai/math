import OAI.Hierarchy.DescentResetPeerRawReads

namespace OAI
/-! # Original stem-key pages and structural flags at the raw successor host -/
namespace Hierarchy.DescentResetPeerUnionRAM.RawTables
open DescentSIMDLookup DescentPackedColony DescentDyadicSpan DescentIssuedTerminalId ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (L : Layout) {w : ℕ}
local notation "H" => L.hosts
local notation "W" => L.shapes
local notation "M" => L.lanes
local notation "G" => L.groups

/-- An earlier packed key is shared by every possible successor shape of its old host.
The address column comes from the already required private evidence mount. -/
theorem original_key (m : Memory w) (room : L.endAddress < 2^w) {l : ℕ} (old : Bank)
    (v : Fin H→Fin G→Cell l) (data_ : Reads old v M m) (oldFit : old.Fits w L.base)
    (size : H*chunks G M ≤ old.size) :
    let addr:=fun c:Fin (chunks G M)=>PrivateEvidence.atOld L.base H W old c.val
    (∀c,(addr c).Fits w L.first) ∧ ReadsAt L (fun h g=>v ((finProdFinEquiv.symm h : Fin H×Fin W).1) g)
      addr (image₀ L m) := by
  intro addr
  obtain ⟨x,y,z,t⟩:=L.bounds
  have firstFit := (y.trans (z.trans t)).trans_lt room
  have shiftRoom : L.base+span (H*W) ≤ L.first := by
    change L.base+span (H*W) ≤ L.base+(2*span (H*W)+_)
    omega
  have pf : (PrivateEvidence.parent L.base H W).Fits w L.first:=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt (shiftRoom.trans_lt firstFit),shiftRoom⟩
  have ofit : old.Fits w L.first := ⟨oldFit.1,oldFit.2.1,oldFit.2.2.trans x⟩
  refine ⟨fun c=>⟨ofit,⟨⟨pf,trivial⟩,trivial⟩⟩,?_⟩
  intro c h
  let p : Fin H×Fin W:=finProdFinEquiv.symm h
  have parent : h.val/W=p.1.val := rfl
  have inside:=h.isLt.trans_le (span_ge (H*W))
  have bound : h.val < L.privateWords := by
    change h.val < 2*span (H*W)+_
    omega
  have tap : image₀ L m (L.base+h.val)=((p.1.val*chunks G M:ℕ):Word w) := by
    rw [show image₀ L m (L.base+h.val)=(L.privateData h.val:Word w) from
      DescentStaticWordColumn.read _ _ _ _ bound]
    simp only [Layout.privateData,PrivateEvidence.constants,ite_eq_left inside,parent]
  have offset:=(lookup_nat (PrivateEvidence.parent L.base H W) (image₀ L m) _ .row h.val rfl inside pf.2.1).trans tap
  let j:=row H G M (p.1,c)
  have numeric : j.val=p.1.val*chunks G M+c.val:=by simp [j,row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have index : (Expr.op .add (.lookup (PrivateEvidence.parent L.base H W) .row) (.lit c.val)).eval (image₀ L m) (h.val:Word w)=
      (j.val:Word w) := by
    change (Expr.lookup _ .row).eval _ _+(c.val:Word w)=_
    rw [offset,numeric,Nat.cast_add]
  exact (lookup_nat old (image₀ L m) _ _ j.val index (j.isLt.trans_le size) oldFit.2.1).trans
    ((frame₀ L m _ (.inl ((Nat.add_lt_add_left (j.isLt.trans_le size) _).trans_le oldFit.2.2))).trans (data_ (p.1,c)))

/-- Raw actor directory sources carry the address of the first group word per raw host.
The same expression serves every current trunk socket and each partial final SIMD word. -/
def actorOperand (roots src : Bank) (chunk : ℕ) : Expr :=
  .lookup src (.op .add (.lookup roots .row) (.lit chunk))

theorem actor_read (m : Memory w) (bounds : ℕ) {l : ℕ} (roots src : Bank)
    (rowAt : Fin (H*W)→ℕ) (value : Fin (H*W)→Fin G→Cell l)
    (rootsFit : roots.Fits w bounds) (srcFit : src.Fits w bounds) (rootSize : H*W ≤ roots.size)
    (srcSize : ∀v,rowAt v+chunks G M ≤ src.size)
    (rootWord : ∀v,m (roots.base+v.val)=(rowAt v:Word w))
    (stored : ∀v (c : Fin (chunks G M)),m (src.base+(rowAt v+c.val))=((data («M»:=M) value (v,c)).val:Word w)) :
    (∀c:Fin (chunks G M),(actorOperand roots src c.val).Fits w bounds) ∧
      ReadsAt L value (fun c=>actorOperand roots src c.val) m := by
  refine ⟨fun _=>⟨srcFit,⟨⟨rootsFit,trivial⟩,trivial⟩⟩,?_⟩
  intro c v
  have root:=(lookup_nat roots m _ .row v.val rfl (v.isLt.trans_le rootSize) rootsFit.2.1).trans (rootWord v)
  have address : (Expr.op .add (.lookup roots .row) (.lit c.val)).eval m (v.val:Word w)=((rowAt v+c.val:ℕ):Word w) := by
    change (Expr.lookup roots .row).eval m _+(c.val:Word w)=_
    rw [root,Nat.cast_add]
  exact (lookup_nat src m _ _ _ address ((Nat.add_lt_add_left c.isLt _).trans_le (srcSize v)) srcFit.2.1).trans (stored v c)

end
end Hierarchy.DescentResetPeerUnionRAM.RawTables

end OAI
