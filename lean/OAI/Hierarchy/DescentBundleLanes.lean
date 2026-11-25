import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentLaneCover

namespace OAI
/-! # Ordered bank and exceptional-gate scalar requests on whole payloads -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentLaneGates
noncomputable section
variable {A : Type} {w : A→ℕ} {Y p : ℕ} (units : A→ℕ) (multiple : ∀a,w a=units a*p) (hp : 0<p)

private def covered (l : Lane p w) (i : Fin (l.count units)) : BlockRef p w :=
  ⟨l.port,(l.block units multiple hp i).val,by rw [multiple];exact Nat.mul_le_mul_right _ (l.block units multiple hp i).isLt⟩

def laneSlice {H : Type} {hw : H→ℕ} (l : Lane p w) : Slice p (BlockRef p w⊕BlockRef p hw) where
  start := l.residue
  stride := l.stride
  count := l.count units
  residue := Nat.mod_lt _ hp
  bound := l.count_le units
  fits := l.index_lt units multiple hp
  get i := .inl (covered units multiple hp l i)

theorem laneSlice_read {H : Type} {hw : H→ℕ} (l : Lane p w) (d : Fin p) :
    decode (laneSlice (hw:=hw) units multiple hp l) d=.inl (l.atBit d) := by
  apply congrArg Sum.inl
  change l.blockBit units multiple hp _ (l.offset hp d)=l.atBit d
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Fin.ext
  change (l.bundleStart+l.index d)*p+(l.residue+l.stride*d.val)%p=l.start+l.stride*d.val
  have h := Nat.mod_add_div' (l.residue+l.stride*d.val) p
  have h₀ := Nat.mod_add_div' l.start p
  unfold Lane.index Lane.residue Lane.bundleStart
  unfold Lane.residue at h
  rw [Nat.add_mul]
  omega

def ofProgram (q : Program Y p w) : Shape p q.recipe where
  hiddenMultiple x := by change Empty at x; exact x.elim
  groups _ _ := 1
  size_eq _ _ := (Nat.one_mul p).symm
  chunk u j _ := laneSlice units multiple hp ((q.op u).arg j)
  read u j g d := by
    rw [laneSlice_read]
    have index : Fin.cast (Nat.one_mul p) (finProdFinEquiv (g,d))=d := by
      apply Fin.ext
      have zero : g.val=0 := by omega
      simp [finProdFinEquiv]
    change Sum.inl (((q.op u).arg j).atBit d)=Sum.inl (((q.op u).arg j).atBit _)
    exact congrArg (fun t : Fin p=>Sum.inl (((q.op u).arg j).atBit t)) index.symm

@[simp] theorem ofProgram_stride (q : Program Y p w) (u j g) :
    ((ofProgram units multiple hp q).chunk u j g).stride=((q.op u).arg j).stride := rfl
end
end Hierarchy.DescentBundleHistory

end OAI
