import OAI.Hierarchy.DescentSparseBinDedup
import OAI.Hierarchy.DescentFirstColonyPadding

namespace OAI
/-! # Reading occupied target names from the actual first-site issuer -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM
open DescentFirstOccurrence DescentFirstColonyRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {U C : Type*} [Fintype C] [DecidableEq C] {n cells w : ℕ}

def occupant (cell : C ↪ Fin cells) (b : Fin cells) : Option C :=
  if h : ∃c,cell c=b then some h.choose else none

omit [DecidableEq C] in
theorem occupant_eq_some (cell : C↪Fin cells) (b : Fin cells) (c : C) :
    occupant cell b=some c ↔ cell c=b := by
  unfold occupant
  split
  next h =>
    rw [Option.some.injEq]
    exact ⟨fun eqn=>eqn ▸ h.choose_spec,fun eqn=>cell.injective (h.choose_spec.trans eqn.symm)⟩
  next h => exact ⟨by simp,fun eqn=>(h ⟨c,eqn⟩).elim⟩

omit [DecidableEq C] in
theorem occupant_eq_none (cell : C↪Fin cells) (b : Fin cells) :
    occupant cell b=none ↔ ∀c,cell c≠b := by
  classical
  by_cases h : ∃c,cell c=b <;> simp [occupant,h]; tauto

/-- Every word is issued by the earlier first-site executable. The represented
names are the names whose finite ordinal equals the site's physical rank. -/
structure Headers (L : Chart) (cell : C↪Fin cells) (o : Memory w) : Prop where
  good : ∀c,∃f,f+1<2^w ∧ f<L.starts.size ∧ o (L.heads.base+(cell c).val)=((f+1:ℕ):Word w) ∧
    o (L.starts.base+f)=(code c:Word w)
  empty : ∀b : Fin cells,(∀c,cell c≠b) → o (L.heads.base+b.val)=0

omit [DecidableEq C] in
private theorem headers_from_words (row : U≃Fin n) (group : U→C) (covered : Function.Surjective group)
    (cell : C↪Fin cells) (L : Chart) (size : n≤L.starts.size) (m o : Memory w)
    (h : Published row group covered cell L m o) :
    Headers L ((DescentPhysicalOrder.rename (rank row group covered)).symm.toEmbedding.trans cell) o := by
  let E := DescentPhysicalOrder.rename (rank row group covered)
  constructor
  · intro c
    let x := E.symm c
    let f := rank row group covered x
    obtain ⟨j,_,hj⟩ := rank_at row group covered x
    have ord : f<n := by
      change rank row group covered x < n
      exact hj ▸ j.isLt
    have head := h.first x
    have word : f+1<2^w := by
      change rank row group covered x + 1 < 2^w
      rw [← head]
      exact (o (L.heads.base+(cell x).val)).isLt
    refine ⟨f,word,ord.trans_le size,Fin.ext (head.trans (Fin.val_cast_of_lt word).symm),?_⟩
    apply (h.compact x).trans
    have e : (Fintype.equivFin C c).val=(DescentPhysicalOrder.physical (rank row group covered) x).val := by
      simpa [x,E] using congrArg Fin.val (DescentPhysicalOrder.code_rename (rank row group covered) x)
    exact congrArg (fun z : ℕ=>(z:Word w)) e.symm
  · intro b vacant
    exact Fin.ext (h.empty b (fun c hcell=>vacant (E c) (by simpa [E] using hcell)))

omit [DecidableEq C] in
theorem headers_of_published (row : U≃Fin n) (group : U→C) (covered : Function.Surjective group)
    (cell : C↪Fin cells) (L : Chart) (room : Room L w n cells) (m o : Memory w)
    (h : Published row group covered cell L m o) :
    Headers L ((DescentPhysicalOrder.rename (rank row group covered)).symm.toEmbedding.trans cell) o :=
  headers_from_words row group covered cell L ((Nat.le_succ n).trans room.startsSize) m o h

omit [DecidableEq C] in
theorem headers_of_padding {limit : ℕ} (row : U≃Fin n) (group : U→C) (covered : Function.Surjective group)
    (cell : C↪Fin cells) (L : Chart) (capacity : n≤limit) (room : Room L w limit (cells+1)) (m o : Memory w)
    (h : Padding.Real row group covered cell L m o) :
    Headers L ((DescentPhysicalOrder.rename (rank row group covered)).symm.toEmbedding.trans cell) o :=
  headers_from_words row group covered cell L ((capacity.trans (Nat.le_succ _)).trans room.startsSize) m o
    ⟨h.site,h.first,h.empty,h.compact,h.prior⟩

omit [DecidableEq C] in
theorem header_code_missing (missing : ℕ) (L : Chart) (cell : C↪Fin cells) (o : Memory w) (h : Headers L cell o)
    (expr : Expr) (r : Word w) (b : Fin cells) (read : expr.eval o r=(b.val:Word w))
    (space : cells≤L.heads.size) (wide : L.heads.size<2^w) :
    (header L expr missing).eval o r=(wideTag missing (occupant cell b):Word w) := by
  have tap : L.heads.read o (expr.eval o r)=o (L.heads.base+b.val) := by
    have lo := b.isLt.trans_le space
    simp [Bank.read,read,Fin.val_cast_of_lt (lo.trans wide),Nat.mod_eq_of_lt lo]
  cases e : occupant cell b with
  | none => exact header_empty L expr _ o r (tap.trans (h.empty b ((occupant_eq_none cell b).mp e)))
  | some c =>
    have eqn := (occupant_eq_some cell b c).mp e
    obtain ⟨f,small,span,head,key⟩ := h.good c
    rw [eqn] at head
    exact header_hit L expr _ f (code c) o r (tap.trans head) small span key

omit [DecidableEq C] in
theorem header_code (L : Chart) (cell : C↪Fin cells) (o : Memory w) (h : Headers L cell o)
    (expr : Expr) (r : Word w) (b : Fin cells) (read : expr.eval o r=(b.val:Word w))
    (space : cells≤L.heads.size) (wide : L.heads.size<2^w) :
    (header L expr (Fintype.card C)).eval o r=(tag (occupant cell b):Word w) := by
  have tap : L.heads.read o (expr.eval o r)=o (L.heads.base+b.val) := by
    have lo := b.isLt.trans_le space
    simp [Bank.read,read,Fin.val_cast_of_lt (lo.trans wide),Nat.mod_eq_of_lt lo]
  cases e : occupant cell b with
  | none => exact header_empty L expr _ o r (tap.trans (h.empty b ((occupant_eq_none cell b).mp e)))
  | some c =>
    have eqn := (occupant_eq_some cell b c).mp e
    obtain ⟨f,small,span,head,key⟩ := h.good c
    rw [eqn] at head
    exact header_hit L expr _ f (code c) o r (tap.trans head) small span key

end Hierarchy.DescentPacking.SparseBinRAM

end
end OAI
