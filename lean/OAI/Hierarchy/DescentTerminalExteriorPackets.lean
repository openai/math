import OAI.Hierarchy.DescentTerminalPublicRead
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Aligned common-home rows of short original exterior stack words -/
namespace Hierarchy.DescentTerminalExteriorPackets
open DescentExterior DescentExteriorFetch DescentGL DescentColonies
open DescentTerminalDenseWindow DescentTerminalDenseGraphRead Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.FragmentBucket
open ThreeFlat.RAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {E j r p S H Q n : ℕ}

/-- A direct map from literal independent-copy input names to the phase-three
row and stack lane calculated by the chosen basis on its original slab. -/
def chart (M:Fin E→Layout (j+(j+r))) :
    (Σ _ : Fin (2^(j+(j+r))), Fin E) ≃ Fin (E*2^(j+r)) × Fin (2^j) where
  toFun z:=
    let xy:=coords j r (M z.2 ((DescentColonies.address _).symm z.1))
    (finProdFinEquiv (z.2,rowOrd j r xy.2),chunkOrd j xy.1)
  invFun a:=
    let row:=finProdFinEquiv.symm a.1
    ⟨DescentColonies.address _ ((M row.1).symm ((coords j r).symm ((chunkOrd j).symm a.2,(rowOrd j r).symm row.2))),row.1⟩
  left_inv := by rintro ⟨x,y⟩; simp
  right_inv := by rintro ⟨a,b⟩; obtain ⟨⟨x,y⟩,rfl⟩:=finProdFinEquiv.surjective a; simp

variable {P:Type} [Fintype P] (rows:P≃Fin n×Fin Q) (owner:Fin n→Fin H)
def position : P ≃ Fin (n*Q) :=
  (rows.trans ((dest owner).prodCongr (Equiv.refl _))).trans finProdFinEquiv
def code : P ↪ ℕ := (position rows owner).toEmbedding.trans Fin.valEmbedding

omit [Fintype P] in
theorem code_val (z:P) : code rows owner z=(dest owner (rows z).1).val*Q+(rows z).2.val := by
  change (rows z).2.val+Q*(dest owner (rows z).1).val=_
  ac_rfl

omit [Fintype P] in
theorem clustered (home:P→Fin H) (agree:∀z,home z=owner (rows z).1) {a b:P} (lt:home a<home b) :
    code rows owner a<code rows owner b := by
  rw [agree,agree] at lt
  have active: (dest owner (rows a).1).val<(dest owner (rows b).1).val :=
    (ProtocolRAMPortRanks.dest_lt_iff ..).2 ((ProtocolRAMPortRanks.bySite_lt_iff ..).2 (.inl lt))
  have bounds:((dest owner (rows a).1).val+1)*Q≤(dest owner (rows b).1).val*Q :=
    Nat.mul_le_mul_right _ active
  rw [Nat.add_mul] at bounds
  have x:=(rows a).2.isLt
  rw [code_val,code_val]
  omega

theorem start (z:P) : ProtocolRAMPortRanks.«prefix» (fun _:P=>p) (code rows owner) z=(code rows owner z)*p := by
  classical
  unfold ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter,←(position rows owner).symm.sum_comp]
  simp only [code,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Fin.valEmbedding_apply,
    Equiv.apply_symm_apply,←Finset.sum_filter]
  have same:Finset.univ.filter (fun i:Fin (n*Q)=>i.val<(position rows owner z).val)=Finset.Iio (position rows owner z) := by ext; simp
  rw [same,Finset.sum_const,Fin.card_Iio,nsmul_eq_mul]
  simp only [Nat.cast_id]

theorem dense_value (out:P→Fin p→Bool) (raw:Fin n→Word (Q*p))
    (field:∀z b,wordBits (Q*p) (raw (rows z).1) (finProdFinEquiv ((rows z).2,b))=out z b)
    (whereAt:Fin n) :
    dense (Q*p) (publicStream (bits:=fun _:P=>p) (code rows owner) out) whereAt.val=raw ((dest owner).symm whereAt) := by
  apply (wordBits _).injective
  funext d
  obtain ⟨⟨l,b⟩,rfl⟩:=finProdFinEquiv.surjective d
  let atRow:=(dest owner).symm whereAt
  let z:=rows.symm (atRow,l)
  have found:rows z=(atRow,l):=Equiv.apply_symm_apply _ _
  have index : ProtocolRAMPortRanks.«prefix» (fun _:P=>p) (code rows owner) z+b.val=
      whereAt.val*(Q*p)+(finProdFinEquiv (l,b)).val := by
    rw [start,code_val,found];simp only [atRow,Equiv.apply_symm_apply]
    change (_*Q+l.val)*p+b.val=_*(Q*p)+(b.val+p*l.val)
    ring
  rw [show wordBits (Q*p) (dense (Q*p) (publicStream (code rows owner) out) whereAt.val) _=
    publicStream (code rows owner) out (whereAt.val*(Q*p)+(finProdFinEquiv (l,b)).val) by simp [dense],
    ←index,public_at]
  simpa [found] using (field z b).symm

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
