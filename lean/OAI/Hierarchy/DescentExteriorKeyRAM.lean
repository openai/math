import OAI.Hierarchy.DescentExteriorFetchRAM

namespace OAI
/-! # Staging the actual selected exterior layout and fixed row coordinates -/
namespace Hierarchy.DescentExteriorFetch
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

structure KeyBanks where
  owner : Bank
  matrix : Bank
  offsets : Bank
  row : Bank

def KeyBanks.all (g : KeyBanks) := [g.owner,g.matrix,g.offsets,g.row]

def joinKey (g : KeyBanks) : Expr :=
  .op .add (.lookup g.offsets (.lookup g.matrix (.lookup g.owner .row))) (.lookup g.row .row)

theorem joinKey_work (g : KeyBanks) : (joinKey g).work=25 := rfl

variable {bits j r e : ℕ}
local notation "R" => 2^(j+r)
local notation "K" => (j+(j+r))*(j+(j+r))
local notation "I" => Fin (e*R)

def KeyInputs (g : KeyBanks) (M : Fin e→Layout (j+(j+r))) (m : Memory bits) : Prop :=
  (∀i:I,m (g.owner.base+i.val)=((slab i).val:Word bits)) ∧
  (∀a:Fin e,m (g.matrix.base+a.val)=((matrixCode (M a)).val:Word bits)) ∧
  (∀k:Word K,m (g.offsets.base+k.val)=((k.val*R:ℕ):Word bits)) ∧
  (∀i:I,m (g.row.base+i.val)=((rowOrd j r (dest i)).val:Word bits))

theorem key_val (M : Fin e→Layout (j+(j+r))) (i : I) :
    (encoded M i).val=(matrixCode (M (slab i))).val*R+(rowOrd j r (dest i)).val := by
  change (rowOrd j r (dest i)).val+R*(matrixCode (M (slab i))).val=_
  ring

private theorem bank_key (g : Bank) (m : Memory bits) (a out : ℕ) (ha : a<g.size)
    (fit : g.Fits bits out) : g.read m (a : Word bits)=m (g.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (ha.trans fit.2.1),Nat.mod_eq_of_lt ha]

theorem key_read {out : ℕ} (g : KeyBanks) (fits : ∀b∈g.all,b.Fits bits out)
    (room : e*R≤g.owner.size) (layouts : e≤g.matrix.size) (ptrs : 2^K≤g.offsets.size)
    (rows : e*R≤g.row.size) (M : Fin e→Layout (j+(j+r))) (m : Memory bits)
    (inputs : KeyInputs g M m) (i : I) :
    (joinKey g).eval m (i.val:Word bits)=((encoded M i).val:Word bits) := by
  obtain ⟨ho,hm,hp,hr⟩:=inputs
  simp only [joinKey,Expr.eval,RowOp.opcode,BinaryOp.eval]
  rw [bank_key g.owner m _ out (i.isLt.trans_le room) (fits _ (by simp [KeyBanks.all])),ho,
    bank_key g.matrix m _ out ((slab i).isLt.trans_le layouts) (fits _ (by simp [KeyBanks.all])),hm,
    bank_key g.offsets m _ out ((matrixCode (M (slab i))).isLt.trans_le ptrs) (fits _ (by simp [KeyBanks.all])),hp,
    bank_key g.row m _ out (i.isLt.trans_le rows) (fits _ (by simp [KeyBanks.all])),hr,key_val,Nat.cast_add]

theorem key_spec (out : ℕ) (g : KeyBanks) (fits : ∀b∈g.all,b.Fits bits out)
    (room : e*R≤g.owner.size) (layouts : e≤g.matrix.size) (ptrs : 2^K≤g.offsets.size)
    (rows : e*R≤g.row.size) (M : Fin e→Layout (j+(j+r))) (endFit : out+e*R<2^bits) :
    (scan bits out (e*R) (joinKey g)).Spec (KeyInputs g M)
      (fun m dst=>dst=image out (e*R) (joinKey g) m ∧ ∀i:I,dst (out+i.val)=((encoded M i).val:Word bits))
      (4+54*(e*R)) ∧ CheapCode (scan bits out (e*R) (joinKey g)) := by
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  have fit : (joinKey g).Fits bits out := by
    simp only [joinKey,Expr.Fits,fits g.owner (by simp [KeyBanks.all]),fits g.matrix (by simp [KeyBanks.all]),
      fits g.offsets (by simp [KeyBanks.all]),fits g.row (by simp [KeyBanks.all]),and_self]
  intro P X A machine pc reg pub exit rom «public» cfg m start input
  obtain ⟨time,ht,done,after,run,ended,mem⟩:=scan_exec out (e*R) (joinKey g) m fit endFit
    machine pc reg pub exit rom «public» cfg m start rfl
  refine ⟨time,by simpa [joinKey_work,Nat.mul_comm] using ht,done,after,run,ended,mem,?_⟩
  intro i
  rw [mem]
  simpa [ProtocolRAM.image,fillSegment,show out≤out+i.val ∧ out+i.val<out+e*R by have:=i.isLt;omega,Nat.cast_add]
    using key_read g fits room layouts ptrs rows M m input i

end
end Hierarchy.DescentExteriorFetch

end OAI
