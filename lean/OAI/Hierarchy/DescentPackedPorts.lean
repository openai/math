import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Actual native bounded-degree neighbor lookups on packed rows -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M a b w Δ : ℕ}

structure Ports (Δ : ℕ) where
  ids : Fin Δ→Bank
  roster : Bank
  offsets : Bank
  chunks : Bank

def neighborID (P : Ports Δ) (i : Fin Δ) : Expr := .lookup P.roster (.lookup (P.ids i) .row)
def peerExpr (P : Ports Δ) (prior : Bank) (H : ℕ) (i : Fin Δ) : Expr :=
  let q:=neighborID P i
  .branch .eq q (.lit H) (.lit 0) (.lookup prior (.op .add (.lookup P.chunks .row) (.lookup P.offsets q)))

def target (q : Option (Fin H)) := q.elim H Fin.val

structure Mounted (P : Ports Δ) (roster : Fin H→Fin Δ→Option (Fin H)) (m : Memory w) (G M : ℕ) : Prop where
  ids (p : Row H G M) (i : Fin Δ) : m ((P.ids i).base+(row H G M p).val)=((p.1.val*Δ+i.val:ℕ):Word w)
  roster (v : Fin H) (i : Fin Δ) : m (P.roster.base+(v.val*Δ+i.val))=(target (roster v i):Word w)
  offsets (u : Fin H) : m (P.offsets.base+u.val)=((chunks G M*u.val:ℕ):Word w)
  chunks (p : Row H G M) : m (P.chunks.base+(row H G M p).val)=(p.2.val:Word w)

structure Accessible (P : Ports Δ) (prior : Bank) (H G M w out : ℕ) : Prop where
  ids (i : Fin Δ) : (P.ids i).Fits w out
  idsRoom (i : Fin Δ) : H*chunks G M≤(P.ids i).size
  roster : P.roster.Fits w out
  rosterRoom : H*Δ≤P.roster.size
  offsets : P.offsets.Fits w out
  offRoom : H≤P.offsets.size
  chunks : P.chunks.Fits w out
  chunkRoom : H*DescentSIMDLookup.chunks G M≤P.chunks.size
  source : prior.Fits w out
  srcRoom : H*DescentSIMDLookup.chunks G M≤prior.size

def Reads (B : Bank) (x : Fin H→Fin G→Cell a) (M : ℕ) (m : Memory w) : Prop :=
  ∀p : Row H G M,m (B.base+(row H G M p).val)=((data x p).val:ℕ)

private theorem zero_chunk (p : Row H G M) :
    (data (fun _ : Fin H=>fun _ : Fin G=>(0:Cell a)) p).val=0 := by
  change (finFunctionFinEquiv (fun i : Fin M=>if _ : p.2.val*M+i.val<G then (0:Cell a) else 0)).val=0
  simp

private theorem digit_read {a : ℕ} (x : Fin H→Fin G→Cell a) (p : Row H G M) (q : Option (Fin H)) :
    (data (fun _ g=>q.elim 0 (fun v=>x v g)) p).val = q.elim 0 (fun v=>(data x (v,p.2)).val) := by
  cases q with
  | none=>exact zero_chunk p
  | some u=>rfl

theorem peerSource (P : Ports Δ) (prior : Bank) (out : ℕ) (fit : Accessible P prior H G M w out)
    (roster : Fin H→Fin Δ→Option (Fin H)) (m : Memory w) (real : Mounted P roster m G M)
    (x : Fin H→Fin G→Cell a) (old : Reads prior x M m) (i : Fin Δ) :
    DescentPackedZip.Source (peerExpr P prior H i) (fun v g=>(roster v i).elim 0 (fun u=>x u g)) M m := by
  intro p
  have z:=p.1.isLt
  have idSmall : p.1.val*Δ+i.val<P.roster.size :=
    (show p.1.val*Δ+i.val<H*Δ from by
      have top:=Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt p.1.isLt)
      rw [Nat.succ_mul] at top
      have := i.isLt
      omega).trans_le fit.rosterRoom
  have rs : (neighborID P i).eval m ((row H G M p).val:Word w)=(target (roster p.1 i):Word w) := by
    simp only [neighborID,Expr.eval,DescentPackedZip.bank_read _ _ ((row _ _ _ p).isLt.trans_le (fit.idsRoom i)) (fit.ids i),
      real.ids,DescentPackedZip.bank_read _ _ idSmall fit.roster,real.roster]
  have hH : H<2^w := fit.offRoom.trans_lt fit.offsets.2.1
  have pin :
      (data (fun v g=>(roster v i).elim 0 (fun u=>x u g)) p).val =
        (roster p.1 i).elim 0 (fun u=>(data x (u,p.2)).val) := digit_read x p (roster p.1 i)
  rw [pin]
  simp only [peerExpr,Expr.eval,rs]
  cases eqn : roster p.1 i with
  | none=>simp [target,Comparison.test]
  | some u=>
    have unequal : Comparison.eq.test (u.val:Word w) (H:Word w)=false := by
      simp [Comparison.test,Fin.ext_iff,Fin.val_cast_of_lt (u.isLt.trans hH),Fin.val_cast_of_lt hH,Nat.ne_of_lt u.isLt]
    have ordinal : (row H G M (u,p.2)).val=p.2.val+chunks G M*u.val := rfl
    simp only [target,Option.elim_some,unequal,Bool.false_eq_true,ite_false,RowOp.opcode,BinaryOp.eval,
      DescentPackedZip.bank_read _ _ ((row _ _ _ p).isLt.trans_le fit.chunkRoom) fit.chunks,real.chunks,
      DescentPackedZip.bank_read _ _ (u.isLt.trans_le fit.offRoom) fit.offsets,real.offsets,
      ←Nat.cast_add,←ordinal,DescentPackedZip.bank_read _ _ ((row _ _ _ (u,p.2)).isLt.trans_le fit.srcRoom) fit.source]
    exact old (u,p.2)

structure WordRoom (T : DescentPackedZip.Tables) (a b M w out : ℕ) : Prop where
  shift : T.shift.Fits w out
  apply : T.apply.Fits w out
  shiftBits : T.shift.bits=a*M
  applyBits : T.apply.bits=(a+b)*M

theorem WordRoom.issue {T : DescentPackedZip.Tables} {out : ℕ} (h : WordRoom T a b M w out)
    (u v : Expr) (left : u.Fits w out) (right : v.Fits w out) :
    DescentPackedZip.Fits T u v a b M out w :=
  ⟨left,right,h.shift,h.apply,h.shiftBits,h.applyBits⟩

theorem WordRoom.safe {T : DescentPackedZip.Tables} {out : ℕ} (h : WordRoom T a b M w out)
    (u v : Expr) (left : u.Fits w out) (right : v.Fits w out) : (T.read u v).Fits w out := by
  simp [DescentPackedZip.Tables.read,Expr.Fits,h.shift,h.apply,left,right]

theorem peer_fits (P : Ports Δ) (B : Bank) (out : ℕ) (access : Accessible P B H G M w out)
    (i : Fin Δ) : (peerExpr P B H i).Fits w out := by
  simp [peerExpr,neighborID,Expr.Fits,access.roster,access.ids,access.source,access.offsets,access.chunks]

end
end Hierarchy.DescentPackedColony

end OAI
