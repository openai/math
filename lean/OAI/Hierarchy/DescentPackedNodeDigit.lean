import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Shared finite digit tables for SIMD-projected physical node archives -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a K H G M w : ℕ}

def take (j : Fin K) (x : Cell (a*K)) :=(encode a K).symm x j
theorem take_zero (j : Fin K) : take (a:=a) j 0=0 :=by
  have e : encode a K (fun _=>0)=0:=by apply Fin.ext;change (finFunctionFinEquiv (fun _ : Fin K=>(0:Cell a))).val=0;simp []
  have h: (encode a K).symm 0=(fun _=>0):=(encode a K).symm_apply_eq.mpr e.symm
  simp [take,h]

def pages (a K M : ℕ) (j : Fin K) : ROM.Page :=⟨(a*K)*M,fun n=>(DescentSIMDLookup.table (M:=M) (take (a:=a) j) n).val⟩

def chart (base a K M : ℕ) (j : Fin K) :=ROM.bank (pages a K M) ((a*K)*M) base j

theorem initialized (base a K M : ℕ) (m : Memory w) (j : Fin K) (n : Cell ((a*K)*M)) :
    ROM.after (pages a K M) ((a*K)*M) base m ((chart base a K M j).base+n.val)=((DescentSIMDLookup.table (M:=M) (take (a:=a) j) n).val:Word w) :=
  ROM.read (pages a K M) _ base m j le_rfl n

def project (dict : Fin K→Bank) (prior : Expr) (j : Fin K) : Expr:=.lookup (dict j) prior

theorem fetched (dict : Fin K→Bank) (older : Expr) (j : Fin K) (out : ℕ) (m : Memory w) (values : Fin H→Fin G→Cell (a*K))
    (read : Source older values M m) (fit : (dict j).Fits w out) (bits : (dict j).bits=(a*K)*M)
    (static_ : ∀x : Cell ((a*K)*M),m ((dict j).base+x.val)=((DescentSIMDLookup.table (M:=M) (take (a:=a) j) x).val:Word w)) :
    Source (project dict older j) (fun h g=>take j (values h g)) M m :=by
  intro p
  have lo:(data values p).val<(dict j).size:=by simpa only [Bank.size,bits] using (data values p).isLt
  change (dict j).read m (older.eval m _)=_
  rw [read,bank_read _ _ lo fit,static_]
  apply congrArg (fun z : Cell (a*M)=>(z.val:Word w))
  simp only [DescentSIMDLookup.table,data,Equiv.symm_apply_apply]
  apply congrArg (encode a M);funext i
  by_cases used:p.2.val*M+i.val<G <;> simp [used,take_zero]

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
