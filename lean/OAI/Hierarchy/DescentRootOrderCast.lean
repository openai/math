import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Reusing each inverse-layout comparison at a different per-lane payload width -/
namespace Hierarchy.DescentRootOrderCast
open DescentSIMDLookup DescentPackedZip DescentPackedColony.Phase.Arena DescentIssuedTerminalId
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w a b M H G : ℕ}

def widen (x : Cell a) : Cell b := (x.val:ℕ)
def bank (base a M : ℕ) : Bank :=⟨base,a*M⟩
def stop (base a M : ℕ) :=base+2^(a*M)
def literals (base a b M w : ℕ) : Image w :=
  ⟨base,stop base a M,fun x=> let key:Cell (a*M):=((x-base:ℕ):Cell (a*M))
                             ((DescentSIMDLookup.table (M:=M) (widen (a:=a) (b:=b)) key).val:Word w)⟩

theorem table_read (x : Fin H→Fin G→Cell a) (p : Row H G M) :
    DescentSIMDLookup.table (M:=M) (widen (a:=a) (b:=b)) (data x p)=data (fun v g=> widen (b:=b) (x v g)) p := by
  unfold DescentSIMDLookup.table data
  rw [Equiv.symm_apply_apply]
  apply congrArg (encode b M)
  funext i
  by_cases h:p.2.val*M+i.val< G <;> simp [Function.comp_apply,h,widen]

theorem source (base : ℕ) (e : Expr) (m : Memory w)
    (wide : stop base a M<2^w) (mounted : (literals base a b M w).Resident m)
    (x : Fin H→Fin G→Cell a) (read : Source e x M m) :
    Source (.lookup (bank base a M) e) (fun v g=> widen (b:=b) (x v g)) M m := by
  intro p
  let k:=data x p
  have hi:k.val<2^(a*M):=k.isLt
  have available:2^(a*M)<2^w:=by unfold stop at wide;omega
  have lookup:=lookup_nat (bank base a M) m ((row H G M p).val:Word w) e k.val (read p) hi available
  have found:=mounted (base+k.val) (by change base≤ base+k.val;omega)
    (by change base+k.val< base+2^(a*M);omega)
  have key:(((base+k.val-base:ℕ):Cell (a*M)))=k:=by simp []
  have known:=table_read (b:=b) x p
  change m (base+k.val)=((DescentSIMDLookup.table (M:=M) (widen (a:=a) (b:=b)) (((base+k.val-base:ℕ):Cell (a*M)))).val:Word w) at found
  rw [key,known] at found
  exact lookup.trans found

theorem installed (base : ℕ) (m : Memory w) (wide : stop base a M<2^w) :
    let I:=literals base a b M w
    I.program.Exec m (I.output m) (4+10*2^(a*M)) ∧ CheapCode I.program ∧
    I.Resident (I.output m) ∧ ∀x,x< base ∨ stop base a M≤ x→I.output m x=m x := by
  intro I
  have installed:=I.issue m (by simpa [I,literals,Image.length,stop] using wide)
  refine ⟨?_,I.hardware.1,installed.2⟩
  have length : I.length=2^(a*M) := by simp [I,literals,Image.length,stop]
  rw [←length]
  intro P R K machine
  exact installed.1 machine

end
end Hierarchy.DescentRootOrderCast

end OAI
