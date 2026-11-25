import OAI.Hierarchy.TaggedWideDatedAddresses
import OAI.Hierarchy.ProtocolRAMTurnReplay

namespace OAI
/-! # Native scatter of the historical width at every fixed named socket -/

noncomputable section
namespace Hierarchy.ProtocolRAM.RoleWidths
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

def destination (base sink : ℕ) (size index : Expr) : Expr :=
  .branch .eq size (.lit 0) (.lit sink) (.op .add (.lit base) index)

theorem offset_at {W : ℕ} (stride : Bank) (site role : Expr) (m : Memory W) (z : Word W)
    (u v slots : ℕ) (lookup : stride.read m (site.eval m z)=((u*slots:ℕ):Word W))
    (code : role.eval m z=(v:Word W)) :
    (offset stride site role).eval m z=((u*slots+v:ℕ):Word W) := by
  simp only [offset,Expr.eval,lookup,code,RowOp.opcode,BinaryOp.eval,Nat.cast_add]

variable {W n L : ℕ} {I H : Type} (port : I ↪ H) (slot : H ↪ Fin L) (bits : I→ℕ)

/-- The exact cleared width shelf. Unrepresented roles, including all
unpaid positive ports, carry a literal zero word. -/
def shelf : Fin L→ℕ := Function.extend (fun i=>slot (port i)) bits (fun _=>0)

theorem shelf_live (i : I) : shelf port slot bits (slot (port i))=bits i :=
  (slot.injective.comp port.injective).extend_apply _ _ i

theorem shelf_blank (p : H) (none : p∉Set.range port) : shelf port slot bits (slot p)=0 := by
  apply Function.extend_apply'
  rintro ⟨i,h⟩
  exact none ⟨i,slot.injective h⟩

/-- Every true input row is read by the physical word-RAM procedure. A
vacant row is sent to the sink even if its role table entry is arbitrary.
All active rows have reports; the RAM replay retains true prefix widths at
both distinguished endpoints and defaults to zero on all other slots. -/
theorem run_all (base scratch sink : ℕ) (size index : Expr) (m : Memory W)
    (source : Fin n → Option I) (covers : ∀i,0<bits i→∃ j,source j=some i)
    (small : ∀i,bits i<2^W) (sf : size.Fits W base)
    (af : (destination base sink size index).Fits W base) (before : base+L ≤ scratch)
    (memory : scratch+n+n<2^W) (low : sink<base)
    (nativeSize : ∀j,size.eval m (j.val:Word W)=((source j).elim 0 bits:ℕ))
    (nativeRole : ∀j i,source j=some i→0<bits i → index.eval m (j.val:Word W)=((slot (port i)).val:Word W)) :
    ∃ out,(ProtocolRAMTurnReplay.program W base L scratch n (destination base sink size index) size).Exec m out
        (ProtocolRAMTurnReplay.work L n (destination base sink size index) size) ∧
      (∀t : Fin L,out (base+t.val)=(shelf port slot bits t:Word W)) ∧
      ∀t,(t<base ∨ base+L ≤ t) → (t<scratch ∨ scratch+n+n ≤ t) → t≠sink → out t=m t := by
  let dest (j : Fin n) := (source j).elim sink (fun i=>if bits i=0 then sink else base+(slot (port i)).val)
  let val (j : Fin n) : Word W := ((source j).elim 0 bits:ℕ)
  let result (j : Fin L) : Word W := (shelf port slot bits j:Word W)
  have data (j : Fin n) : (destination base sink size index).eval m (j.val:Word W)=(dest j:Word W) := by
    rw [destination]
    cases found : source j with
    | none=>simp [Expr.eval,Comparison.test,nativeSize,found,dest]
    | some i=>
      by_cases zero : bits i=0
      · simp [Expr.eval,Comparison.test,nativeSize,found,dest,zero]
      · have lit : (bits i:Word W)≠0 := by
          intro h
          have val := congrArg Fin.val h
          change bits i % 2^W=0 at val
          exact zero ((Nat.mod_eq_of_lt (small i)).symm.trans val)
        simp [Expr.eval,Comparison.test,nativeSize,nativeRole j i found (Nat.pos_of_ne_zero zero),found,dest,
          zero,lit,RowOp.opcode,BinaryOp.eval,Nat.cast_add]
  have range (j : Fin n) : dest j=sink ∨ base ≤ dest j ∧ dest j<base+L := by
    cases found : source j with
    | none=>simp [dest,found]
    | some i=>by_cases z : bits i=0 <;> simp [dest,found,z,(slot (port i)).isLt]
  have agree (j : Fin n) (s : Fin L) (address : dest j=base+s.val) : val j=result s := by
    cases found : source j with
    | none=>simp [dest,found] at address;omega
    | some i=>
      by_cases z : bits i=0
      · simp [dest,found,z] at address;omega
      · have same : slot (port i)=s := Fin.ext (by simpa [dest,found,z] using address)
        subst s
        simp [val,result,found,shelf_live]
  have cover (p : Fin L) : result p=0 ∨ ∃j,dest j=base+p.val := by
    by_cases hit : ∃ i,slot (port i)=p
    · obtain ⟨i,rfl⟩ := hit
      by_cases z : bits i=0
      · simp [result,shelf_live,z]
      · obtain ⟨j,seen⟩ := covers i (Nat.pos_of_ne_zero z)
        exact Or.inr ⟨j,by simp [dest,seen,z]⟩
    · have vacant : shelf port slot bits p=0 := Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hit)
      exact Or.inl (by simp [result,vacant])
  obtain ⟨out,exec,each,frame⟩ := ProtocolRAMTurnReplay.run base L scratch sink _ size m dest val result
    af sf before memory (by omega) data nativeSize range agree cover
  exact ⟨out,exec,each,frame⟩

theorem run (base scratch sink : ℕ) (size index : Expr) (m : Memory W)
    (source : Fin n → Option I) (covers : ∀i,0<bits i→∃ j,source j=some i)
    (small : ∀i,bits i<2^W) (sf : size.Fits W base)
    (af : (destination base sink size index).Fits W base) (before : base+L ≤ scratch)
    (memory : scratch+n+n<2^W) (low : sink<base)
    (nativeSize : ∀j,size.eval m (j.val:Word W)=((source j).elim 0 bits:ℕ))
    (nativeRole : ∀j i,source j=some i→0<bits i → index.eval m (j.val:Word W)=((slot (port i)).val:Word W)) :
    ∃ out,(ProtocolRAMTurnReplay.program W base L scratch n (destination base sink size index) size).Exec m out
        (ProtocolRAMTurnReplay.work L n (destination base sink size index) size) ∧
      (∀p,out (base+(slot p).val)=(shelf port slot bits (slot p):Word W)) ∧
      ∀t,(t<base ∨ base+L ≤ t) → (t<scratch ∨ scratch+n+n ≤ t) → t≠sink → out t=m t := by
  obtain ⟨out,exec,each,frame⟩:=run_all port slot bits base scratch sink size index m source covers
    small sf af before memory low nativeSize nativeRole
  exact ⟨out,exec,fun p=>each (slot p),frame⟩

end Hierarchy.ProtocolRAM.RoleWidths

end
end OAI
