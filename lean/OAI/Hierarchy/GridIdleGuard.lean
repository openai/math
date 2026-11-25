import OAI.Hierarchy.GridSelectorPadding
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Checking every bit after the identity flag on the installed selector -/

noncomputable section
namespace Hierarchy.GridIdleGuard
open ThreeFlat RAM RAM.PhysicalProcedure RAM.DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

private def args (ctrl cap : ℕ) : ProtocolRAM.Expr :=
  .branch .eq .row (.lit 0) (.lit (ctrl+1)) (.branch .eq .row (.lit 1) (.lit (cap+1)) (.lit 0))

def warm {W : ℕ} (ctrl cap : ℕ) : Memory W → Memory W :=
  ProtocolRAM.image ctrl 3 (args ctrl cap)

def procedure (W ctrl raw cap : ℕ) : Procedure W :=
  (ProtocolRAM.scan W ctrl 3 (args ctrl cap)).seq
    (TerminalWireArchive.check (GridSelector.layout ctrl (ctrl+2) raw cap))

def cost (ctrl raw cap : ℕ) :=
  4+3*(2*(args ctrl cap).work+4) +
    (6+(cap+1)*(2*(TerminalWireArchive.checkWord (GridSelector.layout ctrl (ctrl+2) raw cap)).work+4))

theorem frame {W : ℕ} (ctrl cap : ℕ) (m : Memory W) (a : ℕ) (outside : a<ctrl ∨ ctrl+3≤a) :
    warm ctrl cap m a=m a := by
  simp [warm,ProtocolRAM.image,fillSegment,show ¬(ctrl≤a ∧ a<ctrl+3) by omega]

theorem admission {F : Type*} [Semiring F] {W : ℕ} (field : FieldCode F W)
    (ctrl raw cap : ℕ) (s : Fin cap → Bool) (m : Memory W)
    (control : ctrl+3<2^W) (below : raw+cap≤ctrl) (low : 0<W)
    (bits : ∀ i : Fin cap, m (raw+i.val)=BitLayout.bitWord W (s i)) :
    let p := procedure W ctrl raw cap
    TickStageSpec.Admission field p.block p.publicData (·=m) (fun _=>∀ i,s i=false)
      (fun _ out => out=warm ctrl cap m) (cost ctrl raw cap) := by
  intro p
  let put := ProtocolRAM.scan W ctrl 3 (args ctrl cap)
  let z := warm ctrl cap m
  let x := GridSelector.layout ctrl (ctrl+2) raw cap
  let check := TerminalWireArchive.check (W:=W) x
  let : NeZero W := ⟨low.ne'⟩
  have two : 2<2^W := by omega
  have twoW : (2 : Word W)≠0 := fun h => by
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt two] at this
  have twoOne : (2 : Word W)≠1 := fun h => by
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt two,Nat.mod_eq_of_lt (by omega : 1<2^W)] at this
  have packed : put.Exec m z (4+3*(2*(args ctrl cap).work+4)) :=
    ProtocolRAM.scan_exec ctrl 3 (args ctrl cap) m (by simp [args,ProtocolRAM.Expr.Fits]) control
  have first : z ctrl=(ctrl+1:ℕ) := by
    simp [z,warm,ProtocolRAM.image,fillSegment,args,ProtocolRAM.Expr.eval,Comparison.test]
  have second : z (ctrl+1)=(cap+1:ℕ) := by
    simp [z,warm,ProtocolRAM.image,fillSegment,args,ProtocolRAM.Expr.eval,Comparison.test,Nat.cast_add,low.ne']
  have third : z (ctrl+2)=0 := by
    simp [z,warm,ProtocolRAM.image,fillSegment,args,ProtocolRAM.Expr.eval,Comparison.test,Nat.cast_add,twoW,twoOne]
  have read (i : Fin cap) : z (raw+i.val)=BitLayout.bitWord W ((List.ofFn s)[i.val]'(by simp)) := by
    rw [show z (raw+i.val)=m (raw+i.val) from frame _ _ _ _ (Or.inl (by have := i.isLt; omega))]
    simpa using bits i
  have addr : TerminalWireArchive.Bounds x W := by
    constructor <;> dsimp [x,GridSelector.layout] <;> omega
  have limit : (z (z ctrl).val).val=cap+1 := by
    rw [first,Fin.val_cast_of_lt (by omega),second,Fin.val_cast_of_lt (by omega)]
  have verifies {targetPC targetRegisters targetSlots : ℕ} (target : Machine W targetPC targetRegisters targetSlots) := GridSelector.check_padding (lo:=0) low ctrl (ctrl+2) raw field z (List.ofFn s)
    List.length_ofFn (by simp [third]) read addr limit target
  have all : (0≤cap ∧ (List.ofFn s).drop 0=List.replicate (cap-0) false) ↔ ∀ i,s i=false := by
    rw [GridSelector.padded_iff _ List.length_ofFn]
    simp
  intro P R K M pc reg pub exit inst data c mem beginAt hm
  obtain ⟨yes,no⟩ := TickStageSpec.admission_seq (good:=fun _ : Memory W => ∀ i,s i=false) field put check
    (TickStageSpec.admission_of_spec field put packed) (@verifies) (by intros; trivial)
    (by intro _ o _ _ eq; exact ⟨eq,all⟩)
    M pc reg pub exit inst data c mem beginAt hm
  refine ⟨fun ok => ?_,no⟩
  obtain ⟨t,ht,d,out,done,⟨tmp,stored,same⟩,advance⟩ := yes ok
  exact ⟨t,ht,d,out,done,same.trans stored,advance⟩

end Hierarchy.GridIdleGuard
end

end OAI
