import OAI.Hierarchy.DescentTerminalOperandRepackPrice
import OAI.Hierarchy.DescentTerminalPointerArchive

namespace OAI
/-! # Read each live terminal operand through its actual earlier slot -/
namespace Hierarchy.DescentTerminalOperandRepack
open DescentSIMDLookup DescentTerminalPointerDigits DescentPackedColony ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {blocks oldArgs K N D cap H G w:ℕ}
def padded (original:Fin 4→Fin oldArgs→Fin blocks→Bank) (unused:Fin blocks→Bank) :
    Fin 4→Fin K→Fin blocks→Bank :=
  fun f j b=>if good:j.val<oldArgs then original f ⟨j.val,good⟩ b else unused b

def Pages (base:Gather.Pages blocks cap oldArgs) (unused:Fin blocks→Bank) : Gather.Pages blocks cap K :=
  ⟨base.population,base.matrix,base.frozen,base.arity,padded base.pointers unused,base.signed⟩

variable (base:Gather.Pages blocks cap oldArgs) (unused:Fin blocks→Bank) (m:Memory w)
    (t:CellInputs D cap N K)
local notation "wide" => Pages (K:=K) base unused
local notation "split_" => Equiv.symm (finProdFinEquiv (m:=N) (n:=K))
local notation "at_" => fun i:Fin (N*K)=>Prod.snd (split_ i)

/-- The native terminal decoder masks every operand past the true node arity.
Thus such slots can use a previously paid bank without reading a missing
stored operand or requiring its contents to be zero. -/
theorem active_slot (arity:∀u:Fin N,u.val<t.n→t.arity u≤oldArgs) (i:Fin (N*K)) (live:t.active i) :
    (at_ i).val<oldArgs := live.2.trans_le (arity _ live.1)

variable (g:Fin G) (b:Fin blocks) (h:Fin H) (nodeBits arityBits width:ℕ)
local notation "fmt" => Widths.mk nodeBits arityBits (fun _=>width) (some N)
variable (rawValues:Fin 4→Fin oldArgs→Fin blocks→Fin H→Fin G→Cell (width*N))
    (printed:∀f j b,Reads (base.pointers f j b) (rawValues f j b) G m)
    (fit:(width*N)*G≤w) (capAt:∀u:Fin N,u.val<t.n→t.arity u≤oldArgs)
    (trueHeaders:∀(i:Fin (N*K))(active:t.active i)(f:Fin 4),
      ((encode width N).symm (rawValues f ⟨((finProdFinEquiv (m:=N) (n:=K)).symm i).2.val,active_slot t capAt i active⟩ b h g)
        (nodeOf i)).val=(t.pointer i).header f)

include printed fit capAt trueHeaders in
theorem pointer_field (i:Fin (N*K)) (live:t.active i) (f:Fin 4) :
    (fmt).nodeDigit width (nodeOf i).val g.val (m (((wide).pointers f (at_ i) b).base+h.val)).val=
      (t.pointer i).header f := by
  let j:Fin oldArgs:=⟨(at_ i).val,active_slot t capAt i live⟩
  let current:=rawValues f j b
  have val:=base.archived_field m b h g fmt (K:=N) rfl f j current (printed f j b)
    fit (nodeOf i) ((encode width N).symm (current h g) (nodeOf i)) rfl
  have found:(wide).pointers f (at_ i) b=base.pointers f j b:=by
    simp only [Pages,padded,dite_eq_left (active_slot t capAt i live),j]
  rw [found]
  exact val.trans (trueHeaders i live f)

end
end Hierarchy.DescentTerminalOperandRepack

end OAI
