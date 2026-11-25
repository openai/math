import OAI.Hierarchy.DescentTerminalPointerColumns
import OAI.Hierarchy.DescentTerminalPointerFrame
import OAI.Hierarchy.DescentOperandStateBanks

namespace OAI
/-! # Gathering previous physical columns to a single terminal lookup across all blocks -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOperandStateBanks
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace Gather
variable {L H w b d : ℕ}

/-- Sources can read different previous banks. For example the matrix uses
one global address, the frozen list one address per host, and each signed or
archived operand page uses its own block and host row. -/
def expression (src : Fin L→ Expr) (j : ℕ) : Expr :=
  if on : j<L then src ⟨j,on⟩ else .lit 0

def reads (origin H : ℕ) (src : Fin L→ Expr) : List Pass :=
  DescentPackedFlowBatch.passes origin H H (expression src) 0 L

def banks (origin H : ℕ) (j : Fin L) : Bank:=column origin H j.val

def values (src : Fin L→ Expr) (mem : Memory w) (h : Fin H) (j : Fin L) : Cell d :=
  (((src j).eval mem (h.val:Word w)).val:Cell d)

/-- One physical pass per source reads the original words before writing
the contiguous block-major position rows. -/
theorem fetch (origin H : ℕ) (src : Fin L→ Expr) (mem : Memory w)
    (fits : ∀j,(src j).Fits w origin) (room : origin+L*H < 2^w) :
    let ps:=reads origin H src
    let warm:=result ps mem
    (program w ps).Exec mem warm (clock ps) ∧ CheapCode (program w ps) ∧
      (∀(j : Fin L)(h : Fin H),warm ((banks origin H j).base+h.val)=(src j).eval mem (h.val:Word w)) ∧
      ∀a,a<origin ∨ origin+L*H≤a→ warm a=mem a := by
  dsimp only
  obtain ⟨exec,issued,keep⟩:=DescentPackedFlowBatch.execute origin H H L (expression src) mem
    (fun j hj=>by simpa [expression,hj] using fits ⟨j,hj⟩) room le_rfl
  refine ⟨exec,program_cheap _ _,?_,?_⟩
  · intro j h
    simpa only [reads,banks,column,expression,dite_eq_left j.isLt] using issued j h
  · intro a where_
    rcases where_ with lo|hi
    · exact keep a lo
    · exact DescentPackedFlowBatch.above origin H H _ mem 0 L a le_rfl (by simpa using hi)

def rom (origin L H : ℕ):=guard origin L H

theorem banks_fit (origin H d : ℕ) (offsets : 2^d < 2^w)
    (endAt : rom origin L H+DescentTerminalPointerFrame.size L d+H < 2^w) :
    DescentTerminalPointerFrame.Room (banks (L:=L) origin H) (rom origin L H) d H w where
  source j:=(read_fits j (show guard origin L H ≤ rom origin L H from le_rfl) (by omega : rom origin L H < 2^w)).1
  length _:=Nat.le_pow_clog (by decide : 1<2) H
  offsets:=offsets
  limit:=endAt

/-- The single shared lookup sees the genuine predecessor expressions. The
whole program runs on every input memory, including malformed archives. -/
theorem execute (origin H : ℕ) (src : Fin L→ Expr) (f : (Fin L→ Cell d)→ Cell b) (mem : Memory w)
    (fits : ∀j,(src j).Fits w origin) (offsets : 2^d < 2^w)
    (endAt : rom origin L H+DescentTerminalPointerFrame.size L d+H < 2^w) :
    let ps:=reads origin H src
    let warm:=result ps mem
    let B:=banks (L:=L) origin H
    let base:=rom origin L H
    let out:=base+DescentTerminalPointerFrame.size L d
    let next:=DescentTerminalPointerFrame.result base B H f warm
    ((program w ps).seq (DescentTerminalPointerFrame.program w base B H f)).Exec mem next
      (clock ps+((4+10*DescentTerminalPointerFrame.size L d)+(4+H*(16+26*L)))) ∧
    CheapCode ((program w ps).seq (DescentTerminalPointerFrame.program w base B H f)) ∧
    (∀h:Fin H,next (out+h.val)=((f (values src mem h)).val:Word w)) ∧
    ∀a,a<origin ∨ out+H≤a→ next a=mem a := by
  dsimp only
  have sep : origin+L*H≤rom origin L H:=Nat.le_add_right _ _
  let warm:=result (reads origin H src) mem
  obtain ⟨first,cheap₀,gathered,saved₀⟩:=fetch origin H src mem fits (by omega)
  have ok:=banks_fit (L:=L) origin H d offsets endAt
  obtain ⟨second,cheap₁,saved₁⟩:=DescentTerminalPointerFrame.run _ _ f warm ok
  have emitted:=DescentTerminalPointerFrame.read_masked _ _ f warm ok (values (d:=d) src mem)
    (fun h j=>by
      change ((result (reads origin H src) mem) ((banks origin H j).base+h.val)).val%2^d=(values (d:=d) src mem h j).val
      rw [gathered j h];rfl)
  refine ⟨first.then second,cheap_seq cheap₀ cheap₁,emitted,?_⟩
  intro a away
  exact (saved₁ a (by omega)).trans (saved₀ a (by omega))

theorem fetch_price (src : Fin L→ Expr) (K origin H : ℕ) (work : ∀j,(src j).work≤K) :
    clock (reads origin H src)≤4+L*(4+H*(2*K+4)) :=
  DescentPackedFlowBatch.tariff origin H H L (expression src) K (fun j hj=>by simpa [expression,hj] using work ⟨j,hj⟩)

end Gather
end
end Hierarchy.DescentTerminalPointerDigits

end OAI
