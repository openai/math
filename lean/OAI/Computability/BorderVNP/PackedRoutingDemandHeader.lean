import OAI.Computability.BorderVNP.PackedHistoryRoutingFrame

/-! # The raw demand bank and its actual scalar layout in the startup header

Ordinary operand nine supplies frame word eight. The four processor dimensions come
from the existing packet operands, while the five private/site dimensions come from
the installed extension. These words are enough to decode the actual directory reader.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction.ProcessorSlots Packing Packing.RoutingOutputs DiagonalResidueRAM
open private read_claim from OAI.Computability.BorderVNP.TransmissionPacketOperands

/-- Install the first free workspace address as the demand-table base in ordinary operand nine. -/
def withDemandBase {W : ℕ} (other : Arg → Word W) (base : ℕ) : Arg → Word W :=
  Function.update other 9 (word W base)

/-- The actual ordinary and extended startup frame decodes the intended directory layout.
The native program writes its seven-word rows at the beginning of the reserved workspace. -/
theorem decoded_demand_header {W : ℕ} (D : Directory.Layout) (B : PacketOperands)
    (other : Arg → Word W) (base origin edges cells : ℕ) (mem : Memory W)
    (dims : D.teams = B.layout.teams ∧ D.processors = B.layout.processors ∧
      D.literal = B.layout.literal ∧ D.link = B.layout.link)
    (fit : B.Fits W) (baseFit : base < 2^W) (fields : 0 < D.fields) :
    let args := core (withDemandBase other base) origin edges cells
    let pub := B.bank args
    (∀ i : Fin 31, mem ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) →
    DirectoryHeader D (pub 0).val mem →
    Directory.ISA.frameLayout (readings pub) (readings mem) = D ∧
      frameField (readings pub) (readings mem) 8 = base := by
  intro args pub stored ext
  have first (i : Fin 31) : frameField (readings pub) (readings mem) i.val =
      readings pub (Fin.ofNat 32 (i.val+1)) := congrArg Fin.val (stored i)
  have r1 : frameField (readings pub) (readings mem) 1 = D.teams :=
    (first 1).trans ((read_claim B args 2 rfl (fit _ (by simp [PacketOperands.values]))).trans dims.1.symm)
  have r2 : frameField (readings pub) (readings mem) 2 = D.processors :=
    (first 2).trans ((read_claim B args 3 rfl (fit _ (by simp [PacketOperands.values]))).trans dims.2.1.symm)
  have r3 : frameField (readings pub) (readings mem) 3 = D.literal :=
    (first 3).trans ((read_claim B args 4 rfl (fit _ (by simp [PacketOperands.values]))).trans dims.2.2.1.symm)
  have r4 : frameField (readings pub) (readings mem) 4 = D.link :=
    (first 4).trans ((read_claim B args 5 rfl (fit _ (by simp [PacketOperands.values]))).trans dims.2.2.2.symm)
  refine ⟨?_,?_⟩
  · dsimp only [Directory.ISA.frameLayout]
    rw [r1,r2,r3,r4]
    have high : frameField (readings pub) (readings mem) 70+1 = D.fields :=
      (congrArg (·+1) ext.fields).trans (Nat.sub_add_cancel fields)
    change ⟨D.teams,D.processors,D.literal,D.link,_,_,_,_,_⟩ = D
    rw [high]
    change ⟨D.teams,D.processors,D.literal,D.link,readings mem ((pub 0).val+67),
      readings mem ((pub 0).val+68),readings mem ((pub 0).val+69),readings mem ((pub 0).val+66),D.fields⟩ = D
    rw [ext.sites,ext.block,ext.description,ext.entries]
  · refine (first 8).trans ?_
    change (B.bank args 9).val = base
    rw [B.bank_passthrough args 9 (by decide) (by decide)]
    change (withDemandBase other base 9).val = base
    rw [withDemandBase, Function.update_self,word_val _ _ baseFit]

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
