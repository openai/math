import OAI.Computability.BorderVNP.TeamTapeInputRoute

/-! # Decoding the public comparator suffix size on the saved literal

The row cutter obtains its sole extra numerical parameter from a tagged binary field
immediately following the public buffer parameters. Its unary working tally is constructed
by the same finite binary-to-tally table used by the physical input splitter. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape TeamTapeSorting

/-- Install the existing public-length reader in the parser's scratch bank, directing its
decoded unary output to the comparator size register. -/
def sizePort : TeamTapeInput.Port → Port
  | .cut .incidentCount => .suffixSize
  | p => .entry (.inl p)

private theorem sizePort_inj : Function.Injective sizePort := by
  intro i j h
  rcases i with i | i | _ | _ | _ <;> rcases j with j | j | _ | _ | _ <;>
    first | cases i <;> cases j <;> simp_all [sizePort] | cases i <;> simp_all [sizePort] |
      cases j <;> simp_all [sizePort] | simp_all [sizePort]

/-- Read the next tagged parameter from the still-retained literal prefix. -/
def readSize : FiniteRoutine Port := (TeamTapeInput.readLength .routing).onPorts sizePort

/-- Public binary parameter as it is written on the processor's literal tape. -/
def sizeBits (n d e w : ℕ) : List Bool :=
  Evaluator.InputBank.fieldBits (TeamTapeInput.digits n (comparisonSize d e w))

/-- After reading the tagged length, the literal remainder is preserved, the unary count
matches the actual Batcher suffix, and all other parser registers remain in place. -/
theorem readSize_runs (n d e w : ℕ) (hsize : comparisonSize d e w ≤ n)
    (s : Stacks Port) (rest : List Bool)
    (hin : s (.entry (.inl (.peek .input))) = sizeBits n d e w ++ rest)
    (hb : s (.entry (.inl .bits)) = []) (hh : s (.entry (.inl .high)) = [])
    (hs : s (.entry (.inl .scratch)) = []) (hc : s .suffixSize = []) :
    ∃ t ≤ 7*comparisonSize d e w + 9*Nat.clog 2 (n+1)+3,
      readSize.Runs t s (Function.update (Function.update s (.entry (.inl (.peek .input))) rest)
        .suffixSize (List.replicate (comparisonSize d e w) true)) := by
  let L := comparisonSize d e w
  let bs := TeamTapeInput.digits n L
  let out := Function.update (Function.update s (.entry (.inl (.peek .input))) rest) .suffixSize (List.replicate L true)
  obtain ⟨t,ht,run⟩ := TeamTapeInput.readLength_runs .routing (s ∘ sizePort) bs rest hin hb hh hs hc
  have eq : TapeWord.value bs = L := TeamTapeInput.digits_value hsize
  rw [eq] at ht run
  have hl : bs.length = Nat.clog 2 (n+1) := length_wordBits _
  rw [hl] at ht
  refine ⟨t,ht,?_⟩
  apply (TeamTapeInput.readLength .routing).runs_onPorts_framed sizePort_inj run
  · intro i; rfl
  · intro i; rcases i with i | i | _ | _ | _ <;> first | cases i <;> rfl | rfl
  · intro i hi
    have h₁ : i ≠ .entry (.inl (.peek .input)) := fun e => hi (.peek .input) e.symm
    have h₂ : i ≠ .suffixSize := fun e => hi (.cut .incidentCount) e.symm
    simp [h₁,h₂]

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
