import OAI.Optimization.LinearProgramming.Compression.SignWireNumericService
import OAI.Optimization.LinearProgramming.Compression.SignWireBounds

/-! Fixed, three-way, finite-window sign callback for the lattice bit program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable MinorProxyCache
open scoped BigOperators

def wordComparator : Fragment := wordSignFragment numericalCachedTagger

/-- From the scalar-bit request, the machine reads the signed integer row,
evaluates the actual mixed logarithm comparison, and emits the two response
bits while preserving the VM's stack and heap addresses. Its execution and
bit limits apply equally to the three possible signs and depend only on the
numerical bounds and allocated window. -/
theorem wordComparator_rawReply_capture {n : ℕ} (fuel prec B C R addr cap src base qbase : ℕ)
    (A : ℤ) (mag : ℕ → ℚ) (L : Buffers) (m : Memory ℚ) (row : Fin (n+1) → ℤ)
    (bits : ∀ i : Fin n, ratBits (mag i) ≤ B)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (hcap : symbolicQueryCap n fuel ≤ C)
    (prog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ addr)
    (envelope : max (2*C) (2*R+1) ≤ addr) (reserve : addr+(cachedProxySignSteps n fuel C+5) ≤ cap)
    (hbits : m.AllData (fun q => ratBits q ≤ wordComparatorBits n fuel prec B))
    (send : m.index 43=qbase) (len : m.index 37=(Lattice.signRowWord row).length)
    (dim : m.index 51=n+1) (ptr : m.index 53=src) (high : 9 ≤ qbase)
    (apart : qbase+(Lattice.signRowWord row).length ≤ src)
    (packet : BitRAM.ScalarPacket m qbase (Lattice.signRowWord row))
    (resident : ∀ z : Memory ℚ, z.AllData (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) →
      (∀ i,(i < 3 ∨ 8 < i) → (i < src ∨ src+(n+1) ≤ i) → z.data i=m.data i) →
      (∀ i,(i < 3 ∨ 6 < i) → i ≠ 10 → i ≠ 11 → i ≠ 12 → z.index i=m.index i) →
      OuterJobData (n:=n) mag L fuel prec C R cap src base
        (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) z) :
    ∃ t, BitRAM.NativeService.RawReply wordComparator
      (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) m (wordComparatorTime n fuel C)
      (Lattice.signReply (formOrdering (DyadicRAM.cachedForm fuel prec mag row))) t ∧
      ∃ u y, WireReadFrame m u src (n+1) ∧ NumericReceipt mag L fuel prec C R cap src base
        (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) row u y ∧ ReplyWriteFrame y t := by
  let P := fun q : ℚ => ratBits q ≤ wordComparatorBits n fuel prec B
  have pos : P 1 :=
    (show ratBits 1 ≤ fuel+4 by change 3 ≤ _;omega).trans (le_max_right ..)
  have zero : P 0 :=
    (show ratBits 0 ≤ fuel+4 by change 3 ≤ _;omega).trans (le_max_right ..)
  have hnum (i : Fin (n+1)) (z : ℕ) (hz : z ≤ 2^(row i).natAbs.bits.length) : P z :=
    (field_reader_bits row fuel prec form cut i z hz).trans (le_max_right ..)
  have hrow (i : Fin (n+1)) : P (row i) :=
    (ratBits_signed_integer_of_le_pow _ fuel (row_natAbs_le row fuel prec form cut i)).trans
      ((show fuel+3 ≤ fuel+4 by omega).trans (le_max_right ..))
  have checked := numericalCachedTagger_reads_capture (n:=n) fuel prec B C R addr cap src base A mag L P
    bits cut hcap (fun _ h => h.trans (le_max_left ..)) prog envelope reserve
  obtain ⟨t,rc,result⟩ := wordSignFragment_rawReply_capture P row _ _ _ qbase src m hbits zero pos send len dim ptr high
    apart packet hnum hrow _ resident _ form _ checked
  refine ⟨t,⟨rc.run.mono ?_,rc.packet,rc.length,rc.frame⟩,result⟩
  unfold wordComparatorTime
  have length := row_word_length_le row fuel prec form cut
  omega

theorem wordComparator_rawReply {n : ℕ} (fuel prec B C R addr cap src base qbase : ℕ)
    (A : ℤ) (mag : ℕ → ℚ) (L : Buffers) (m : Memory ℚ) (row : Fin (n+1) → ℤ)
    (bits : ∀ i : Fin n, ratBits (mag i) ≤ B)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (hcap : symbolicQueryCap n fuel ≤ C)
    (prog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ addr)
    (envelope : max (2*C) (2*R+1) ≤ addr) (reserve : addr+(cachedProxySignSteps n fuel C+5) ≤ cap)
    (hbits : m.AllData (fun q => ratBits q ≤ wordComparatorBits n fuel prec B))
    (send : m.index 43=qbase) (len : m.index 37=(Lattice.signRowWord row).length)
    (dim : m.index 51=n+1) (ptr : m.index 53=src) (high : 9 ≤ qbase)
    (apart : qbase+(Lattice.signRowWord row).length ≤ src)
    (packet : BitRAM.ScalarPacket m qbase (Lattice.signRowWord row))
    (resident : ∀ z : Memory ℚ, z.AllData (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) →
      (∀ i,(i < 3 ∨ 8 < i) → (i < src ∨ src+(n+1) ≤ i) → z.data i=m.data i) →
      (∀ i,(i < 3 ∨ 6 < i) → i ≠ 10 → i ≠ 11 → i ≠ 12 → z.index i=m.index i) →
      OuterJobData (n:=n) mag L fuel prec C R cap src base
        (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) z) :
    ∃ t, BitRAM.NativeService.RawReply wordComparator
      (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) m (wordComparatorTime n fuel C)
      (Lattice.signReply (formOrdering (DyadicRAM.cachedForm fuel prec mag row))) t := by
  obtain ⟨t,reply,_⟩ := wordComparator_rawReply_capture fuel prec B C R addr cap src base qbase A mag L m row
    bits form cut hcap prog envelope reserve hbits send len dim ptr high apart packet resident
  exact ⟨t,reply⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
