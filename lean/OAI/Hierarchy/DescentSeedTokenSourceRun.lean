import OAI.Hierarchy.DescentSeedTokenSourceProgram
import OAI.Hierarchy.DescentSeedPackedHeaderNumbers

namespace OAI
/-! # Running the packed primitive-role source on the original memory -/
namespace Hierarchy.DescentPackedSeed.Primitive.Source
open DescentDyadicSpan DescentSeedRoot DescentSIMDLookup Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s payload bw : ℕ)
local notation "O" => Fintype.card (Old X)
local notation "A" => pieces payload s
local notation "n" => jobs X R s payload
local notation "dst" => raw X R s payload
local notation "top" => finish X R s payload
local notation "T" => fun base=>tape base O R A s (publicWords X)
omit [Field F] in
theorem placed (base : ℕ) : endAddr base O R A s ≤ dst base :=by
  have data:=span_ge n
  have dict:=span_ge (cols s A)
  change base+cols s A+2*n ≤ base+span (cols s A)+2*span n
  omega

omit [Field F] in
theorem raw_fit (base : ℕ) (space : top base < 2^bw) :
    (bank X R s payload base).Fits bw (top base) ∧ n ≤ (bank X R s payload base).size :=by
  have edge : (bank X R s payload base).base+(bank X R s payload base).size=top base:=rfl
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (edge.le.trans_lt space),edge.le⟩,span_ge n⟩

set_option maxRecDepth 4096 in
omit [Field F] in
theorem room (base : ℕ) (prior : publicWords X+span n ≤ base) (space : top base < 2^bw) (native : payload ≤ bw) :
    Room ((T) base) (dst base) (digitsNeeded s*8) (roleBits s) A O R s bw :=by
  have nr:=span_ge n
  have dr:=span_ge (cols s A)
  have endCap : dst base+span n < 2^bw:=space
  have address : dst base < 2^bw:=by omega
  have fits (b : Bank) (edge : b.base+b.size ≤ dst base) : b.Fits bw (dst base) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (edge.trans_lt address),edge⟩
  refine ⟨?_,?_,?_,?_,(result_fit payload s).trans native⟩
  · intro b among
    simp only [List.mem_cons,List.not_mem_nil,or_false] at among
    rcases among with rfl|rfl|rfl|rfl <;> apply fits
    · change publicWords X+span n ≤ base+span (cols s A)+2*span n
      omega
    · change base+cols s A+n+span n ≤ base+span (cols s A)+2*span n
      omega
    · change base+cols s A+span n ≤ base+span (cols s A)+2*span n
      omega
    · simp only [tape,Bank.size,raw,span]
      exact Nat.le_add_right ..
  · intro b among
    simp only [List.mem_cons,List.not_mem_nil,or_false] at among
    rcases among with rfl|rfl|rfl <;> exact nr
  · simpa only [tape,Bank.size,span] using dr
  · change dst base+n < 2^bw
    omega

theorem execute (base : ℕ) (m : Memory bw) (prior : publicWords X+span n ≤ base)
    (space : top base < 2^bw) (native : payload ≤ bw) :
    (program X R s payload bw base).Exec m (image X R s payload bw base m) (clock X R s payload base) ∧
    CheapCode (program X R s payload bw base) ∧ ∀u,u < base ∨ top base ≤ u → image X R s payload bw base m u=m u :=by
  obtain ⟨run,cheap,frame⟩:=wide_any (R:=R) (s:=s) X payload bw base (dst base) m (placed X R s payload base)
    (room X R s payload bw base prior space native)
  exact ⟨run,cheap,fun u off=>frame u (off.imp_right (((Nat.add_le_add_left (span_ge n) _).trans ·)))⟩

end
end Hierarchy.DescentPackedSeed.Primitive.Source

end OAI
