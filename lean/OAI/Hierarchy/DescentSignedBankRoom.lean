import OAI.Hierarchy.DescentSignedPrimitiveBanks
import OAI.Hierarchy.DescentPackedHostLookupROM

namespace OAI
/-! Physical containment of sliced columns and packed lookup ROMs in a dated
signed program, including the final partially occupied dyadic bank. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem segment_fits {w n pitch base stop bit:ℕ} (j:Fin n) (small:2^bit≤pitch)
    (paid:base+n*pitch≤ stop) (space:stop<2^w):
    (⟨base+j.val*pitch,bit⟩:Bank).Fits w stop:=by
  have block:=Nat.mul_le_mul_right pitch j.isLt
  rw [Nat.succ_mul] at block
  have before:base+j.val*pitch+2^bit≤ stop:=by omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (before.trans_lt space),before⟩

theorem slice_fits {w n rows base stop:ℕ} (j:Fin n) (paid:base+n*span rows≤ stop) (space:stop<2^w):
    (subbank base rows j.val).Fits w stop:=segment_fits j le_rfl paid space

theorem binary_fits {n w a b c M width base stop:ℕ} (book:Fin n→Page)
    (ptr:Fin 2→Fin n) (fn:Cell a→Cell b→Cell c) (x y:Expr)
    (lo:x.Fits w stop) (hi:y.Fits w stop) (shapes:∀i,book (ptr i)=binary fn M i)
    (left:a*M≤width) (both:(a+b)*M≤width) (paid:base+n*2^width≤ stop) (space:stop<2^w):
    DescentPackedZip.Fits (joined book width base ptr) x y a b M stop w:=by
  have h₀:(book (ptr 0)).bits=a*M:=by rw [shapes];rfl
  have h₁:(book (ptr 1)).bits=(a+b)*M:=by rw [shapes];rfl
  exact ⟨lo,hi,bank_room book width base stop _ (h₀.trans_le left) paid space,
    bank_room book width base stop _ (h₁.trans_le both) paid space,h₀,h₁⟩

theorem packed_room {w T a b M H G base stop:ℕ} (dir:Bank) (q:Expr)
    (header:dir.Fits w stop) (enough:H*T≤dir.size) (query:q.Fits w stop)
    (paid:base+DescentPackedChildNeighbor.SIMD.ROM.cells T a b M H G+
      (span (H*chunks G M)-H*chunks G M)≤ stop) (space:stop+H*chunks G M<2^w):
    DescentPackedChildNeighbor.SIMD.Room
      (DescentPackedChildNeighbor.SIMD.ROM.layout base T a b M (Nat.clog 2 (H*chunks G M)) dir)
      q H G a b M w stop:=by
  let sh:=2^(a*M)
  let tab:=2^(a*M+b)
  let left:=2^(b*M)
  let join:=2^((b+b)*M)
  let n:=H*chunks G M
  have align:n≤ span n:=span_ge n
  have leading:base+sh+T*tab+left+join+span n≤ stop:=by
    change base+(sh+(T*tab+(left+(join+n))))+(span n-n)≤ stop at paid
    omega
  have available:stop<2^w:=(Nat.le_add_right ..).trans_lt space
  have fits (B:Bank) (bound:B.base+B.size≤ stop):B.Fits w stop:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt available),bound⟩
  have joinEnd : base+sh+T*tab+left+join ≤ stop :=
    (Nat.le_add_right _ (span n)).trans leading
  have leftEnd : base+sh+T*tab+left ≤ stop :=
    (Nat.le_add_right _ join).trans joinEnd
  have tableEnd : base+sh+T*tab ≤ stop :=
    (Nat.le_add_right _ left).trans leftEnd
  refine ⟨query,header,fits _ ?_,fits _ ?_,?_,fits _ ?_,fits _ ?_,enough,align,rfl,fun _=>rfl,rfl,rfl,space⟩
  · exact leading
  · exact (Nat.le_add_right (base+sh) (T*tab)).trans tableEnd
  · intro j
    apply fits
    have size:=Nat.mul_le_mul_right tab j.isLt
    rw [Nat.succ_mul] at size
    calc
      base+sh+j.val*tab+tab = (base+sh)+(j.val*tab+tab) := Nat.add_assoc ..
      _ ≤ base+sh+T*tab := Nat.add_le_add_left size (base+sh)
      _ ≤ stop := tableEnd
  · exact leftEnd
  · exact joinEnd

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
