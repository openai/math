import OAI.Hierarchy.DescentPreparedPageTariff
import OAI.Hierarchy.DescentResetRootLookupKey
import OAI.Hierarchy.DescentRotorReservationSources

namespace OAI
/-! Cost of the repeated physical catalog and all of its installed public root pages. -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedWalsh DescentPlainTerminal.Suffix DescentPackedColony DescentResetGates
open DescentPackedPrivateMenu DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

namespace RootBook
variable {n r D L cap field : ℕ} (book : RootBook n r D L cap field)

/-- The scalar table contributes one host field per row, and the leaf table contributes two
packed directory columns. The remaining words depend only on the public table dimensions. -/
theorem repeated_words (base H G M : ℕ) :
    book.repeatEnd base H G M-base ≤
      DescentSharedBookScan.Public.lanes*(2*(H*DescentSharedBookScan.width r (2^n) D+
        (r+1)+2^r+(2^n+1)+DescentFallbackShapeTable.imageSize r (2^n) book.shapes)+1)+
      2*(2*(H*chunks G M)+1)+(2*((M+1)*2^field)+1) := by
  let A:=DescentSharedBookScan.Public.maxRows r (2^n) D H book.shapes
  have size:=DescentDyadicSpan.span_le A
  have bound:A ≤ H*DescentSharedBookScan.width r (2^n) D+(r+1)+2^r+(2^n+1)+
      DescentFallbackShapeTable.imageSize r (2^n) book.shapes := by
    have combined (u v x y z : ℕ) : max u (max v (max x (max y z))) ≤ u+v+x+y+z := by
      simp only [max_le_iff]
      omega
    exact combined _ _ _ _ _
  have packed:=DescentDyadicSpan.span_le (H*chunks G M)
  have menu:=DescentDyadicSpan.span_le ((M+1)*2^field)
  change (base+DescentSharedBookScan.Public.lanes*DescentDyadicSpan.span A+
    2*DescentDyadicSpan.span (H*chunks G M)+DescentDyadicSpan.span ((M+1)*2^field))-base ≤ _
  rw [Nat.add_assoc base,Nat.add_assoc base,Nat.add_sub_cancel_left]
  gcongr; omega

theorem page_words (H G M arity key extra : ℕ)
    (slots : book.maxSlots ≤ arity) (bits : book.addressBits M ≤ key)
    (casts : book.castWords M ≤ 2^key) (reserve : book.extraSize ≤ extra) :
    book.pageBound H G M ≤ (2*arity+2)*2^key+(2*(H*chunks G M)+2)+extra := by
  have lookup:=Nat.pow_le_pow_right (by decide : 0<2) bits
  have table:=Nat.mul_le_mul slots (Nat.mul_le_mul_left 2 lookup)
  have packed:=DescentDyadicSpan.span_le (H*chunks G M)
  change 2^Nat.clog 2 (H*chunks G M) ≤ _ at packed
  unfold pageBound sharedWords
  rw [Nat.add_mul]
  have twice:arity*(2*2^key)=(2*arity)*2^key := by ring
  omega

end RootBook

namespace Receiver
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "args" => arityLimit D (2^r) cap n r

/-- Both address exponents are the actual cutoff arguments of the selected reset. The
reservation source uses its original estimator dimension and original number of hosts. -/
theorem issued_rom_price (key : ℕ) (tables : (field*(args+1))*M ≤ key) (order : stencil.n*M ≤ key) :
    a.rootROMWords book ≤
      DescentSharedBookScan.Public.lanes*(2*(H*DescentSharedBookScan.width r (2^n) D+
        (r+1)+2^r+(2^n+1)+DescentFallbackShapeTable.imageSize r (2^n) (2^Ht))+1)+
      2*(2*(H*chunks (2^c) M)+1)+(2*((M+1)*2^field)+1)+
      Fintype.card (RootPage r (2^n))*((2*args+2)*2^key+
        (2*(H*chunks (2^c) M)+2)+((2*(E.dim+2)+1)*(1+2^total)+4*H+2)) := by
  have data:=a.issued_literals E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
  have repeated:=(book).repeated_words a.projectionEnd H (2^c) M
  rw [data.2.2.1] at repeated
  have slots : (book).maxSlots ≤ args := by
    apply Finset.sup_le
    intro p _
    exact (a.issued_arity E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
      f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage p).1
  have casts:(book).castWords M ≤ 2^key := by
    rw [RootBook.castWords,data.2.2.2.1]
    exact Nat.pow_le_pow_right (by decide) order
  have lookup:=a.issued_lookup E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage M
  have extra:=DescentReservationHeader.reserveEntries_depth H E.dim total
  rw [← data.2.2.2.2.1] at extra
  exact Nat.add_le_add repeated (Nat.mul_le_mul_left _ ((book).page_words H (2^c) M _ _ _
    slots (lookup.trans tables) casts extra))

end Receiver
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
