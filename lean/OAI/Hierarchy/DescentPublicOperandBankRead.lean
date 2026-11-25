import OAI.Hierarchy.DescentPublicOperandDateRead

namespace OAI
/-! # The joint public-operand lookup pages in the final installed date -/
namespace Hierarchy.DescentOperandFamilyBook
open DescentPackedZip DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {H G w K n a b : ℕ}

/-- Read an issued lookup after other fields have been written above it. A source operand
may be certified on the final tape, since all its addresses precede the mounted dictionary. -/
theorem issued_after (F : Fin K→(Fin n→Cell a)→Cell b) (empty : ∀j,F j (fun _=>0)=0)
    (M base : ℕ) (src : Fin n→Expr) (old final : Memory w)
    (x : Fin H→Fin G→Fin n→Cell a) (fit : ∀i,(src i).Fits w base)
    (seen : ∀i,Source (src i) (fun h g=>x h g i) M final)
    (room : endAddress K n a M base<2^w)
    (held : ∀j,j<endAddress K n a M base→final j=image F M base old j) (j : Fin K) :
    (expr F M base j src).Fits w (endAddress K n a M base) ∧
      Source (expr F M base j src) (fun h g=>F j (x h g)) M final :=by
  have run:=any F M base old room
  have before (k : ℕ) (hk : k<base) : old k=final k :=
    ((held k (hk.trans_le (Nat.le_add_right ..))).trans (run.2.2.1 k (.inl hk))).symm
  have initial (i) : Source (src i) (fun h g=>x h g i) M old := by
    intro q
    exact (eval_below _ _ final old (fit i) before).trans (seen i q)
  have done_:=issued F empty M base j src old x fit initial room
  exact ⟨done_.1,fun q=>(eval_below _ _ _ final done_.1 held).trans (done_.2 q)⟩
end
end Hierarchy.DescentOperandFamilyBook

namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM DescentSIMDLookup DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {w H G : ℕ}

def beforePublicQueries (base : ℕ) (s : C.Sources) (f : C.Laws) (m : Memory w) :=
  (C.beforeFallback base w f).image (C.publicCasts.image (C.packetEnd base) (C.packetMemory base s m))

theorem public_pages (base : ℕ) (s : C.Sources) (f : C.Laws) (m : Memory w)
    (space : C.endAddress base<2^w) (src : Fin C.fallbackInputs→Expr)
    (values : Fin H→Fin G→Fin C.fallbackInputs→Cell C.fallbackBits)
    (fit : ∀i,(src i).Fits w (C.publicEnd base))
    (seen : ∀i,Source (src i) (fun h g=>values h g i) C.lanes ((C.code base w s f).image m))
    (qzero : ∀j,f.fallbackQuery j (fun _=>0)=0) (fzero : ∀j,f.fallbackFields j (fun _=>0)=0) :
    let final:=(C.code base w s f).image m
    (∀j,let e:=DescentOperandFamilyBook.expr f.fallbackQuery C.lanes (C.fallbackQuery base) j src
        e.Fits w (C.endAddress base) ∧ Source e (fun h g=>f.fallbackQuery j (values h g)) C.lanes final) ∧
    (∀j,let e:=DescentOperandFamilyBook.expr f.fallbackFields C.lanes (C.fallbackFields base) j src
        e.Fits w (C.endAddress base) ∧ Source e (fun h g=>f.fallbackFields j (values h g)) C.lanes final) :=by
  let prior:=C.beforePublicQueries base s f m
  let next:=DescentOperandFamilyBook.image f.fallbackQuery C.lanes (C.fallbackQuery base) prior
  let final:=(C.code base w s f).image m
  obtain ⟨a,b,c,d,e,g,h,k⟩:=C.order base
  have atQuery : C.publicEnd base≤C.fallbackQuery base:=by omega
  have fieldRun :=DescentOperandFamilyBook.any f.fallbackFields C.lanes (C.fallbackFields base) next space
  constructor
  · intro j
    have r:=DescentOperandFamilyBook.issued_after f.fallbackQuery qzero C.lanes (C.fallbackQuery base) src prior final
      values (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ atQuery (fit i)) seen (k.trans_lt space)
      (fun i hi=>fieldRun.2.2.1 i (.inl hi)) j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ k r.1,r.2⟩
  · intro j
    exact DescentOperandFamilyBook.issued_after f.fallbackFields fzero C.lanes (C.fallbackFields base) src next final
      values (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (atQuery.trans h) (fit i)) seen space
      (fun _ _=>rfl) j

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
