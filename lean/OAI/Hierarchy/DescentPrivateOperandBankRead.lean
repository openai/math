import OAI.Hierarchy.DescentPublicOperandBankRead
import OAI.Hierarchy.DescentPhysicalOperandMenu

namespace OAI
/-! The two genuine private rotor lookup pages on the same tape as the public and retained operands. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM DescentSIMDLookup DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {w H G : ℕ}

theorem private_pages (base : ℕ) (s : C.Sources) (f : C.Laws) (m : Memory w)
    (space : C.endAddress base<2^w) (src : Fin 4→Expr)
    (values : Fin H→Fin G→Fin 4→Cell C.rotorBits)
    (fit : ∀i,(src i).Fits w (C.publicEnd base))
    (seen : ∀i,Source (src i) (fun h g=>values h g i) C.lanes ((C.code base w s f).image m))
    (qzero : ∀j,f.rotorQuery j (fun _=>0)=0) (fzero : ∀j,f.rotorFields j (fun _=>0)=0) :
    let final:=(C.code base w s f).image m
    (∀j,let e:=DescentOperandFamilyBook.expr f.rotorQuery C.lanes (C.rotorQuery base) j src
        e.Fits w (C.endAddress base) ∧ Source e (fun h g=>f.rotorQuery j (values h g)) C.lanes final) ∧
    (∀j,let e:=DescentOperandFamilyBook.expr f.rotorFields C.lanes (C.rotorFields base) j src
        e.Fits w (C.endAddress base) ∧ Source e (fun h g=>f.rotorFields j (values h g)) C.lanes final) :=by
  let loaded:=C.publicCasts.image (C.packetEnd base) (C.packetMemory base s m)
  let before:=(((C.castBook (C.publicEnd base) w).join (C.carryBook (C.casts base) w)).join
    (C.sliceBook (C.slices base) w)).image loaded
  let look:=DescentOperandFamilyBook.image f.rotorQuery C.lanes (C.rotorQuery base) before
  let columns:=DescentOperandFamilyBook.image f.rotorFields C.lanes (C.rotorFields base) look
  let public_:=DescentOperandFamilyBook.image f.fallbackQuery C.lanes (C.fallbackQuery base) columns
  let final:=(C.code base w s f).image m
  obtain ⟨a,b,c,d,e,g,h,k⟩:=C.order base
  have field:=DescentOperandFamilyBook.any f.rotorFields C.lanes (C.rotorFields base) look ((h.trans k).trans_lt space)
  have surf:=DescentOperandFamilyBook.any f.fallbackQuery C.lanes (C.fallbackQuery base) columns (k.trans_lt space)
  have last:=DescentOperandFamilyBook.any f.fallbackFields C.lanes (C.fallbackFields base) public_ space
  have earlier (n : ℕ) (hn : n<C.fallbackQuery base) : final n=columns n :=
    (last.2.2.1 n (.inl (hn.trans_le h))).trans (surf.2.2.1 n (.inl hn))
  have upto : C.publicEnd base≤C.rotorQuery base:=by omega
  constructor
  · intro j
    have r:=DescentOperandFamilyBook.issued_after f.rotorQuery qzero C.lanes (C.rotorQuery base) src before final
      values (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ upto (fit i)) seen ((g.trans (h.trans k)).trans_lt space)
      (fun n hn=>(earlier n (hn.trans_le g)).trans (field.2.2.1 n (.inl hn))) j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (g.trans (h.trans k)) r.1,r.2⟩
  · intro j
    have r:=DescentOperandFamilyBook.issued_after f.rotorFields fzero C.lanes (C.rotorFields base) src look final
      values (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (upto.trans e) (fit i)) seen
      ((h.trans k).trans_lt space) earlier j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (h.trans k) r.1,r.2⟩

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
