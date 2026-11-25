import OAI.Hierarchy.DescentPrivateOperandDateTables
import OAI.Hierarchy.DescentPhysicalOperandSelection

namespace OAI
/-! The retained stem or trunk selector and both chronology corrections in actual operand memory. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentOperandFamilyBook
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {w H G : ℕ}

def beforeCarried (base : ℕ) (s : C.Sources) (m : Memory w) :=
  (C.castBook (C.publicEnd base) w).image (C.publicCasts.image (C.packetEnd base) (C.packetMemory base s m))

theorem carried_pages (base : ℕ) (s : C.Sources) (f : C.Laws) (m : Memory w)
    (space : C.endAddress base<2^w) (src : Fin C.inputs→Expr)
    (values : Fin H→Fin G→C.cable.Input) (fit : ∀i,(src i).Fits w (C.casts base))
    (seen : ∀i,Source (src i) (fun h g=>values h g i) C.lanes ((C.code base w s f).image m)) :
    let final:=(C.code base w s f).image m
    let q:=DescentOperandFamilyBook.expr C.cable.queryLaw C.lanes (C.casts base) 0 src
    (q.Fits w (C.endAddress base) ∧ Source q (fun h g=>C.cable.query (values h g)) C.lanes final) ∧
    ∀j:Fin 2,let e:=DescentOperandFamilyBook.expr C.cable.prices C.lanes (C.find base) j src
      e.Fits w (C.endAddress base) ∧ Source e (fun h g=>C.cable.correction j (values h g)) C.lanes final:=by
  let p:=C.beforeCarried base s m
  let c:=C.cable.image (C.casts base) p
  let t:=(C.sliceBook (C.slices base) w).image c
  let u:=image f.rotorQuery C.lanes (C.rotorQuery base) t
  let v:=image f.rotorFields C.lanes (C.rotorFields base) u
  let q:=image f.fallbackQuery C.lanes (C.fallbackQuery base) v
  let final:=(C.code base w s f).image m
  obtain ⟨_,b,c₁,d,e,g,h,l⟩:=C.order base
  have p₁:=DescentOperandFamilyBook.any C.cable.prices C.lanes (C.find base)
    (C.cable.first (C.casts base) p) ((d.trans (e.trans (g.trans (h.trans l)))).trans_lt space)
  have p₂:=DescentResetOperandSlices.mount_any C.oldPieces C.fieldBits C.lanes (C.slices base) c
    ((e.trans (g.trans (h.trans l))).trans_lt space)
  have p₃:=DescentOperandFamilyBook.any f.rotorQuery C.lanes (C.rotorQuery base) t ((g.trans (h.trans l)).trans_lt space)
  have p₄:=DescentOperandFamilyBook.any f.rotorFields C.lanes (C.rotorFields base) u ((h.trans l).trans_lt space)
  have p₅:=DescentOperandFamilyBook.any f.fallbackQuery C.lanes (C.fallbackQuery base) v (l.trans_lt space)
  have p₆:=DescentOperandFamilyBook.any f.fallbackFields C.lanes (C.fallbackFields base) q space
  have held (i) (lo:i<C.slices base) : final i=c i:=by
    exact (p₆.2.2.1 i (.inl (lo.trans_le (d.trans (e.trans (g.trans h)))))).trans
      ((p₅.2.2.1 i (.inl (lo.trans_le (d.trans (e.trans g))))).trans
      ((p₄.2.2.1 i (.inl (lo.trans_le (d.trans e)))).trans
      ((p₃.2.2.1 i (.inl (lo.trans_le d))).trans (p₂.2.1 i (.inl lo)))))
  have blank : C.cable.found (fun _=>0)=none:=C.cable.absent _ (by simp [DescentResetRetainedCableLaw.Shape.header])
  constructor
  · have read:=issued_after C.cable.queryLaw (fun _=>C.cable.query_none _ blank) C.lanes (C.casts base) src
      p final values fit seen ((c₁.trans (d.trans (e.trans (g.trans (h.trans l))))).trans_lt space)
      (fun i hi=>(held i (hi.trans_le c₁)).trans (p₁.2.2.1 i (.inl hi))) 0
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (c₁.trans (d.trans (e.trans (g.trans (h.trans l))))) read.1,read.2⟩
  · intro j
    have read:=issued_after C.cable.prices (fun j=>C.cable.charge_none _ blank j) C.lanes (C.find base) src
      (C.cable.first (C.casts base) p) final values (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ b (fit i)) seen
      ((d.trans (e.trans (g.trans (h.trans l)))).trans_lt space) held j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (d.trans (e.trans (g.trans (h.trans l)))) read.1,read.2⟩

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
