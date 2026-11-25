import OAI.Hierarchy.DescentPublicOperandDateTables

namespace OAI
/-! The private operand and all seven private price columns of the actual retained operand program. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentOperandFamilyBook
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {w H G : ℕ}

theorem private_pages_from_initial (base : ℕ) (s : C.Sources) (f : C.Laws) (m : Memory w)
    (ready : C.Ready s w base) (space : C.endAddress base<2^w) (src : Fin 4→Expr)
    (values : Fin H→Fin G→Fin 4→Cell C.rotorBits)
    (fit : ∀i,(src i).Fits w base)
    (seen : ∀i,Source (src i) (fun h g=>values h g i) C.lanes m)
    (qzero : ∀j,f.rotorQuery j (fun _=>0)=0) (fzero : ∀j,f.rotorFields j (fun _=>0)=0) :
    let final:=(C.code base w s f).image m
    (∀j,let e:=DescentOperandFamilyBook.expr f.rotorQuery C.lanes (C.rotorQuery base) j src
        e.Fits w (C.endAddress base) ∧ Source e (fun h g=>f.rotorQuery j (values h g)) C.lanes final) ∧
    (∀j,let e:=DescentOperandFamilyBook.expr f.rotorFields C.lanes (C.rotorFields base) j src
        e.Fits w (C.endAddress base) ∧ Source e (fun h g=>f.rotorFields j (values h g)) C.lanes final) :=by
  let p:=C.publicCasts.image (C.packetEnd base) (C.packetMemory base s m)
  let pre:=(C.sliceBook (C.slices base) w).image ((C.carryBook (C.casts base) w).image
    ((C.castBook (C.publicEnd base) w).image p))
  let q:=image f.rotorQuery C.lanes (C.rotorQuery base) pre
  let k:=image f.rotorFields C.lanes (C.rotorFields base) q
  let t:=image f.fallbackQuery C.lanes (C.fallbackQuery base) k
  let final:=(C.code base w s f).image m
  obtain ⟨a,b,c,d,e,g,h,l⟩:=C.order base
  obtain ⟨before,_,_,_,lower⟩:=C.public_snapshots base s f m ready space
  have pubStart : C.packetEnd base≤C.publicEnd base:=Nat.le_add_right ..
  have read (i) : Source (src i) (fun h g=>values h g i) C.lanes final:=by
    intro row
    exact (eval_below _ _ m final (fit i) lower).trans (seen i row)
  have pr:=DescentOperandFamilyBook.any f.rotorFields C.lanes (C.rotorFields base) q
    ((h.trans l).trans_lt space)
  have pq:=DescentOperandFamilyBook.any f.fallbackQuery C.lanes (C.fallbackQuery base) k (l.trans_lt space)
  have pf:=DescentOperandFamilyBook.any f.fallbackFields C.lanes (C.fallbackFields base) t space
  have held (i : ℕ) (lo : i<C.fallbackQuery base) : final i=k i:=
    (pf.2.2.1 i (.inl (lo.trans_le h))).trans (pq.2.2.1 i (.inl lo))
  have below : base≤C.rotorQuery base:=by omega
  constructor
  · intro j
    have r:=issued_after f.rotorQuery qzero C.lanes (C.rotorQuery base) src pre final values
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ below (fit i)) read
      ((g.trans (h.trans l)).trans_lt space)
      (fun i hi=>(held i (hi.trans_le g)).trans (pr.2.2.1 i (.inl hi))) j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (g.trans (h.trans l)) r.1,r.2⟩
  · intro j
    have r:=issued_after f.rotorFields fzero C.lanes (C.rotorFields base) src q final values
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (below.trans e) (fit i)) read
      ((h.trans l).trans_lt space) held j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (h.trans l) r.1,r.2⟩

end
end Hierarchy.DescentResetOperandSetup.Chart

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (m : OperandMenu z roots)
local notation "C" => a.successor.setup
local notation "cfg" => publicOperands z roots m.payload

theorem private_tables {H G w} (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
    (initial : Memory w) (src : Fin 4→Expr) (values : Fin H→Fin G→Fin 4→Cell (C).rotorBits)
    (ready : (C).Ready (m.banks sh floor count hub g Y w) w (a.successor.operandFloor (a.rebased floor)))
    (space : (C).endAddress (a.successor.operandFloor (a.rebased floor))<2^w)
    (fit : ∀i,(src i).Fits w (a.successor.operandFloor (a.rebased floor)))
    (seen : ∀i,Source (src i) (fun h g=>values h g i) (C).lanes initial) :
    let base := a.successor.operandFloor (a.rebased floor)
    let final := ((C).code base w (m.banks sh floor count hub g Y w) m.tables).image initial
    (∀j, let e := DescentOperandFamilyBook.expr m.tables.rotorQuery (C).lanes ((C).rotorQuery base) j src
         e.Fits w ((C).endAddress base) ∧ Source e (fun h g₀ => m.tables.rotorQuery j (values h g₀)) (C).lanes final) ∧
    (∀j, let e := DescentOperandFamilyBook.expr m.tables.rotorFields (C).lanes ((C).rotorFields base) j src
         e.Fits w ((C).endAddress base) ∧ Source e (fun h g₀ => m.tables.rotorFields j (values h g₀)) (C).lanes final) :=
  (C).private_pages_from_initial (a.successor.operandFloor (a.rebased floor)) (m.banks sh floor count hub g Y w)
    m.tables initial ready space src values fit seen
    (fun j=>by
      simp [tables,Chart.Format.laws,Chart.Format.privateColumn,DescentRotorOperandQueryROM.Shape.flatReg])
    (fun j=>by
      simp [tables,Chart.Format.laws,Chart.Format.privateColumn,DescentRotorOperandQueryROM.Shape.flatReg])

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
