import OAI.Hierarchy.DescentPhysicalOperandSelection
import OAI.Hierarchy.DescentRetainedTargetPlacementRead
import OAI.Hierarchy.DescentResetRetainedPlacementRead

namespace OAI
/-! Bounds of the operand expressions used by the true and malformed reset programs. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM DescentPackedZip DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {w : ℕ}

theorem converted_fits (base : ℕ) (i : Fin C.inputs) (e : Expr)
    (fit : e.Fits w (C.publicEnd base)) (room : C.casts base<2^w) :
    (C.converted base i e).Fits w (C.casts base):=by
  let g:=DescentOperandInputCast.gates C.width C.fieldBits
  let t:=DescentOperandInputCast.tables C.width C.fieldBits C.sourceWidth C.lanes (C.publicEnd base) i
  have sides:=Book.geometry g C.sourceWidth C.lanes (C.publicEnd base) i (out:=C.casts base) le_rfl room
    (by simpa [g,DescentOperandInputCast.gates] using C.width_le i)
  have sliced : DescentPackedZip.Fits t e (.lit 0) (C.width i) 0 C.lanes (C.casts base) w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) fit,trivial,sides.1,sides.2,
      by simp [t,DescentOperandInputCast.tables,Book.tables,DescentOperandInputCast.gates],
      by simp [t,DescentOperandInputCast.tables,Book.tables,DescentOperandInputCast.gates]⟩
  exact ⟨sliced.apply,sliced.right,sliced.shift,sliced.left⟩

theorem physical_banks (base : ℕ) (room : C.casts base<2^w) (x : Fin C.placement.blocks) :
    (∀i,(C.oldField base x i).Fits w (C.publicEnd base)) ∧
    (∀i,(C.portField base x i).Fits w (C.publicEnd base)):=by
  have p : C.placed base≤C.packetEnd base:=(C.packets.join _).1.trans (C.packets.join _).2
  have q : C.packetEnd base≤C.publicEnd base:=Nat.le_add_right ..
  have r : C.publicEnd base≤C.casts base:=Nat.le_add_right ..
  have u:=(C.before base).2.2
  constructor
  · intro i
    have safe:=DescentRetainedTargetPlacement.Chart.validBank C.placement C.seven.batch
      (C.seven.place base) ((u.trans (p.trans (q.trans r))).trans_lt room) i x
    exact ⟨⟨safe.1.1,safe.1.2.1,safe.1.2.2.trans (u.trans (p.trans q))⟩,trivial⟩
  · intro i
    have safe:=C.placement.validBank C.signedFields (C.placedSigned base) ((p.trans (q.trans r)).trans_lt room) i x
    exact ⟨⟨safe.1.1,safe.1.2.1,safe.1.2.2.trans (p.trans q)⟩,trivial⟩

theorem carried_fits (base : ℕ) (room : C.casts base<2^w) (x : Fin C.placement.blocks)
    (arg : Fin C.retained.args) (node : Fin C.retained.nodes) (hub : Expr) (ticket : Fin C.strip→Expr)
    (hubs : hub.Fits w (C.casts base)) (fees : ∀j,(ticket j).Fits w (C.casts base)) :
    (∀i,(C.carried base x arg node hub ticket i).Fits w (C.casts base)) ∧
      ∀f,(C.oldValue base x arg node f).Fits w (C.casts base) :=by
  obtain ⟨old,ports⟩:=C.physical_banks base room x
  constructor
  · intro i
    unfold carried
    split_ifs <;> first | exact C.converted_fits base i _ (old _) room | exact hubs |
      exact C.converted_fits base i _ (ports _) room | exact fees _
  · intro f
    exact C.converted_fits base _ _ (old _) room

theorem selected_fits (base : ℕ) (f : C.Laws) (mode : Option (Fin 7)) (x : Fin C.placement.blocks)
    (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
    (old : Fin C.inputs→Expr) (reg : Fin 4→Expr) (surface : Fin C.fallbackInputs→Expr)
    (prior : ∀i,(old i).Fits w (C.casts base)) (priorValue : ∀i,(C.oldValue base x arg node i).Fits w (C.casts base))
    (registers : ∀i,(reg i).Fits w (C.rotorQuery base)) (public_ : ∀i,(surface i).Fits w (C.fallbackQuery base))
    (room : C.endAddress base<2^w) :
    (C.selected base f mode x arg node old reg surface).Fits w (C.endAddress base):=by
  obtain ⟨a,b,c,d,e,g,h,l⟩:=C.order base
  let j:Fin C.members:=finProdFinEquiv (arg,node)
  have ch:=d.trans (e.trans (g.trans (h.trans l)))
  have rh:=g.trans (h.trans l)
  have cable:=DescentOperandFamilyBook.expr_fits C.cable.queryLaw C.lanes (C.casts base) 0 old prior ((c.trans ch).trans_lt room)
  cases mode with
  | none=>
    have private_:=DescentOperandFamilyBook.expr_fits f.rotorQuery C.lanes (C.rotorQuery base) j reg registers (rh.trans_lt room)
    have publicPage:=DescentOperandFamilyBook.expr_fits f.fallbackQuery C.lanes (C.fallbackQuery base) j surface public_ (l.trans_lt room)
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (c.trans ch) cable,
      ProtocolRAMGeneratedWrite.fits_mono _ rh private_,ProtocolRAMGeneratedWrite.fits_mono _ l publicPage⟩
  | some k=>
    have left:=ProtocolRAMGeneratedWrite.fits_mono _ (b.trans (c.trans ch)) (priorValue k)
    have right (i:Fin 2):=(DescentOperandFamilyBook.expr_fits C.cable.prices C.lanes (C.find base) i old
      (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ b (prior j)) (ch.trans_lt room))
    have private_:=DescentOperandFamilyBook.expr_fits f.rotorFields C.lanes (C.rotorFields base) (finProdFinEquiv (k,j)) reg
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ e (registers i)) ((h.trans l).trans_lt room)
    have publicPage:=DescentOperandFamilyBook.expr_fits f.fallbackFields C.lanes (C.fallbackFields base) (finProdFinEquiv (k,j)) surface
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ h (public_ i)) room
    refine ⟨⟨left,?_⟩,ProtocolRAMGeneratedWrite.fits_mono _ (h.trans l) private_,publicPage⟩
    split
    · exact ProtocolRAMGeneratedWrite.fits_mono _ ch (right _)
    · trivial

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
