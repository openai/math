import OAI.Hierarchy.DescentTerminalPreflightRun
import OAI.Hierarchy.DescentTerminalPreflightROM

namespace OAI
/-! # Paying for and running the three public scan tables and the full terminal preflight -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentSIMDLookup DescentTerminalPreflightInvoice DescentTerminalLocalPortBook
open DescentTerminalCombinedRole DescentTerminalPointerDigits DescentTerminalHeaderDraft
open DescentStaticWordColumn DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

def scanPages (x : Spec) (start q : ℕ) : DescentTerminalControlROMs.Page :=
  ⟨4,x.vertices,x.vertices*x.arguments,x.arguments,Book.tokenBits (x.vertices*x.arguments),
    q,x.binSize,x.paidRows,start⟩

variable (x:Spec) (org q : ℕ)
local notation "P₀" => x.scanPages org q

/-- The live host and socket banks come from the earlier census and signed
history. The numeric fields used for counting come from the fixed allocation. -/
theorem scan_before (begin_ : ℕ) (space:(P₀).stop≤begin_)
    (paid actor:Fin x.scalar.blocks→Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (peer homes : Bank)
    (p₁ : ∀b,(paid b).base+(paid b).size≤x.cohortEnd begin_)
    (p₂ : ∀b,x.scalar.shops*DescentSIMDLookup.chunks x.groups x.paidLanes≤(paid b).size)
    (a₁ : ∀b,(actor b).base+(actor b).size≤x.cohortEnd begin_)
    (a₂ : ∀b,x.scalar.shops*DescentSIMDLookup.chunks x.groups x.actorLanes≤(actor b).size)
    (o₁ : ∀b j,(old b j).base+(old b j).size≤x.cohortEnd begin_)
    (pr : peer.base+peer.size≤x.cohortEnd begin_) (hs : homes.base+homes.size≤x.cohortEnd begin_) :
    x.Before begin_ paid actor old peer (P₀).total (P₀).modulo homes (P₀).boundaries := by
  have end_:=x.incoming begin_
  have lo : (P₀).stop≤x.cohortEnd begin_ := by omega
  exact ⟨p₁,p₂,a₁,a₂,o₁,pr,(P₀).ranges.1.trans lo,(P₀).ranges.2.1.trans lo,hs,
    (P₀).ranges.2.2.trans lo⟩

theorem scan_reel_side (dst : ℕ) (earlier:dst<org) :
    dst<(P₀).total.base ∧ dst<(P₀).modulo.base ∧ dst<(P₀).boundaries :=
  ⟨earlier,earlier.trans_le (Nat.le_add_right ..),earlier.trans_le (Nat.le_add_right ..)⟩

variable (begin_ : ℕ) (peer:Bank) (wing:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (w p nd nodes hidden args:ℕ) (oldPaid actor:Fin x.scalar.blocks→Bank)
    (first second:Shelf) (chart:Fin x.scalar.columns→Fin x.scalar.blocks→Gather.Address)
    {out0 out7:ℕ} (f0:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out0)
    (f7:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out7)
    (decode:(Fin x.strips→Cell x.printBits)→Directory 4 x.vertices x.arguments)
    (homes:Bank) (control:ℕ→ℕ)

local notation "body" => x.purchasedProgram begin_ peer wing w q p nd nodes hidden args oldPaid actor
  first second chart f0 f7 decode (P₀).total (P₀).modulo homes (P₀).boundaries control
local notation "ticks" => x.purchasedClocks begin_ peer wing q p oldPaid actor chart
  (P₀).total (P₀).modulo homes (P₀).boundaries
local notation "state_" => x.purchasedMem begin_ peer wing w q p nd nodes hidden args oldPaid actor
  first second chart f0 f7 decode (P₀).total (P₀).modulo homes (P₀).boundaries control

/-- It is valid to write the constant tables on the live census image. The
purchased computation retains all three physical lookup columns to its end. -/
theorem funded_preflight (m : Memory w) (space:(P₀).stop≤begin_)
    (before:x.Before begin_ oldPaid actor wing peer (P₀).total (P₀).modulo homes (P₀).boundaries)
    (room:x.maskBase begin_<2^w) (positive:0<w) (nonempty:0<x.strips) (columns:0<x.scalar.columns)
    (role:(emit first).Fits w (x.primitive begin_)) (arity:(emit second).Fits w (x.primitive begin_))
    (pointers:∀j b,(chart j b).Fits (x.scalar.gather (x.primitive begin_)) x.scalar.shops w) :
    let output := state_ ((P₀).image m)
    (((P₀).program w).seq body).Exec m output ((4+10*(P₀).words)+ticks) ∧
      CheapCode (((P₀).program w).seq body) ∧ (P₀).Reads output := by
  have firstRoom := x.incoming begin_
  have ⟨s₁,s₂,s₃,s₄,s₅,s₆,s₇,s₈,s₉⟩:=x.layers begin_
  have low : (P₀).stop≤x.cohortEnd begin_ := by omega
  have firstRun := (P₀).install m (show (P₀).stop<2^w by omega)
  have secondRun := x.purchased_run begin_ peer wing w q p nd nodes hidden args oldPaid actor first second chart
    f0 f7 decode (P₀).total (P₀).modulo homes (P₀).boundaries control ((P₀).image m)
    before room positive nonempty columns role arity pointers
  exact ⟨fun machine=>Procedure.Exec.then firstRun.1 secondRun.1 machine,cheap_seq firstRun.2.1 secondRun.2.1,
    (P₀).transfer firstRun.2.2.1 (fun j _ hj=>secondRun.2.2 j (hj.trans_le low))⟩

local notation "atBook" => x.bookSnapshot begin_ peer wing w q p nd nodes hidden args oldPaid actor
  first second chart f0 f7 decode

include control in
/-- At the Book date the same ROM carries the values installed before the
population and histogram passes. The folded route computation reads them here. -/
theorem funded_book_pages (m : Memory w) (space:(P₀).stop≤begin_)
    (before:x.Before begin_ oldPaid actor wing peer (P₀).total (P₀).modulo homes (P₀).boundaries)
    (room:x.maskBase begin_<2^w) (positive:0<w) (nonempty:0<x.strips) (columns:0<x.scalar.columns)
    (role:(emit first).Fits w (x.primitive begin_)) (arity:(emit second).Fits w (x.primitive begin_))
    (pointers:∀j b,(chart j b).Fits (x.scalar.gather (x.primitive begin_)) x.scalar.shops w) :
    (P₀).Reads (atBook ((P₀).image m)) := by
  have beginRoom:=x.incoming begin_
  have ⟨s₁,s₂,s₃,s₄,s₅,s₆,s₇,s₈,s₉⟩:=x.layers begin_
  have low : (P₀).stop≤x.cohortEnd begin_ := by omega
  have bookRoom : (P₀).stop≤x.bookEnd begin_ := by omega
  have already:=(P₀).install m (show (P₀).stop<2^w by omega)
  have reads:=x.purchased_frames begin_ peer wing w q p nd nodes hidden args oldPaid actor first second chart
    f0 f7 decode (P₀).total (P₀).modulo homes (P₀).boundaries control ((P₀).image m) before
    room positive nonempty columns role arity pointers
  apply (P₀).transfer already.2.2.1
  intro j _ hj
  exact (reads.2.2.2.2 j (hj.trans_le bookRoom)).symm.trans
    (reads.2.2.1 j (.inl (hj.trans_le low)))

theorem funded_preflight_price (h factor paid : ℕ)
    (room:ProgramRoom x begin_ peer wing h factor paid) (hp:0<x.scalar.shops)
    (hf:0<factor) (degrees:x.degree=3) :
    (names (((P₀).program w).seq body)+(4+10*(P₀).words+ticks))*(w+1)≤
      24200200*((2^(h/2)+x.scalar.shops*factor)*(w+1)+paid*(w+1)) := by
  have extra := (P₀).cost_le w h (show (P₀).bytes≤2^(h/2) from room.data)
  have raw := x.purchased_price begin_ peer wing w q p nd nodes hidden args oldPaid actor first second chart
    f0 f7 decode (P₀).total (P₀).modulo homes (P₀).boundaries control h w factor paid room hp hf degrees
  have rowBound : x.paidRows≤paid := (Nat.le_add_left _ _).trans room.widthAndDraft
  have one : 0<2^(h/2) := Nat.two_pow_pos _
  have extraBudget : 100*(2^(h/2)+(P₀).rows+1)≤200*(2^(h/2)+x.scalar.shops*factor+paid) := by
    change 100*(2^(h/2)+x.paidRows+1)≤_;omega
  have charged:=extra.trans (Nat.mul_le_mul_right (w+1) extraBudget)
  calc
    _ = (names ((P₀).program w)+(4+10*(P₀).words))*(w+1)+(names body+ticks)*(w+1) := by rw [names_seq];ring
    _ ≤ 200*(2^(h/2)+x.scalar.shops*factor+paid)*(w+1)+
      24200000*((2^(h/2)+x.scalar.shops*factor)*(w+1)+paid*(w+1)) := Nat.add_le_add charged raw
    _ = _ := by ring

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
