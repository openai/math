import OAI.Hierarchy.TaggedWirePublicSlab
import OAI.Hierarchy.TaggedWideSpillHopWords
import OAI.Hierarchy.TaggedWideChordAperture

namespace OAI
/-! # Reading the selected spill bit from the native public role table -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open AdaptiveProbe ReportSockets Tagged WireTelescope RoleProgram
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical
variable {h W k attempts p e deg width : ℕ} {V : Type}
    (S : PurchaseSampler) (s : Site h (2^W) k)
local notation "Fib" => Fiber (attempts:=attempts) S s
variable (room : ∀a : Fiber (attempts:=attempts) S s,∀t,RoleProgram.labelled S t a.val<2^p)
    (seat : Fiber (attempts:=attempts) S s→Fin deg)

/-- The two fixed local gathers expose complete chord replicas. Numeric
role and output polarity select the corresponding replica and the turn
table selects one bit in it. -/
def spillAperture (q : TurnShelf.Aperture p e) : ((V⊕(Fin deg×Fin width))⊕(Fin deg×Fin width))⊕Bool :=
  Sum.elim (fun x : (Bool×Fib)×Row e=>
    if inside : x.2.val<width then
      if x.1.1 then .inl (.inr (seat x.1.2,⟨x.2.val,inside⟩))
      else .inl (.inl (.inr (seat x.1.2,⟨x.2.val,inside⟩)))
    else .inr false) Sum.inr (slabPins S s room q)

theorem spillAperture_read {P : Type} {sizes : Bool→P→ℕ}
    (parts : ∀b,PassiveWindow.Parts P (Fin deg) width (sizes b))
    (state : Bool→P→ℕ→Bool) (v : V→Bool) (q : TurnShelf.Aperture p e)
    (a : Fib) (b : Bool) (port : P) (role : q.1.val=RoleProgram.labelled S b a.val)
    (hits : (parts b).owner (seat a)=some port) (fits : sizes b port≤width)
    (active : q.2.val<sizes b port) :
    let bank:=fun side=>Function.uncurry (ChordAperture.canonical (parts side) (state side))
    Sum.elim (Sum.elim (Sum.elim v (bank false)) (bank true)) id (spillAperture S s room seat q)=
      state b port q.2.val := by
  intro bank
  rw [spillAperture,slabPins_at S s room q a b role]
  have small:=(active).trans_le fits
  cases b <;> simp [small,bank,ChordAperture.canonical,hits,active]

/-- The role lookup and the mixed-radix cut agree on a genuine row, including
when the retained chunk shares its chord with earlier active rows. -/
theorem spillAperture_row {K n : ℕ} (atSite : Fin K) (rest active : Bool→Widths K)
    (z : ∀b,State (rest b+active b) atSite) (ends : Fin n→Chord K) (count : Fin n→ℕ)
    (b : Bool) (same : installedWidths ends count=active b) (u : (bitGraph (rowGraph ends) count).Port atSite)
    (parts : ∀t,PassiveWindow.Parts ((portGraph K).Port atSite) (Fin deg) width
      (fun port=>(rest t+active t) port.val.1))
    (a : Fib) (q : TurnShelf.Aperture p e) (v : V→Bool) (code : q.1.val=RoleProgram.labelled S b a.val)
    (owner : (parts b).owner (seat a)=some (sourcePort ends count u))
    (fits : (rest b+active b) (ends u.1.1.1)≤width)
    (digit : q.2.val=datedBase ends count u.1.1.1+u.1.1.2.val) :
    let bank:=fun side=>Function.uncurry (ChordAperture.canonical (parts side)
      (fun port=>Nat.testBit (z side port).val))
    Sum.elim (Sum.elim (Sum.elim v (bank false)) (bank true)) id (spillAperture S s room seat q)=
      rowBits ends count (cast (congrArg (fun C=>State C atSite) same.symm)
        (splitPortState (rest b) (active b) atSite (z b)).2) u := by
  intro bank
  have off : (NamedAperture.sourceBit ends count u.1.1).val=q.2.val :=
    (NamedAperture.offset ends count u.1.1).trans digit.symm
  have small := (NamedAperture.sourceBit ends count u.1.1).isLt
  rw [off,same] at small
  rw [spillAperture_read S s room seat parts (fun side port=>Nat.testBit (z side port).val) v q a b
      (sourcePort ends count u) code owner fits (by
        change q.2.val<(rest b) (ends u.1.1.1)+(active b) (ends u.1.1.1)
        omega),
    datedSpill_chord ends count (rest b) (active b) same atSite (z b) u,digit];rfl


end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal

end

end OAI
