import OAI.Hierarchy.TaggedWirePacketPortBits
import OAI.Hierarchy.TaggedWireTurnShelf
import OAI.Hierarchy.TaggedWirePacketMiddle

namespace OAI
/-! # Packet output addresses by the first original occurrence of a physical row -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal.MotifOuterTerms Tagged AdaptiveProbe TurnShelf CalendarTape
open scoped Classical

variable {F : Type} [Field F] {S N H copies p e : ℕ} {row : Row F S H copies} {phys : Fin N→Chord S}

namespace PostCode
variable {M n : ℕ}

theorem positive {m : ℕ} (route : Fin m→List (Fin M)) (bits : Fin m→ℕ)
    (rank : Fin n≃Σi,Fin (route i).length) (key : Fin M) (live : 0<routeLoad route bits key) :
    ∃q,NativeSlot.edge route rank q=key := by
  by_contra! none
  rw [←NativeSlot.mass_route route bits rank key] at live
  simp [NativeSlot.mass,none] at live

end PostCode

variable (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)
local notation "roles" => Fintype.card R.Roles
local notation "run" => R.install.steps R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "mass" => routeLoad run w
local notation "ids" => NativeSlot.edge run R.ordinal
local notation "wout" => congrArg (installedWidths phys) (R.install.counted R.order (R.bits c))

/-- A local aperture paid for by actual occurrences in this one packet.
Several role paths using the same physical resource share one sector
and use different weighted-prefix digits within it. -/
def postBundle (room : roles*2+(R.occurrences+1)*2≤2^p) (fits : ∀i,mass i≤2^e) :
    Bundle mass × Bool ↪ Aperture p e where
  toFun x := (⟨PostCode.after ids roles x.1.1 x.2,(PostCode.after_lt ids _ _ _).trans_le room⟩,
    ⟨x.1.2.val,x.1.2.isLt.trans_le (fits _)⟩)
  inj' := by
    rintro ⟨⟨i,j⟩,b⟩ ⟨⟨q,r⟩,t⟩ eq
    obtain ⟨header,digit⟩:=Prod.mk.inj eq
    have same:=PostCode.after_injective ids (PostCode.positive run w R.ordinal i (Nat.zero_lt_of_lt j.isLt))
      (PostCode.positive run w R.ordinal q (Nat.zero_lt_of_lt r.isLt)) (congrArg Fin.val header)
    obtain ⟨rfl,rfl⟩:=same
    obtain rfl : j=r := Fin.ext (congrArg (fun x : Fin (2^e) => x.val) digit)
    rfl

def postPlace (room : roles*2+(R.occurrences+1)*2≤2^p) (fits : ∀i,mass i≤2^e) :
    SiteBit (R.post c) s ↪ Aperture p e where
  toFun a := postBundle R c room fits ((NamedAperture.halfBits phys mass).symm
    ((NamedAperture.transport wout).symm ⟨s,a⟩))
  inj' _ _ eq := by
    have d := (NamedAperture.transport wout).symm.injective
      ((NamedAperture.halfBits phys mass).symm.injective ((postBundle R c room fits).injective eq))
    exact eq_of_heq (Sigma.mk.inj d).2

theorem postPlace_at (room : roles*2+(R.occurrences+1)*2≤2^p) (fits : ∀i,mass i≤2^e) (i)
    (j : Fin (w i)) (q : Fin (run i).length) (b : Bool) (atSite : (rowGraph phys).vertex ((run i).get q) b=s) :
    let a:=postPlace R c s room fits (NamedAperture.transportAt wout
      (NamedAperture.atPort phys mass (PacketTurns.paidPort phys run w R.ordinal i j q b atSite)))
    a.1.val=PostCode.after ids roles ((run i).get q) b ∧ a.2.val=NativeSlot.start run w R.ordinal i q+j.val := by
  let port:=PacketTurns.paidPort phys run w R.ordinal i j q b atSite
  let bundle:=(NamedAperture.halfBits phys mass).symm ((NamedAperture.transport wout).symm
    ⟨s,NamedAperture.transportAt wout (NamedAperture.atPort phys mass port)⟩)
  have eq : bundle=(port.1.1,port.1.2) := by
    dsimp only [bundle]
    rw [←NamedAperture.transport_pair,Equiv.symm_apply_apply,←NamedAperture.at_half,Equiv.symm_apply_apply]
  change PostCode.after ids roles bundle.1.1 bundle.2=_ ∧ bundle.1.2.val=_
  rw [eq]
  exact ⟨congrArg (fun e=>PostCode.after ids roles e b) (NativeSlot.allocation_edge run w R.ordinal _),
    NativeSlot.allocation_value run w R.ordinal i q j⟩

theorem packetData_paid {V : Type} (embed : Aperture p e→V) (cap : ℕ) (room : roles*2+(R.occurrences+1)*2≤2^p)
    (fits : ∀i,mass i≤2^e) (i) (j : Fin (w i)) (q : Fin (run i).length) (b : Bool)
    (atSite : (rowGraph phys).vertex ((run i).get q) b=s) (d : Aperture p e)
    (role : d.1.val=PostCode.after ids roles ((run i).get q) b)
    (digit : d.2.val=NativeSlot.start run w R.ordinal i q+j.val) :
    packetData roles cap embed d=.inl (embed (postPlace R c s room fits (NamedAperture.transportAt wout
      (NamedAperture.atPort phys mass (PacketTurns.paidPort phys run w R.ordinal i j q b atSite))))) := by
  have value:=postPlace_at R c s room fits i j q b atSite
  rw [packetData_new embed d (role ▸ Nat.le_add_right _ _)]
  exact congrArg (fun v=>Sum.inl (embed v)) (Prod.ext (Fin.ext (role.trans value.1.symm))
    (Fin.ext (digit.trans value.2.symm)))

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
