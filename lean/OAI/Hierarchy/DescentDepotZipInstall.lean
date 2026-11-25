import OAI.Hierarchy.DescentDepotZipGates

namespace OAI
/-! # Genuine installation of the old donor's six-input and rank/width binary lookup tables -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Binary
open DescentPackedZip DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w K H G : ℕ} (s : DepotRAM.Shape) (M unit base : ℕ)
local notation "N" => s.blocks*(2*s.cap)
local notation "D" => s.degree+1
local notation "cb" => DescentSignedCableCodec.width s.degree s.cap
local notation "ob" => (Owners.digits s.blocks s.degree s.short*3)*s.blocks
local notation "ub" => s.short*«fields» s.blocks s.degree (2*s.cap)
local notation "bytes" => count s*(2*2^(unit*M))

def bank (j : Kind s) := Book.tables (menu s) unit M base (ordinal s j)
local notation "shelf" => bank s M unit base

def joints : Tables6 := ⟨shelf (.inl 0),shelf (.inl 1),shelf (.inl 2),shelf (.inl 3),shelf (.inl 4)⟩
def cables (i : Fin N) := shelf (.inr (.inl i))
def owners (i : Fin D) := shelf (.inr (.inr (.inl i)))
def layoutBit := shelf (.inr (.inr (.inr 0)))

def «fields» (R : Resident.Sources s K) : Resident.Sources s K :=
  { R with cableTables:=cables s M unit base,ownerTables:=owners s M unit base }

local notation "done" => Book.image (menu s) unit M base
local notation "code" => Book.install (menu s) unit M w base

def Installed (m : Memory w) : Prop :=
  Fixed s (joints s M unit base) M m ∧
  (∀i,Static (cables s M unit base i) (Gather.setField (d:=cb) i) M m) ∧
  (∀i,Static (owners s M unit base i) (Gather.setField (d:=ob) i) M m) ∧
  Static (layoutBit s M unit base) (Owners.LayoutBit.join ub) M m

theorem installed_of_all (m : Memory w)
    (static : ∀i,Static (Book.tables (menu s) unit M base i) (menu s i).eval M m) : Installed s M unit base m := by
  have hit (j : Kind s) : Static (shelf j) (gates s j).eval M m := by
    let Q : Book.Gate → Prop := fun g => Static (shelf j) g.eval M m
    exact (congrArg Q (menu_at s j)).mp (static (ordinal s j))
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · exact hit (.inl 0)
  · exact hit (.inl 1)
  · exact hit (.inl 2)
  · exact hit (.inl 3)
  · exact hit (.inl 4)
  · exact fun i=>hit (.inr (.inl i))
  · exact fun i=>hit (.inr (.inr (.inl i)))
  · exact hit (.inr (.inr (.inr 0)))

theorem install (m : Memory w) (large : 2*totalBits s+1≤unit) (room : base+bytes<2^w) :
    (code).Exec m (done m) (4+10*bytes) ∧ Installed s M unit base (done m) ∧
    (∀x,x<base ∨ base+bytes≤x→done m x=m x) ∧ CheapCode code := by
  have caps : ∀j,(menu s j).left+(menu s j).right≤unit :=
    fun j=>(width s ((ordinal s).symm j)).trans large
  obtain ⟨run,static,frame,cheap⟩:=Book.mount (menu s) unit M base m caps room
  exact ⟨run,installed_of_all s M unit base _ static,frame,cheap⟩

theorem rooms (j : Kind s) (out : ℕ) (large : 2*totalBits s+1≤unit) (before : base+bytes≤out) (fit : out<2^w) :
    (shelf j).shift.Fits w out ∧ (shelf j).apply.Fits w out :=
  Book.geometry (menu s) unit M base (ordinal s j) before fit (by simpa only [menu_at] using (width s j).trans large)

theorem immutable (z : DescentPacking.PackedMatch.Shape) (R : Resident.Sources s K) (B prof C pad scale : ℕ)
    (m : Memory w) (sealed : Installed s M unit base m)
    (fresh : Fresh.Fixed (H:=H) (G:=G) (M:=M) s z R.fresh B prof C pad scale m) :
    Resident.Immutable (H:=H) (G:=G) (M:=M) s z («fields» s M unit base R) B prof C pad scale m :=
  ⟨sealed.2.1,sealed.2.2.1,fresh⟩

theorem install_names : DescentStaticWordColumn.names code=15*(bytes+1) := Book.names ..

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Binary

end OAI
