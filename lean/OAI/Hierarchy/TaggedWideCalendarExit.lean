import OAI.Hierarchy.TaggedWireTerminalPhysicalValue
import OAI.Hierarchy.TaggedWireEndMuxData
import OAI.Hierarchy.TaggedWidePrivateOrdinals
import OAI.Hierarchy.TaggedWireTimelineLast
import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedWideDataWorkspace
import OAI.Hierarchy.TaggedWideTimeOccupancy

namespace OAI
/-! # Fixed physical endpoint of the native paid terminal calendar -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open AdaptiveProbe ReportSockets Tagged TaggedShorterSupergroups WireTelescope CalendarTape
open RoleProgram ProtocolRAM.Calendar.CatalogueRows
open ThreeFlat Routing
open scoped Classical BigOperators
set_option quotPrecheck false
variable {h W k attempts H p e : ℕ} {V : Type} (S : PurchaseSampler)
    (dir : Directory (reserved h W (copies k attempts)) H)

/-- Board wires of the last state, private switch and paid positive output
select literal physical signals. Non-output roles have a zero bit. -/
def endPin (previous : Public S h W k attempts→ℕ→V⊕Bool)
    (privateBits : Free S h (2^W) k→Bool→ℕ→V⊕Bool)
    (positiveBits : Fin dir.groups×Fin H→ℕ→V⊕Bool) :
    Bool→Public S h W k attempts→ℕ→V⊕Bool
  | false,r=>previous r
  | true,.inl (.inl (f,s))=>privateBits f s
  | true,.inl (.inr a)=>positiveBits (packed dir a)
  | true,.inr _=>fun _=>.inr false

theorem endPin_value (previous : Public S h W k attempts→ℕ→V⊕Bool)
    (privateBits : Free S h (2^W) k→Bool→ℕ→V⊕Bool)
    (positiveBits : Fin dir.groups×Fin H→ℕ→V⊕Bool) (v : V→Bool)
    (t : Bool) (r : Public S h W k attempts) (j : ℕ) :
    Sum.elim v id (endPin S dir previous privateBits positiveBits t r j)=
      publicData S dir (fun r j=>Sum.elim v id (previous r j))
        (fun f b j=>Sum.elim v id (privateBits f b j)) (fun a j=>Sum.elim v id (positiveBits a j)) t r j := by
  rcases t with _|_ <;> rcases r with ((f|a)|g) <;> rfl

variable (vtx : Site h (2^W) k)
local notation "Fib" => Fiber (attempts:=attempts) S vtx
variable (roleRoom : ∀a:Fiber (attempts:=attempts) S vtx,∀t,RoleProgram.labelled S t a.val<2^p)
    (previous : Public S h W k attempts→ℕ→V⊕Bool)
    (freeBits : Free S h (2^W) k→Bool→ℕ→V⊕Bool)
    (positiveBits : Fin dir.groups×Fin H→ℕ→V⊕Bool)

def aperturePin (q : TurnShelf.Aperture p e) : V⊕Bool :=
  Sum.elim (fun z : (Bool×Fib)×Row e=>endPin S dir previous freeBits positiveBits z.1.1 z.1.2.val z.2.val)
    Sum.inr (slabPins S vtx roleRoom q)

theorem aperture_read (v : V→Bool) (q : TurnShelf.Aperture p e) :
    Sum.elim v id (aperturePin S dir vtx roleRoom previous freeBits positiveBits q)=
      (Sum.elim (fun z : (Bool×Fib)×Row e=>
        publicData S dir (fun r j=>Sum.elim v id (previous r j)) (fun f b j=>Sum.elim v id (freeBits f b j))
          (fun a j=>Sum.elim v id (positiveBits a j)) z.1.1 z.1.2.val z.2.val) id ∘ slabPins S vtx roleRoom) q := by
  change Sum.elim v id (Sum.elim _ _ (slabPins S vtx roleRoom q))=Sum.elim _ id (slabPins S vtx roleRoom q)
  cases slabPins S vtx roleRoom q with
  | inl z=>exact endPin_value S dir previous freeBits positiveBits v z.1.1 z.1.2.val z.2.val
  | inr bit=>rfl

section Sources
variable {T : Type} {ports lanes view : ℕ} (es : List ProtocolRAM.Calendar.Event)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (cap : b.Private order→ℕ) (histCap : Public S h W k attempts→ℕ) (width : T→ℕ)
local notation "Roles" => Public S h W k attempts
local notation "Times" => (r:Roles) × Fin (histCap r)
local notation "D" => WideStack.DataWorkspace T (Fin dir.groups) (b.Private order) Roles H lanes
    (es.length+1) view width cap histCap

def lastHistoryPin (r : Roles) (j : ℕ) : D⊕Bool :=
  if h : j<histCap r then .inl (.inr (.inr (.inl (timeOrder (Q:=Times) es (Fin.last es.length,⟨r,j,h⟩)))))
  else .inr false

def freeOutputPin (f : Free S h (2^W) k) (side : Bool) (j : ℕ) : D⊕Bool :=
  let i:=(b.freeOrdinal order) f
  if h : j<cap i then .inl (.inr (.inl (side,⟨i,j,h⟩))) else .inr false

def positiveOutputPin (loc : Fin dir.groups×Fin H) (j : ℕ) : D⊕Bool :=
  if h : j<view then .inl (.inr (.inr (.inr (loc,⟨j,h⟩)))) else .inr false

/-- Source projection from a site's binary barrel all the way to the fixed
three relevant blocks of the physical shared input. -/
def outputAperture (s : Site h (2^W) k) (fits : ∀a:Fiber (attempts:=attempts) S s,∀t,RoleProgram.labelled S t a.val<2^p) :
    TurnShelf.Aperture p e→D⊕Bool :=
  aperturePin S dir s fits (lastHistoryPin S dir es b order cap histCap width)
    (freeOutputPin S dir es b order cap histCap width)
    (positiveOutputPin S dir es b order cap histCap width)

theorem outputAperture_value (s : Site h (2^W) k) (fits : ∀a:Fiber (attempts:=attempts) S s,∀t,RoleProgram.labelled S t a.val<2^p)
    (v : D→Bool) (q : TurnShelf.Aperture p e) :
    Sum.elim v id (outputAperture S dir es b order cap histCap width s fits q)=
      (Sum.elim (fun z : (Bool×Fiber (attempts:=attempts) S s)×Row e=>
        publicData S dir
          (fun r j=>if h : j<histCap r then v (.inr (.inr (.inl (timeOrder (Q:=Times) es (Fin.last es.length,⟨r,j,h⟩))))) else false)
          (fun f side j=>if h : j<cap ((b.freeOrdinal order) f) then v (.inr (.inl (side,⟨(b.freeOrdinal order) f,j,h⟩))) else false)
          (fun loc j=>if h : j<view then v (.inr (.inr (.inr (loc,⟨j,h⟩)))) else false) z.1.1 z.1.2.val z.2.val) id
        ∘ slabPins S s fits) q := by
  rw [outputAperture,aperture_read]
  have historyRead :
      (fun r j => Sum.elim v id (lastHistoryPin S dir es b order cap histCap width r j)) =
      fun r j => if hj : j < histCap r then
        v (.inr (.inr (.inl (timeOrder (Q:=Times) es (Fin.last es.length, ⟨r,j,hj⟩)))))
      else false := by
    funext r j
    by_cases hj : j < histCap r <;> simp [lastHistoryPin, hj]
  have privateRead :
      (fun f side j => Sum.elim v id (freeOutputPin S dir es b order cap histCap width f side j)) =
      fun f side j => if hj : j < cap ((b.freeOrdinal order) f) then
        v (.inr (.inl (side, ⟨(b.freeOrdinal order) f,j,hj⟩)))
      else false := by
    funext f side j
    by_cases hj : j < cap ((b.freeOrdinal order) f) <;> simp [freeOutputPin, hj]
  have paidRead :
      (fun loc j => Sum.elim v id (positiveOutputPin S dir es b order cap histCap width loc j)) =
      fun loc j => if hj : j < view then v (.inr (.inr (.inr (loc,⟨j,hj⟩)))) else false := by
    funext loc j
    by_cases hj : j < view <;> simp [positiveOutputPin, hj]
  rw [historyRead, privateRead, paidRead]

/-- Read either an old endpoint or a paid endpoint of an original private
or purchased role after selecting its fixed native aperture code. -/
theorem outputAperture_at (s : Site h (2^W) k) (fits : ∀a:Fiber (attempts:=attempts) S s,∀t,RoleProgram.labelled S t a.val<2^p)
    (v : D→Bool) (q : TurnShelf.Aperture p e) (a : Fiber (attempts:=attempts) S s) (t : Bool)
    (code : q.1.val=RoleProgram.labelled S t a.val) :
    Sum.elim v id (outputAperture S dir es b order cap histCap width s fits q)=
      Sum.elim v id (endPin S dir (lastHistoryPin S dir es b order cap histCap width)
        (freeOutputPin S dir es b order cap histCap width) (positiveOutputPin S dir es b order cap histCap width)
        t a.val q.2.val) := by
  unfold outputAperture aperturePin
  rw [slabPins_at S s fits q a t code]
  rfl

theorem lastHistoryPin_value (s : Site h (2^W) k)
    (fits : ∀a:Fiber (attempts:=attempts) S s,∀t,RoleProgram.labelled S t a.val<2^p) (v : D→Bool)
    (q : TurnShelf.Aperture p e) (a : Fiber (attempts:=attempts) S s)
    (code : q.1.val=RoleProgram.labelled S false a.val) (live : q.2.val<histCap a.val) :
    Sum.elim v id (outputAperture S dir es b order cap histCap width s fits q)=
      v (.inr (.inr (.inl (bodyIndex es (Fin.last es.length) (⟨a.val,q.2.val,live⟩:Times))))) := by
  rw [outputAperture_at S dir es b order cap histCap width s fits v q a false code]
  simp [endPin,lastHistoryPin,live,bodyIndex,timeOrder]


end Sources

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
end

end OAI
