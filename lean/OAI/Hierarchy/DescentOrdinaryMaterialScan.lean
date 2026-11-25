import OAI.Hierarchy.DescentOrdinaryRawObserved
import OAI.Hierarchy.DescentMaterialRegisterJoin
import OAI.Hierarchy.DescentActorRechunk

namespace OAI
/-! All signed and capture fields share one contiguous allocation and one change of group pitch. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Sheets
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) (u : Setup) {H G M w : ℕ}
def bits := totalBits s+chartBits s
def count :=15*roles s
def fieldId (f : Fin 15) (z : Seat s) : Fin (count s) :=finProdFinEquiv (f,seatIndex s z)
def id (f : Fin 9) (z : Seat s) :=fieldId s (f.castLE (by decide)) z
def rawIndex (f : Fin 6) : Fin 15:=⟨9+f.val,by have:=f.isLt;omega⟩
def rawId (f : Fin 6) (z : Seat s) :=fieldId s (rawIndex f) z
def observed (v : Parts s) (rev : Cell (chartBits s)) (z : Seat s) (f : Fin 9) : Cell u.fieldBits :=
  if j:f.val<8 then (observations s u v z ⟨f.val,j⟩:ℕ)
  else ticketLaw s u z rev (observations s u v z 0:Cell u.fieldBits)
def allFields (v : Parts s) (rev : Cell (chartBits s)) (z : Seat s) (f : Fin 15) : Cell u.fieldBits :=
  if old : f.val<9 then observed s u v rev z ⟨f.val,old⟩
  else rawObserved s u v rev z ⟨f.val-9,by have:=f.isLt;omega⟩
def law (i : ℕ) (joint : Cell (bits s)) : Cell u.fieldBits :=
  if live : i<count s then
    let j : Fin 15×Fin (roles s):=finProdFinEquiv.symm ⟨i,live⟩
    let v:=(DescentRawCablePanel.pair (totalBits s) (chartBits s)).symm joint
    allFields s u (separate s v.1) v.2 ((seatIndex s).symm j.2) j.1
  else 0

theorem read_all (z : Seat s) (i : Fin 15) (v : Parts s) (r : Cell (chartBits s)) :
    law s u (fieldId s i z).val (RegisterJoin.joined (combine s v) r)=allFields s u v r z i :=by
  unfold law
  rw [dite_eq_left (fieldId s i z).isLt]
  let pair := (i,seatIndex s z)
  have decode : (finProdFinEquiv.symm (fieldId s i z) : Fin 15×Fin (roles s)) = pair := finProdFinEquiv.symm_apply_apply pair
  simp only [RegisterJoin.joined,Equiv.symm_apply_apply,separate_combine]
  change allFields s u v r ((seatIndex s).symm (finProdFinEquiv.symm (fieldId s i z)).2) (finProdFinEquiv.symm (fieldId s i z)).1 = _
  rw [decode]
  simp only [pair,Equiv.symm_apply_apply]
theorem read_law (z : Seat s) (i : Fin 9) (v : Parts s) (r : Cell (chartBits s)) :
    law s u (id s i z).val (RegisterJoin.joined (combine s v) r)=observed s u v r z i := by
  rw [id,read_all];simp [allFields,i.isLt]
theorem read_raw (z : Seat s) (i : Fin 6) (v : Parts s) (r : Cell (chartBits s)) :
    law s u (rawId s i z).val (RegisterJoin.joined (combine s v) r)=rawObserved s u v r z i :=by
  rw [rawId,read_all]
  simp [allFields,rawIndex]

def phase (H G M w base : ℕ) (both : Bank) : NativePhase w :=
  let f:=law s u
  ⟨RoleScans.cpu f H G M w base (count s) both,RoleScans.ticks (bits s) H G M (count s),
    RoleScans.image f H G M base (count s) both,
    cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)⟩
def beginAt (H G M base : ℕ):=RoleScans.home (bits s) H G M (count s) base
def bank (H G M base : ℕ):Bank:=⟨beginAt s H G M base,Nat.clog 2 (count s*(H*chunks G M)+1)⟩
def «fields» (v : Fin H→Fin G→Parts s) (rev : Fin H→Fin G→Cell (chartBits s)) (j : Fin (count s)) (h : Fin H) (g : Fin G) : Cell u.fieldBits :=
  let key : Fin 15×Fin (roles s):=finProdFinEquiv.symm j
  allFields s u (v h g) (rev h g) ((seatIndex s).symm key.2) key.1

variable (base : ℕ) (both : Bank) (m : Memory w) (below : both.base+both.size≤base)
    (cap : H*chunks G M≤both.size) (bill : M*max (bits s) u.fieldBits≤w/2)
    (room : RoleScans.limit (bits s) H G M base (count s)<2^w)
include below cap bill room in
theorem any :
    let run:=phase s u H G M w base both
    run.Runs m ∧ (∀x,x<base ∨ RoleScans.limit (bits s) H G M base (count s)≤x→ run.image m x=m x) :=by
  intro run
  have yes:=RoleScans.any_run (law s u) base (count s) both m below cap bill room
  exact ⟨yes.1,yes.2.1⟩

include below cap bill room in
theorem run (v : Fin H→Fin G→Parts s) (rev : Fin H→Fin G→Cell (chartBits s))
    (prior : Reads both (fun h g=>RegisterJoin.joined (combine s (v h g)) (rev h g)) M m) :
    let out:=(phase s u H G M w base both).image m
    ∀j : Fin (count s),∀p : Row H G M,out ((bank s H G M base).base+j.val*(H*chunks G M)+(row H G M p).val)=
      ((data («fields» s u v rev j) p).val:Word w) :=by
  intro out j p
  obtain ⟨⟨f,z⟩,rfl⟩:=finProdFinEquiv.surjective j
  obtain ⟨seat,rfl⟩:=(seatIndex s).surjective z
  let jp:=fieldId s f seat
  have law_eq : (fun h g => law s u jp.val (RegisterJoin.joined (combine s (v h g)) (rev h g))) =
      «fields» s u v rev jp := by
    funext h g
    rw [show law s u jp.val (RegisterJoin.joined (combine s (v h g)) (rev h g)) =
        allFields s u (v h g) (rev h g) seat f from read_all s u seat f (v h g) (rev h g)]
    simp only [«fields»,jp,fieldId,Equiv.symm_apply_apply]
  have hit := RoleScans.read (law s u) base (count s) both m below cap bill room _ prior jp p
  rw [law_eq] at hit
  exact hit

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Sheets

end OAI
