import OAI.Hierarchy.DescentOrdinaryMaterialScan
import OAI.Hierarchy.DescentParentFilterFused

namespace OAI
/-! Recover the single previous parent represented by a native seat on the actual old rack. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSixParty.Chronology DescentSIMDLookup DescentHaloWalkRAM DescentParallelBase.ParentFilter
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) (u : Setup) (v : Parts s) (r : Cell (chartBits s)) (z : Seat s)
local notation "read₀" => observations s u v z
local notation "P₀" => breadth s.degree
local notation "tok" => ticketLaw s u z r (read₀ 0 : Cell u.fieldBits)

/-- The size tests are only on surviving incidences, evaluated on the actual previous packed piece. -/
structure ParentRoom (Q K L : ℕ) : Prop where
  src : read₀ 6≠0→ read₀ 0≤P₀ ∧ read₀ 2<Q
  dst : read₀ 6≠0→ read₀ 1≤P₀ ∧ read₀ 3<Q
  weight : read₀ 6≠0→ read₀ 5≤L
  ticket : read₀ 6≠0→(tok).val<K

theorem active_mass (active : read₀ 6≠0) :
    liveMass (report u.oldBits u.gain u.slots (seatDonor s u.profile u.motifWidth u.slots v z.1 z.2.1) z.2.2)≠0 :=by
  intro blank
  apply active
  simp [observations,blank]

private theorem coding :
    (read₀ 6=0→∀i,read₀ i=0) ∧
    (read₀ 6≠0→0<read₀ 0 ∧ 0<read₀ 1 ∧ read₀ 4≤1 ∧ read₀ 6=1 ∧
      read₀ 7=(z.1.val*s.cap+z.2.1.val)*11+z.2.2.val) :=by
  unfold observations
  split
  · simp
  · rename_i live
    have left:=fun (a b c:ℕ) (h:¬(a=0 ∨ b=0 ∨ c=0))=>And.intro (show 0<b by omega) (show 0<c by omega)
    obtain ⟨left,right⟩:=left _ _ _ live
    have val (b : Bool) : b.toNat≤1:=by cases b <;> decide
    simp [left,right,val]

variable {Q K L : ℕ}
def parent (bounds : ParentRoom s u v r z Q K L) : Option (Source P₀ Q K L) :=
  if live : read₀ 6=0 then none else
    let good:=(coding s u v z).2 live
    some ⟨⟨⟨read₀ 0-1,by have h := (bounds.src live).1; have hpos := good.1; omega⟩,⟨read₀ 2,(bounds.src live).2⟩⟩,
          ⟨⟨read₀ 1-1,by have h := (bounds.dst live).1; have hpos := good.2.1; omega⟩,⟨read₀ 3,(bounds.dst live).2⟩⟩,
          decide (read₀ 4=1),⟨(tok).val,bounds.ticket live⟩,⟨read₀ 5,Nat.lt_succ_of_le (bounds.weight live)⟩⟩

def parentDigits {P Q K L b : ℕ} (low : ℕ) (p : Option (Source P Q K L)) (f : Fin 9) : Cell b :=
  (p.elim 0 (fun a=> ![a.src.path.val+1,a.dst.path.val+1,a.src.low.val,a.dst.low.val,a.upper.toNat,
    a.weight.val,1,low,a.ticket.val] f):ℕ)

theorem parent_read (bounds : ParentRoom s u v r z Q K L) (f : Fin 9) :
    Sheets.observed s u v r z f=parentDigits ((z.1.val*s.cap+z.2.1.val)*11+z.2.2.val) (parent s u v r z bounds) f :=by
  by_cases empty:read₀ 6=0
  · have zero :=(coding s u v z).1 empty
    fin_cases f <;> simp [Sheets.observed,parentDigits,parent,empty,zero,ticketLaw]
  · obtain ⟨lpos,rpos,upper,one,last⟩:=(coding s u v z).2 empty
    have left:read₀ 0-1+1=read₀ 0:=by omega
    have right:read₀ 1-1+1=read₀ 1:=by omega
    have flag:(decide (read₀ 4=1)).toNat=read₀ 4:=by
      by_cases test:read₀ 4=1
      · simp [test]
      · have zero:read₀ 4=0:=by omega
        simp [zero]
    fin_cases f <;> simp [Sheets.observed,parentDigits,parent,left,right,one,last,flag]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
