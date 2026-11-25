import OAI.Hierarchy.DescentRegisteredSectionPopulation
import OAI.Hierarchy.DescentArgumentWordRectangle

namespace OAI
/-! # Joint row budget for the old chip, new chip and compact registered resolve -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def rowVolume (h : ℕ) :=
  let m:=v.material
  h+m.oldHosts*h+m.hosts*h+m.oldHosts*m.oldGroups+m.hosts*m.groups+
    (h+1)^2*2^(h/2)*h

/-- Native scalar, previous/current population and lookup terms clipped by one shared
date budget. The compact resolver uses a subset of the actual current host rows. -/
theorem SectionPopulation.native_rows {v : PhysicalOrdinary F P} {A : ArgumentEntry v} {S : DescentCompiler.AtomSchedule}
    {i : ℕ} (p : SectionPopulation v A S i) (h : ℕ) (radix : v.vector.radix=S.radix) (nonempty : 0<v.vector.radix) :
    let Z:=v.rowVolume h
    let m:=v.material
    h≤Z ∧ m.oldHosts*h≤Z ∧ m.hosts*h≤Z ∧ m.oldHosts*m.oldGroups≤Z ∧ m.hosts*m.groups≤Z ∧
      v.resolver.hosts*h≤Z ∧ v.resolver.hosts*v.resolver.groups≤Z ∧
      v.vector.hosts*(v.vector.groups*v.vector.radix)≤Z ∧ v.vector.hosts*v.vector.groups≤Z ∧
      2^(h/2)*h≤Z ∧ (h+1)^2*2^(h/2)*h≤Z ∧ (h+1)*h≤Z :=by
  intro Z m
  have small : h≤Z ∧ m.oldHosts*h≤Z ∧ m.hosts*h≤Z ∧ m.oldHosts*m.oldGroups≤Z ∧
      m.hosts*m.groups≤Z ∧ (h+1)^2*2^(h/2)*h≤Z:=by
    dsimp only [Z,m,rowVolume]
    omega
  rcases small with ⟨origin,source,target,cs,ct,table⟩
  have rg : v.resolver.groups=m.groups:=p.resolver.2.trans p.vector.2
  have vr : v.vector.groups*v.vector.radix=m.oldGroups:=by
    rw [p.vector.2,p.material.2,radix,p.group_partition,p.donor.2]
  have vgroups : v.vector.groups≤ m.oldGroups:=by
    rw [←vr]
    exact Nat.le_mul_of_pos_right _ nonempty
  exact ⟨origin,source,target,cs,ct,(Nat.mul_le_mul_right h p.compact).trans target,
    (Nat.mul_le_mul p.compact rg.le).trans ct,(Nat.mul_le_mul p.vector.1.le vr.le).trans cs,
    (Nat.mul_le_mul p.vector.1.le vgroups).trans cs,
    DescentArgumentWordRectangle.control.trans table,table,DescentArgumentWordRectangle.h_control.trans table⟩

/-- A date pays for both of its resident grids and for a single half-word table. -/
theorem SectionPopulation.row_volume {v : PhysicalOrdinary F P} {A : ArgumentEntry v} {S : DescentCompiler.AtomSchedule}
    {i : ℕ} (p : SectionPopulation v A S i) (h : ℕ) (live : 0<S.hostSize i) :
    v.rowVolume h≤(5+2*(2^S.hostGain)*(S.radix+1))*
      (S.hostSize i*h+S.hostSize i*S.groupCount i)+(h+1)^2*2^(h/2)*h :=by
  let H:=S.hostSize i
  let G:=S.groupCount i
  let r:=S.radix
  let z:=2^S.hostGain
  have h₀ : h≤H*h:=by simpa using Nat.mul_le_mul_right h (show 1≤H from live)
  have h₁ : v.material.oldHosts*h≤2*(H*h):=by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right h p.old_hosts
  have h₂ : v.material.hosts*h≤(2*z*r)*(H*h):=by
    calc
      _≤(2*(H*(z*r)))*h:=Nat.mul_le_mul_right h p.new_hosts
      _=_:=by ring
  have oldG : v.material.oldHosts*v.material.oldGroups≤2*(H*G):=p.rectangles.1
  have newG : v.material.hosts*v.material.groups≤(2*z)*(H*G):=p.rectangles.2.1
  change h+_+_+_+_+_≤(5+2*z*(r+1))*(H*h+H*G)+_
  apply Nat.add_le_add_right
  calc
    _≤H*h+2*(H*h)+(2*z*r)*(H*h)+2*(H*G)+(2*z)*(H*G):=by gcongr
    _≤_:=by ring_nf; omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
