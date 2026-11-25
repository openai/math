import OAI.Hierarchy.ProtocolRAMCalendarCatalystArchive

namespace OAI
/-! # Fixed pointer and kind words for the chronological reserve scatter -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Computability.VPVNP.BurstRAM PrivateRAM Calendar
open scoped Fin.CommRing Classical
variable {w count payload n : ℕ}

def pointerWord (id amount : Fin n→ℕ) (u : ℕ) : ℕ :=
  if h : u/2<n then if u%2=0 then id ⟨u/2,h⟩ else amount ⟨u/2,h⟩ else 0

theorem pointer_even (id amount : Fin n→ℕ) (i : Fin n) : pointerWord id amount (2*i.val)=id i := by
  simp [pointerWord,i.isLt]

theorem pointer_odd (id amount : Fin n→ℕ) (i : Fin n) : pointerWord id amount (2*i.val+1)=amount i := by
  have d : (2*i.val+1)/2=i.val := by omega
  have m : (2*i.val+1)%2=1 := by omega
  simp [pointerWord,d,m,i.isLt]

/-- The two constant tables occupy disjoint boot intervals. Every slot has
two entries even when its eventual width is zero. -/
def mount (a : ReserveUse.Archive) (id amount : Fin n→ℕ) (raw : Memory w) : Memory w :=
  fun u=>if a.kind.base≤u ∧ u<a.kind.base+2*n then ((u-a.kind.base)%2:ℕ)
    else if a.pointer.base≤u ∧ u<a.pointer.base+2*n then pointerWord id amount (u-a.pointer.base)
    else raw u

private theorem mount_pair (a : ReserveUse.Archive) (id amt : Fin n→ℕ) (raw : Memory w)
    (ordered : a.kind.base+2*n≤a.pointer.base) (kindSize : 2*n≤a.kind.size)
    (ptrSize : 2*n≤a.pointer.size) (wide : 2*n≤2^w) (v : ℕ) (small : v<2*n) :
    a.kind.read (mount a id amt raw) (v:Word w)=((v%2:ℕ):Word w) ∧
    a.pointer.read (mount a id amt raw) (v:Word w)=(pointerWord id amt v:Word w) := by
  have kw : a.kind.base≤a.kind.base+v ∧ a.kind.base+v<a.kind.base+2*n := by omega
  have pw : a.pointer.base≤a.pointer.base+v ∧ a.pointer.base+v<a.pointer.base+2*n := by omega
  have outside : ¬(a.kind.base≤a.pointer.base+v ∧ a.pointer.base+v<a.kind.base+2*n) := by omega
  simp [Bank.read,Fin.val_cast_of_lt (small.trans_le wide),Nat.mod_eq_of_lt (small.trans_le kindSize),
    Nat.mod_eq_of_lt (small.trans_le ptrSize),mount,kw,pw,outside]

theorem directory (a : ReserveUse.Archive) (id amt : Fin n→ℕ) (raw : Memory w)
    (ordered : a.kind.base+2*n≤a.pointer.base) (kindSize : 2*n≤a.kind.size)
    (ptrSize : 2*n≤a.pointer.size) (wide : 2*n≤2^w) (i : Fin n) :
    let m := mount a id amt raw
    (a.kind.read m ((2*i.val:ℕ):Word w)=0 ∧ a.kind.read m ((2*i.val+1:ℕ):Word w)≠0) ∧
      (a.pointer.read m ((2*i.val:ℕ):Word w)=(id i:Word w) ∧
       a.pointer.read m ((2*i.val+1:ℕ):Word w)=(amt i:Word w)) := by
  dsimp only
  have hi := i.isLt
  have pos : 1<2^w := by omega
  obtain ⟨ke,pe⟩ := mount_pair a id amt raw ordered kindSize ptrSize wide (2*i.val) (by omega)
  obtain ⟨ko,po⟩ := mount_pair a id amt raw ordered kindSize ptrSize wide (2*i.val+1) (by omega)
  have m : (2*i.val+1)%2=1 := by omega
  refine ⟨⟨by simpa using ke,?_⟩,by simpa [pointer_even] using pe,by simpa [pointer_odd] using po⟩
  intro eq
  have vals := congrArg Fin.val (ko.symm.trans eq)
  have bad : (1:ℕ)=0 := by simpa only [m,Fin.val_cast_of_lt pos,Fin.val_zero] using vals
  omega

theorem frame (a : ReserveUse.Archive) (id amt : Fin n→ℕ) (raw : Memory w) (u : ℕ)
    (kout : ¬(a.kind.base≤u ∧ u<a.kind.base+2*n))
    (pout : ¬(a.pointer.base≤u ∧ u<a.pointer.base+2*n)) :
    mount a id amt raw u=raw u := by simp [mount,kout,pout]

/-- The final memory need retain just the two fixed boot intervals. The
owner and amount then come from the two recorded event cells, which may
occupy different slabs in the same history bank. -/
theorem observed_fields (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw mem : Memory w) (site : Fin n→Fin count) (bits : Fin n→ℕ)
    (ordered : a.kind.base+2*n≤a.pointer.base) (ks : 2*n≤a.kind.size)
    (ps : 2*n≤a.pointer.size) (wide : 2*n≤2^w)
    (kept : ∀ (u : ℕ),u<2*n →
      mem (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      mem (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u))
    (owners : ∀i,id i<a.history.size ∧ id i<2^w ∧
      mem (a.history.base+id i)=((site i).val:Word w))
    (amounts : ∀i,amt i<a.history.size ∧ amt i<2^w ∧
      mem (a.history.base+amt i)=(bits i:Word w)) :
    (∀i : Fin n,a.kind.read mem ((2*i.val:ℕ):Word w)=0 ∧ a.kind.read mem ((2*i.val+1:ℕ):Word w)≠0) ∧
    (∀i : Fin n,a.history.read mem (a.pointer.read mem ((2*i.val:ℕ):Word w))=((site i).val:Word w)) ∧
    (∀i : Fin n,a.history.read mem (a.pointer.read mem ((2*i.val+1:ℕ):Word w))=(bits i:Word w)) := by
  have keep (u : ℕ) (hu : u<2*n) :
      a.kind.read mem (u:Word w)=a.kind.read (mount a id amt raw) (u:Word w) ∧
      a.pointer.read mem (u:Word w)=a.pointer.read (mount a id amt raw) (u:Word w) := by
    simpa [Bank.read,Fin.val_cast_of_lt (hu.trans_le wide),Nat.mod_eq_of_lt (hu.trans_le ks),
      Nat.mod_eq_of_lt (hu.trans_le ps)] using kept u hu
  have keys (i : Fin n) := directory a id amt raw ordered ks ps wide i
  refine ⟨?_,?_,?_⟩
  · intro i
    have hi := i.isLt
    rw [(keep (2*i.val) (by omega)).1,(keep (2*i.val+1) (by omega)).1]
    exact (keys i).1
  · intro i
    have hi := i.isLt
    rw [(keep (2*i.val) (by omega)).2,(keys i).2.1]
    simpa [Bank.read,Fin.val_cast_of_lt (owners i).2.1,Nat.mod_eq_of_lt (owners i).1]
      using (owners i).2.2
  · intro i
    have hi := i.isLt
    rw [(keep (2*i.val+1) (by omega)).2,(keys i).2.2]
    simpa [Bank.read,Fin.val_cast_of_lt (amounts i).2.1,Nat.mod_eq_of_lt (amounts i).1]
      using (amounts i).2.2

theorem observed (a : ReserveUse.Archive) (b : RouteSettlement.Banks)
    (id amt : Fin n→ℕ) (raw mem : Memory w) (site : Fin n→Fin count) (bits : Fin n→ℕ)
    (ordered : a.kind.base+2*n≤a.pointer.base) (ks : 2*n≤a.kind.size)
    (ps : 2*n≤a.pointer.size) (wide : 2*n≤2^w)
    (kept : ∀ (u : ℕ),u<2*n →
      mem (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      mem (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u))
    (owners : ∀i,id i<a.history.size ∧ id i<2^w ∧
      mem (a.history.base+id i)=((site i).val:Word w))
    (amounts : ∀i,amt i<a.history.size ∧ amt i<2^w ∧
      mem (a.history.base+amt i)=(bits i:Word w)) :
    ∀i,(ReserveUse.word a b).eval mem ((2*i.val:ℕ):Word w)=(ReserveUse.address b site i:Word w) ∧
      (ReserveUse.word a b).eval mem ((2*i.val+1:ℕ):Word w)=(bits i:Word w) := by
  obtain ⟨kind,owner,amount⟩ := observed_fields a id amt raw mem site bits ordered ks ps wide kept owners amounts
  exact ReserveUse.loaded_of_archive a b site bits mem kind owner amount

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
