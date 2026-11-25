import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # A finite collection of physically mounted, typed short lookup tables -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ROM
open DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
/-- A page is shared by every host, every group, and every live node in that
batch. An address outside a table's typed input domain has the literal zero. -/
structure Page where
  bits : ℕ
  number : Cell bits→ℕ

def point (p : Page) (j : ℕ) : ℕ := if ok : j<2^p.bits then p.number ⟨j,ok⟩ else 0

def contents {P : ℕ} (pages : Fin P→Page) (width : ℕ) (j : ℕ) : ℕ :=
  if ok : j/2^width<P then point (pages ⟨_,ok⟩) (j%2^width) else 0

def mount {P : ℕ} (pages : Fin P→Page) (width w base : ℕ) :=
  DescentStaticWordColumn.program w base (contents pages width) (P*2^width)

def after {P w : ℕ} (pages : Fin P→Page) (width base : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (contents pages width) m (P*2^width)

def bank {P : ℕ} (pages : Fin P→Page) (width base : ℕ) (p : Fin P) : Bank:=⟨base+p.val*2^width,(pages p).bits⟩

theorem run {P w : ℕ} (pages : Fin P→Page) (width base : ℕ) (m : Memory w) (room : base+P*2^width<2^w) :
    (mount pages width w base).Exec m (after pages width base m) (4+10*(P*2^width)) ∧
    DescentStaticWordColumn.names (mount pages width w base)=15*(P*2^width+1) :=
  ⟨DescentStaticWordColumn.mount base (P*2^width) (contents pages width) m room,DescentStaticWordColumn.names_mount ..⟩

theorem read {P w : ℕ} (pages : Fin P→Page) (width base : ℕ) (m : Memory w) (p : Fin P)
    (size : (pages p).bits≤width) (j : Cell (pages p).bits) :
    after pages width base m ((bank pages width base p).base+j.val)=((pages p).number j:Word w) := by
  let pitch:=2^width
  have inside : j.val<pitch:=j.isLt.trans_le (Nat.pow_le_pow_right (by decide) size)
  have bound : p.val*pitch+j.val<P*pitch:=(Nat.add_lt_add_left inside _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ p.isLt)
  have div : (p.val*pitch+j.val)/pitch=p.val:=by rw [Nat.mul_comm p.val,Nat.mul_add_div (Nat.two_pow_pos width),Nat.div_eq_of_lt inside,Nat.add_zero]
  have rem_ : (p.val*pitch+j.val)%pitch=j.val:=by rw [Nat.mul_comm p.val,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt inside]
  change DescentStaticWordColumn.image base _ m _ ((base+p.val*pitch)+j.val)=_
  rw [Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ bound]
  have number : contents pages width (p.val*pitch+j.val)=point (pages p) j.val := by
    unfold contents
    split
    next ok=>
      have index : (⟨(p.val*pitch+j.val)/2^width,ok⟩ : Fin P)=p:=Fin.ext div
      rw [index]
      exact congrArg (point (pages p)) rem_
    next bad=>
      have live : (p.val*pitch+j.val)/2^width<P:=div.trans_lt p.isLt
      exact (bad live).elim
  rw [number]
  simp [point,j.isLt]

private theorem read_point {P w : ℕ} (pages : Fin P→Page) (width base : ℕ) (m : Memory w)
    (p : Fin P) (size : (pages p).bits ≤ width) (j : ℕ) (inside : j<2^(pages p).bits) :
    after pages width base m ((bank pages width base p).base+j)=(point (pages p) j:Word w) := by
  simpa only [point,dite_eq_left inside] using read pages width base m p size ⟨j,inside⟩

theorem frame {P w : ℕ} (pages : Fin P→Page) (width base : ℕ) (m : Memory w) (j : ℕ) (away : j<base ∨ base+P*2^width≤j) :
    after pages width base m j=m j := DescentStaticWordColumn.frame _ _ _ _ _ away

def binary {x y b : ℕ} (f : Cell x→Cell y→Cell b) (M : ℕ) : Fin 2→Page :=
  ![⟨x*M,fun a=>2^(y*M)*a.val⟩,⟨(x+y)*M,fun a=>(DescentPackedZip.table (M:=M) f a).val⟩]

def joined {P : ℕ} (pages : Fin P→Page) (width base : ℕ) (i : Fin 2→Fin P) : Tables:=⟨bank pages width base (i 0),bank pages width base (i 1)⟩

theorem binary_mounted {P w x y b : ℕ} (f : Cell x→Cell y→Cell b) (M : ℕ) (pages : Fin P→Page) (size base : ℕ) (m : Memory w)
    (room : ∀j,(pages j).bits ≤ size) (i : Fin 2→Fin P) (definition_ : ∀j,pages (i j)=binary f M j) :
    Static (joined pages size base i) f M (after pages size base m) := by
  constructor
  · intro j
    have eqn : pages (i 0)=⟨x*M,fun a=>2^(y*M)*a.val⟩:=definition_ 0
    have inside : j.val<2^(pages (i 0)).bits := by rw [eqn]; exact j.isLt
    change after pages size base m ((bank pages size base (i 0)).base+j.val)=_
    rw [read_point pages size base m (i 0) (room _) j.val inside,eqn]
    simp [point,j.isLt]
  · intro j
    have eqn : pages (i 1)=⟨(x+y)*M,fun a=>(DescentPackedZip.table (M:=M) f a).val⟩:=definition_ 1
    have inside : j.val<2^(pages (i 1)).bits := by rw [eqn]; exact j.isLt
    change after pages size base m ((bank pages size base (i 1)).base+j.val)=_
    rw [read_point pages size base m (i 1) (room _) j.val inside,eqn]
    simp [point,j.isLt]

theorem bank_room {P w : ℕ} (pages : Fin P→Page) (width base out : ℕ) (p : Fin P)
    (size : (pages p).bits≤width) (separated : base+P*2^width≤out) (room : out<2^w) :
    (bank pages width base p).Fits w out := by
  have bound:=Nat.pow_le_pow_right (by decide : 0<2) size
  have early : (bank pages width base p).base+(bank pages width base p).size≤out := calc
    _ ≤ base+(p.val+1)*2^width := by
      change base+p.val*2^width+2^(pages p).bits ≤ _
      rw [Nat.succ_mul];omega
    _ ≤ base+P*2^width := Nat.add_le_add_left (Nat.mul_le_mul_right _ p.isLt) _
    _ ≤ out := separated
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (early.trans_lt room),early⟩

theorem cheap {P : ℕ} (pages : Fin P→Page) (width w base : ℕ) :
    CheapCode (mount pages width w base) := by
  have holds (n : ℕ) : CheapCode (DescentStaticWordColumn.program w base (contents pages width) n) := by
    induction n with
    | zero => apply ProtocolRAM.scan_cheap
    | succ n ih =>
      apply ProtocolRAM.cheap_seq
      · exact @ih
      · apply ProtocolRAM.scan_cheap
  exact @holds (P*2^width)

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ROM

end OAI
