import OAI.Hierarchy.DescentPackedResetImage
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentIssuedTreeArrival

namespace OAI
/-! # Compact root book lookup from scalar geometry fields of the earlier signed slots -/

namespace Hierarchy.DescentPackedLeafSelector
open DescentSIMDLookup DescentPackedFallbackTree DescentPacking.PackedMatch.Local.Gather DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

structure Slot where
  live : Bool
  atRoot : Bool
  bad : Bool
  oppositeBad : Bool
  before : ℕ

abbrev countFields (n : ℕ) := n*5+1
def rawFields (H n : ℕ) (amount : ℕ) (x : Fin n→Slot) : Fin (countFields n)→Cell (H+2) :=
  Fin.cons (amount:Cell (H+2)) fun i=>
    let p:=finProdFinEquiv.symm i
    let t:=x p.1
    ((![t.live.toNat,t.atRoot.toNat,t.bad.toNat,t.oppositeBad.toNat,t.before] p.2:ℕ):Cell (H+2))

def pick (H : ℕ) (amount : ℕ) (t : Slot) : Option (Fin (2^H)) :=
  if t.live && t.atRoot && (t.bad || t.oppositeBad) then
    some ⟨DescentIssuedTreeArrival.table H (amount*2^H+t.before)%2^H,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  else none

def read (H : ℕ) (get : Fin 5→Cell (H+2)) : Slot :=
  ⟨get 0!=0,get 1!=0,get 2!=0,get 3!=0,(get 4).val⟩

def render (H n : ℕ) (word : Cell ((H+2)*countFields n)) : Cell (width H n) :=
  let xs:=(encode (H+2) (countFields n)).symm word
  let a:=(xs 0).val
  pack H (Nat.clog 2 a) (fun i=>pick H a (read H (fun j=>xs (finProdFinEquiv (i,j)).succ)))

theorem render_read (H n amount : ℕ) (x : Fin n→Slot) (room : amount<2^(H+2))
    (rank : ∀i,(x i).before<2^(H+2)) :
    render H n (encode (H+2) (countFields n) (rawFields H n amount x))=
      pack H (Nat.clog 2 amount) (fun i=>pick H amount (x i)) := by
  simp only [render,Equiv.symm_apply_apply,rawFields,Fin.cons_zero,Fin.val_cast_of_lt room,
    Fin.cons_succ,Equiv.symm_apply_apply]
  congr 1
  funext i
  congr 1
  generalize recovered : x i = row
  obtain ⟨a,b,c,d,e⟩ := row
  have before_lt : e < 2^(H+2) := by simpa only [recovered] using rank i
  have nz : (1:Cell (H+2))≠0 := by
    intro h
    have bound : 1<2^(H+2) := Nat.one_lt_two_pow (by omega)
    have v:=congrArg Fin.val h
    simp [] at v
  cases a <;> cases b <;> cases c <;> cases d <;> simp [read,nz,Nat.mod_eq_of_lt before_lt]

variable {H n w hosts groups M : ℕ}
def issued (tables : Fin (countFields n)→Tables) (field : Fin (countFields n)→Expr)
    (out hosts groups M w : ℕ) :=
  scan w out (hosts*chunks groups M) (assembly tables field)

/-- The gather uses disjoint short field operands for each old local slot.
The same shift and combination tables handle all repeated groups. -/
theorem gather (tables : Fin (countFields n)→Tables) (field : Fin (countFields n)→Expr) (out : ℕ)
    (bounds : Bounds (w:=w) (d:=H+2) (M:=M) tables field out) (m : Memory w)
    (header : ∀i,Static (tables i) (setField (d:=H+2) i) M m)
    (amount : Fin hosts→Fin groups→ℕ) (slot : Fin hosts→Fin groups→Fin n→Slot)
    (stored : ∀i,Source (field i) (fun v g=>rawFields H n (amount v g) (slot v g) i) M m)
    (endFit : out+hosts*chunks groups M<2^w) :
    let f:=assembly tables field
    let dst:=image out (hosts*chunks groups M) f m
    (issued tables field out hosts groups M w).Exec m dst (4+(hosts*chunks groups M)*(2*f.work+4)) ∧
      ∀p : Row hosts groups M,dst (out+(row hosts groups M p).val)=
        ((data (fun v g=>encode (H+2) (countFields n) (rawFields H n (amount v g) (slot v g))) p).val:Word w) := by
  have src:=collected tables field out bounds m header (fun v g=>rawFields H n (amount v g) (slot v g)) stored
    (List.finRange (countFields n))
  have ready:=fits tables field out bounds (List.finRange (countFields n))
  refine ⟨scan_exec _ _ _ m ready endFit,fun p=>?_⟩
  apply (ProtocolRAMGeneratedWrite.read_image _ _ _ m (row hosts groups M p)).trans
  simpa only [assembly,List.mem_finRange,ite_true] using src p

end
end Hierarchy.DescentPackedLeafSelector

end OAI
