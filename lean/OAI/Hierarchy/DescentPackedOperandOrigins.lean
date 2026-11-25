import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # The short identity of a captured cable or one of its ten new branches -/
namespace Hierarchy.DescentPackedOperand.Origins
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {d w H r M : ℕ}

def rawName (old : Cell d) (rawRole : Fin 11) : Cell (d+4) :=
  ⟨11*old.val+rawRole.val,by rw [pow_add];have:=old.isLt;have:=rawRole.isLt;omega⟩

theorem rawName_injective (d : ℕ) : Function.Injective (fun p : Cell d×Fin 11=>rawName p.1 p.2) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ equal
  have h:=congrArg Fin.val equal
  change 11*a.val+i.val=11*b.val+j.val at h
  have roleEq : i.val = j.val := by
    simpa only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
      using congrArg (fun n : ℕ => n % 11) h
  have serialEq : a.val = b.val := by omega
  exact Prod.ext (Fin.ext serialEq) (Fin.ext roleEq)

def roleWord (role : Fin 11) : Cell 4:=⟨role.val,by have:=role.isLt;omega⟩
def label (d : ℕ) (old : Cell d) (role : Cell 4) : Cell (d+4) :=
  if valid : role.val<11 then rawName old ⟨role.val,valid⟩ else 0

theorem label_read (old : Cell d) (role : Fin 11) : label d old (roleWord role)=rawName old role := by
  simp [label,roleWord,role.isLt]

theorem label_empty (d : ℕ) : label d 0 0=0 := by
  apply Fin.ext
  simp [label,rawName]

def column (B : Bank) := Expr.lookup B .row
def program (T : Tables) (old role : Bank) (out H r M w : ℕ) :=
  DescentPackedZip.code T (column old) (column role) out H r M w

/-- A shared lookup appends the original/arm/supply branch to the outgoing
parallel-ticket number at every actual operand lane of every host. -/
theorem execute (T : Tables) (old role : Bank) (out : ℕ)
    (fit : DescentPackedZip.Fits T (column old) (column role) d 4 M out w)
    (space : out+H*chunks r M<2^w)
    (serial : Fin H→Fin r→Cell d) (tag : Fin H→Fin r→Fin 11) :
    (program T old role out H r M w).Spec
      (fun m=>Static T (label d) M m ∧ Source (column old) serial M m ∧
        Source (column role) (fun h j=>roleWord (tag h j)) M m)
      (fun _ done=>∀p : Row H r M,done (out+(row H r M p).val)=
        ((data (fun h j=>rawName (serial h j) (tag h j)) p).val:ℕ))
      (4+54*(H*chunks r M)) ∧ CheapCode (program T old role out H r M w) := by
  obtain ⟨step,cost⟩:=DescentPackedZip.spec T (column old) (column role) out fit space
    (label d) (label_empty d) serial (fun h j=>roleWord (tag h j))
  refine ⟨step.mono (fun _ h=>h) (fun _ _ h=>by simpa only [label_read] using h.2) ?_,cost⟩
  change 4+H*chunks r M*(2*25+4)≤_
  omega

end
end Hierarchy.DescentPackedOperand.Origins

end OAI
