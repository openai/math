import OAI.Hierarchy.DescentFreshRoleHeaderData
import OAI.Hierarchy.DescentOperandRoleNumbers
import OAI.Hierarchy.DescentPackedProfileNumber
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentPackedDonorEncoding

namespace OAI
/-! The live and padded fields on the original fresh operand inventory of a matched party. -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentSixParty DescentKernelHistory DescentOperandPhysicalInput DescentSIMDLookup
open DescentOperandStateBanks DescentRawCablePanel
open scoped Classical Fin.CommRing
noncomputable section

structure Spec where
  capacity : ℕ
  supplyOffset : ℕ
  demand : ℕ
  grain : ℕ

/-- Recover the numbered eight-field profile used by the actual matching pass. -/
def profileDigits (C code : ℕ) : Fin 8→Fin (C+2) :=
  finFunctionFinEquiv.symm (code : Fin ((C+2)^8))

theorem profile_read {C} (pr : Profile C) :
    profileDigits C ((DescentPacking.PackedMatch.LayoutSum.profileCode C) pr).val=pr.val:=by
  let key : Fin ((C+2)^8) := finFunctionFinEquiv pr.val
  have castKey : (key.val : Fin ((C+2)^8))=key := Fin.ext (Nat.mod_eq_of_lt key.isLt)
  change finFunctionFinEquiv.symm (key.val : Fin ((C+2)^8))=pr.val
  rw [castKey]
  exact finFunctionFinEquiv.symm_apply_apply pr.val

def units (B : Spec) (z prof : ℕ) : Role→ℕ
  | .original _ | .arm _=>z*B.demand/B.grain
  | .supply e=>z*((profileDigits B.capacity prof e).val+B.supplyOffset)/B.grain

structure Mouth where
  origin : Role
  target : Bool
  chunk : ℕ

def side {j} : RolePort j→Bool
  | .inl (.inl _) | .inr (.inr _) => true
  | .inl (.inr _) | .inr (.inl _) => false

def group (B : Spec) (z prof : ℕ) (j : Fin 6) (arg : Fin (Fintype.card (RolePort j))) : List Mouth :=
  let socket:=(roleIndex j).symm arg
  (List.range (units B z prof (role socket))).map (fun g=>⟨role socket,side socket,g⟩)
def inventory (B : Spec) (z prof : ℕ) (j : Fin 6) :=
  (List.finRange (Fintype.card (RolePort j))).flatMap (group B z prof j)
def mouth (B : Spec) (z prof : ℕ) (j : Fin 6) (arg : ℕ) := (inventory B z prof j)[arg]?
def Mouth.anchor (m : Mouth) : Fin 2:=match m.origin with | .original s=>s | _=>0
def Mouth.rawRole (m : Mouth) : ℕ:=match m.origin with | .original _=>0 | .arm s=>1+s.val | .supply s=>3+s.val

def field (B : Spec) (bits : ℕ) (f : Fin 7) (arg z prof : ℕ) (j : Fin 6) : Cell bits :=
  ((mouth B z prof j arg).elim 0 (fun entry=>(Pointer.cable 0 0 entry.chunk).fields ⟨0,1,1⟩ f):ℕ)

theorem field_missing (B : Spec) (bits : ℕ) (f : Fin 7) (arg z prof : ℕ) (j : Fin 6)
    (noneAt : mouth B z prof j arg=none) : field B bits f arg z prof j=0 :=by simp [field,noneAt]

theorem field_read (B : Spec) (bits : ℕ) (f : Fin 7) (arg z prof : ℕ) (j : Fin 6) (m : Mouth)
    (live : mouth B z prof j arg=some m) (room : (Pointer.cable 0 0 m.chunk).fields ⟨0,1,1⟩ f<2^bits) :
    (field B bits f arg z prof j).val=(Pointer.cable 0 0 m.chunk).fields ⟨0,1,1⟩ f:=by
  simp [field,live,Fin.val_natCast,Nat.mod_eq_of_lt room]

theorem in_group (B : Spec) (z prof : ℕ) (j : Fin 6) (a : Fin (Fintype.card (RolePort j)))
    (g : Fin (units B z prof (roleAt j a))) :
    (group B z prof j a)[g.val]?=some ⟨roleAt j a,side ((roleIndex j).symm a),g.val⟩:=by
  simp [group,roleAt]
  exact List.getElem?_range g.isLt

def actual {F : Type} [Field F] (G : PoweredGadget F) (grain : ℕ) : Spec:=⟨G.C,G.k,G.b,grain⟩

def measuredUnits (demand grain z : ℕ) (supply : Fin 8→ℕ) : Role→ℕ
  | .original _ | .arm _=>z*demand/grain
  | .supply e=>z*supply e/grain

def measuredMouth (demand grain z : ℕ) (supply : Fin 8→ℕ) (j : Fin 6) (arg : ℕ) : Option Mouth :=
  let mouths:=(List.finRange (Fintype.card (RolePort j))).flatMap (fun a=>
    let socket:=(roleIndex j).symm a
    (List.range (measuredUnits demand grain z supply (role socket))).map
      (fun t=>(⟨role socket,side socket,t⟩ : Mouth)))
  mouths[arg]?

theorem measured_actual (B : Spec) (z prof arg : ℕ) (j : Fin 6) :
    measuredMouth B.demand B.grain z (fun e=>(profileDigits B.capacity prof e).val+B.supplyOffset) j arg=
      mouth B z prof j arg :=by
  have eqn : measuredUnits B.demand B.grain z (fun e=>(profileDigits B.capacity prof e).val+B.supplyOffset)=units B z prof :=by
    funext r
    cases r <;> rfl
  simp only [measuredMouth, mouth, inventory,eqn]
  rfl

def pointerAt (demand grain z : ℕ) {loc nam width : ℕ} (d : Donor loc nam width) (j : Fin 6) (arg : ℕ) : Option Mouth :=
  if d.first then measuredMouth demand grain z (fun e=>(d.supplyUnits e).val) j arg else none

variable {l a c : ℕ}

theorem pointer_first (B : Spec) (z prof arg : ℕ) (j : Fin 6) (d : Donor l a c)
    (first : d.first=true) (supply : ∀e,(d.supplyUnits e).val=(profileDigits B.capacity prof e).val+B.supplyOffset) :
    pointerAt B.demand B.grain z d j arg=mouth B z prof j arg :=by
  simp only [pointerAt,first,ite_true,funext supply,measured_actual]

def component (bits : ℕ) (v : Option Mouth) (f : Fin 7) : Cell bits :=
  (v.elim 0 (fun m=>(Pointer.cable 0 0 m.chunk).fields ⟨0,1,1⟩ f) : ℕ)

theorem component_first (B : Spec) (z prof arg bits : ℕ) (j : Fin 6) (d : Donor l a c)
    (first : d.first=true) (supply : ∀e,(d.supplyUnits e).val=(profileDigits B.capacity prof e).val+B.supplyOffset)
    (f : Fin 7) : component bits (pointerAt B.demand B.grain z d j arg) f=field B bits f arg z prof j :=by
  simp only [pointerAt,first,ite_true,funext supply,measured_actual,component,field]

theorem component_absent (d : Donor l a c) (noneHere : d.first=false) (arg z demand grain bits : ℕ) (j : Fin 6) (f : Fin 7) :
    component bits (pointerAt demand grain z d j arg) f=0 :=by simp [pointerAt,noneHere,component]


end
end Hierarchy.DescentOrdinaryBorn

end OAI
