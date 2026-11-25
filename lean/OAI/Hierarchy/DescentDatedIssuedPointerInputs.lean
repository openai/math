import OAI.Hierarchy.DescentDatedBooksTagPages
import OAI.Hierarchy.DescentOrdinaryPublishedRows
import OAI.Hierarchy.DescentOrdinaryBornHeader
import OAI.Hierarchy.DescentDatedRegisteredPointerRows

namespace OAI
/-! # Pointer types of the actual prior retile and the freshly mounted donor-chip pages -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentOperandStateBanks DescentPriorOperandColumns DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM DescentRawCablePanel DescentSIMDLookup DescentOrdinaryBorn
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : v.ArgumentEntry) (S : A.InputShape v)
    (floor : ℕ) (mat : A.Match v floor)
local notation "L" => A.previous
local notation "H" => A.clip.venue.hosts
local notation "G" => A.clip.venue.groups
local notation "B" => v.bornBook
local notation "ref₀" => v.reference
local notation "oldPages" => Pages (L).operands→Fin (L).blocks→Fin (L).hosts→Fin (L).groups→Cell (DescentOrdinaryPriorRetile.digits (L))
local notation "parts₀" => Fin H→Fin G→DepotRAM.Parts A.clip.venue.socket

private theorem cast_digit {a b n N : ℕ} (bits : a=b) (nodes : n=N)
    (all : a*n=b*N) (x : Cell (a*n)) (j : Fin N) :
    (ScalarOperand.take j (Fin.cast (congrArg (fun t=>2^t) all) x : Cell (b*N))).val=
      (ScalarOperand.take (j.cast nodes.symm) x).val :=by cases bits;cases nodes;rfl

private theorem born_component {b : ℕ} (wide : 2≤b) (mouth : Option Mouth) :
    TypedHeader (fun f=>component b mouth (f.castLE (by decide : 4≤7))) :=by
  obtain ⟨t,eqn⟩:=Nat.exists_eq_add_of_le wide
  have rearrange : b=t+2:=by omega
  rw [rearrange]
  exact component_header t mouth

theorem registered_born_input_typed (wide : 2≤(B).bits) (parts : parts₀) (arg : Fin v.vector.operands)
    (x : Fin (2^(ref₀).k)) (seat : Fin (ref₀).capacity) (arm : Fin 6) (h : Fin H) (g : Fin G) :
    TypedHeader (fun f=>A.bornInput v S floor mat parts (pageOf arg f) x seat arm h g) :=by
  let h₀:=h.cast S.hosts.symm
  let g₀:=g.cast S.groups.symm
  let chip:=A.nativeChips v S.toBirthShape parts h₀ g₀
  let donor:=chipDonor (B).format chip (finProdFinEquiv (x.cast mat.newBlocks.symm,seat.cast mat.newCap.symm))
  let mouth:=pointerAt (B).demand (B).grain (B).scale donor arm arg.val
  obtain ⟨p,hp⟩:=born_component wide mouth
  refine ⟨p,fun f=>?_⟩
  simp only [bornInput,rowsAt,pageOf,page,Equiv.symm_apply_apply,Fin.val_cast]
  exact hp f

theorem registered_old_input_typed (old : oldPages) (typed : BookPointers (l:=L) (fun x p=>old p x))
    (nodes : (L).nodes=(ref₀).oldNodes)
    (arg : Fin v.vector.operands) (x : Fin (2^(ref₀).k)) (h : Fin H) (g : Fin G) (j : Fin (ref₀).oldNodes) :
    TypedHeader (fun f=>ScalarOperand.take j (A.oldInput v S floor mat old (pageOf arg f) x h g)) :=by
  have products : ((L).size+2)*(L).nodes=(ref₀).bits*(L).nodes:=by
    simpa only [DescentOrdinaryPriorRetile.digits,← nodes] using S.previousBits
  have inhabited := (j.cast nodes.symm).isLt
  have bits : (L).size+2=(ref₀).bits:=Nat.eq_of_mul_eq_mul_right (by omega) products
  by_cases usable : arg.val<(L).operands
  · by_cases resident : h.val<(L).hosts
    · let p : Fin (L).operands:=⟨arg.val,usable⟩
      let prior : Fin (L).hosts:=⟨h.val,resident⟩
      let bl:=x.cast mat.oldBlocks.symm
      let grp:=g.cast S.prevGroups
      obtain ⟨word,hw⟩:=(books_typed_iff _).1 typed bl (j.cast nodes.symm) p prior grp
      refine ⟨word,fun f=>?_⟩
      have transport:=cast_digit bits nodes S.previousBits (old (pageOf p f) bl prior grp) j
      simp only [oldInput,rowsAt,pageOf,page,oldField,Equiv.symm_apply_apply,dite_eq_left usable,
        DescentOrdinaryPriorPad.extend,DescentOrdinaryHostPad.extend,Fin.cast_refl,id_eq,dite_eq_left resident]
      exact transport.trans (hw f)
    · have zero (f : Fin 4) : A.oldInput v S floor mat old (pageOf arg f) x h g=0:=by
        simp [oldInput,rowsAt,pageOf,page,usable,DescentOrdinaryPriorPad.extend,DescentOrdinaryHostPad.extend,resident]
      simpa only [zero,ScalarOperand.take_zero] using (typed_zero (width:=(ref₀).bits))
  · have zero (f : Fin 4) : A.oldInput v S floor mat old (pageOf arg f) x h g=0:=by
      simp [oldInput,rowsAt,pageOf,page,usable]
    simpa only [zero,ScalarOperand.take_zero] using (typed_zero (width:=(ref₀).bits))

/-- The selected kind digit of a retained original argument survives padding and width transport,
including a predecessor with arbitrary unobserved fields in the same operand. -/
theorem registered_old_input_tag (old : oldPages) (tags : BookTags (l:=L) (fun x p=>old p x))
    (nodes : (L).nodes=(ref₀).oldNodes) (arg : Fin v.vector.operands)
    (x : Fin (2^(ref₀).k)) (h : Fin H) (g : Fin G) (j : Fin (ref₀).oldNodes) :
    (ScalarOperand.take j (A.oldInput v S floor mat old (pageOf arg 0) x h g)).val≤2 :=by
  have products : ((L).size+2)*(L).nodes=(ref₀).bits*(L).nodes:=by
    simpa only [DescentOrdinaryPriorRetile.digits,←nodes] using S.previousBits
  have live:=(j.cast nodes.symm).isLt
  have bits : (L).size+2=(ref₀).bits:=Nat.eq_of_mul_eq_mul_right (by omega) products
  by_cases usable : arg.val<(L).operands
  · by_cases resident : h.val<(L).hosts
    · let p : Fin (L).operands:=⟨arg.val,usable⟩
      let prior : Fin (L).hosts:=⟨h.val,resident⟩
      let bl:=x.cast mat.oldBlocks.symm
      let grp:=g.cast S.prevGroups
      have oldTag:=(books_tags_iff _).1 tags bl (j.cast nodes.symm) p prior grp
      have trans:=cast_digit bits nodes S.previousBits (old (pageOf p 0) bl prior grp) j
      simp only [oldInput,rowsAt,pageOf,page,oldField,Equiv.symm_apply_apply,dite_eq_left usable,
        DescentOrdinaryPriorPad.extend,DescentOrdinaryHostPad.extend,Fin.cast_refl,id_eq,dite_eq_left resident]
      exact trans.le.trans oldTag
    · simp [oldInput,rowsAt,pageOf,page,usable,DescentOrdinaryPriorPad.extend,DescentOrdinaryHostPad.extend,
        resident,ScalarOperand.take_zero]
  · simp [oldInput,rowsAt,pageOf,page,usable,ScalarOperand.take_zero]

theorem pointer_page_cast {n n' : ℕ} (e : n=n') (arg : Fin n) (f : Fin 4) :
    (pageOf arg f).cast (congrArg (7*·) e)=pageOf (arg.cast e) f :=by cases e;rfl

theorem old_group_cell {D k K cap rows J J' a nb mb : ℕ} (groups : J=J')
    (V : ScalarOperand.Values D k K cap rows J a nb mb) (x h g) :
    (groupValues groups V).old x h g=V.old x h (g.cast groups.symm) :=by cases groups;rfl

theorem born_group_cell {D k K cap rows J J' a nb mb : ℕ} (groups : J=J')
    (V : ScalarOperand.Values D k K cap rows J a nb mb) (x seat arm h g) :
    (groupValues groups V).born x seat arm h g=V.born x seat arm h (g.cast groups.symm) :=by cases groups;rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
