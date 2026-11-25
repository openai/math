import OAI.Hierarchy.DescentTerminalRoleBirthWords
import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentResetTerminalNodeFields

namespace OAI
/-! # The installed reset program's actual per-operand lane geometry determines its scalar header -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentBundleHistory DescentLaneGates DescentKernelHistory DescentEpochTagKeys
noncomputable section
variable {X U : Type} {bw : X→ℕ} {Y n A G p R:ℕ} (units:X→ℕ)
    (multiple : ∀x,bw x=units x*p) (hp:0<p) (prg : Program Y p bw) (old:Codec U n) (label:DescentResetGates.CanonicalTag Y→U)
local notation "sh" => ofProgram units multiple hp prg

def laneFields (z : prg.Node) := List.ofFn (fun j:Fin (prg.op z).arity=>
  [(⟨((prg.op z).arg j).residue,((prg.op z).arg j).stride,((prg.op z).arg j).count units⟩:SliceCode)])

theorem reset_printed (z : prg.Node)
    (valid : DescentBundleTagKeys.Fits old A G p R (label (prg.op z).tag,(sh).sliceFields z)) :
    Printed old («fields» (rawWords (n:=n) (p:=p) (R:=R) (birth (A:=A) (G:=G) old (label (prg.op z).tag) (laneFields units prg z))))
      (label (prg.op z).tag) ((sh).sliceFields z) := by
  have actual:=congrArg Prod.snd (lane_terminal_tag (hp:=hp) (units:=units) (multiple:=multiple) (prg:=prg) z)
  rw [(sh).tag_fields hp z] at actual
  change (sh).sliceFields z=laneFields units prg z at actual
  rw [←actual]
  exact birth_printed old _ _ valid

/-- Native reset-role arithmetic when the paid rotor word and the affine references
are in separate banks. Group lengths need only the measured operand count. -/
def rotorColumns (token size:ℕ) (read:Fin G→SliceCode) : Fields A G :=
  ⟨token,size,fun _=>1,read⟩

theorem reset_column (z:prg.Node) (token size:ℕ) (read:Fin G→SliceCode)
    (role:token=(old.store (label (prg.op z).tag)).val+1) (length:size=(prg.op z).arity)
    (source:∀j:Fin G,∀ok:j.val<(prg.op z).arity,let lane:=(prg.op z).arg ⟨j.val,ok⟩
      read j=⟨lane.residue,lane.stride,lane.count units⟩)
    (valid:DescentBundleTagKeys.Fits old A G p R (label (prg.op z).tag,(sh).sliceFields z)) :
    Printed old («fields» (rawWords (n:=n) (p:=p) (R:=R) (rotorColumns (A:=A) token size read)))
      (label (prg.op z).tag) ((sh).sliceFields z) := by
  let code (j:Fin (prg.op z).arity) : SliceCode :=
    ⟨((prg.op z).arg j).residue,((prg.op z).arg j).stride,((prg.op z).arg j).count units⟩
  let xs:=laneFields units prg z
  have decode:=congrArg Prod.snd (lane_terminal_tag (hp:=hp) (units:=units) (multiple:=multiple) (prg:=prg) z)
  rw [(sh).tag_fields hp z] at decode
  change (sh).sliceFields z=xs at decode
  rw [decode] at valid ⊢
  have groupsEq:xs=(List.ofFn code).map (fun x=>[x]) := by rw [List.map_ofFn];rfl
  have singletons (l:List SliceCode) : (l.map (fun x=>[x])).flatten=l := by induction l <;> simp_all
  have flat:xs.flatten=List.ofFn code := by rw [groupsEq,singletons]
  have num:xs.length=(prg.op z).arity := by simp [groupsEq]
  refine raw_emits old _ _ _ ?_ valid
  refine ⟨role,length.trans num.symm,valid.2.1,valid.2.2.1,?_,?_⟩
  · intro j
    simp [rotorColumns,groupsEq]
  · intro j
    have lim:j.val<(prg.op z).arity:=by simpa [flat] using j.isLt
    change read _=xs.flatten[j]
    have atj : xs.flatten[j]=code ⟨j.val,lim⟩ :=
      (getElem_congr flat (rfl : j.val = j.val) j.isLt).trans (List.getElem_ofFn (by simpa using lim))
    exact (source (j.castLE valid.2.2.1) lim).trans atj.symm

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
