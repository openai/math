import OAI.Hierarchy.DescentGadgetRolePorts
import OAI.Hierarchy.DescentFiniteWordRead
import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentQuotientHistory
import OAI.Hierarchy.DescentRecordedBranch
import Mathlib.Data.List.GetD

namespace OAI
/-! # Literal powered six-party role records in the retained local histories -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentSixParty GadgetNetwork
open Computability.VPVNP Computability.VPVNP.WireTensor
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] (G : PoweredGadget F)

private def readField (cols : List (List Bool)) {j : Fin 6} (r : RolePort j) (w : ℕ) : Fin (2^w) :=
  bitsFin w (fun q=>(cols.getD ((roleIndex j r).val) []).getD q.val false)

def gadgetScalar {Z : ℕ} (tag : GadgetTag G Z) (cols : List (List Bool)) : F :=
  let z := tag.1.val
  let p := tag.2.1
  let j := tag.2.2
  if hz : 0<z then G.fixedMap z hz p j
    (fun i hi=>readField cols (.inl (.inl ⟨i,hi.symm⟩)) (z*G.b),
     fun i hi=>readField cols (.inl (.inr ⟨i,hi.symm⟩)) (z*G.b))
    (fun i hi=>readField cols (.inr (.inl ⟨i,hi.symm⟩)) (z*((p.1 i).val+G.k)),
     fun i hi=>readField cols (.inr (.inr ⟨i,hi.symm⟩)) (z*((p.1 i).val+G.k)))
  else 0

variable {I : Type} [Fintype I] {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)
variable (pick : I×Fin 2 ↪ N.Edge) (sw : I→Fin 8→ℕ)
local notation "M" => physical N pick sw

private def oldTarget (v : N.Site) (e : N.Edge) (dst : N.dst e = v) :
    (o : Option (I × Fin 2)) → selected N pick e = o → Boundary (M) (.inl v)
  | none, found => .inl ⟨.inl e,Or.inr (by simp [physical,target,found,dst])⟩
  | some t, found => .inl ⟨.inr (.inl t),Or.inr (by
      change Sum.inl (N.dst (pick t)) = Sum.inl v
      rw [selected_spec N pick found,dst])⟩

def oldBoundary (v : N.Site) : Boundary N v→Boundary (M) (.inl v)
  | .inr p => .inr ⟨p.1,congrArg Sum.inl p.property⟩
  | .inl e =>
    if s : N.src e.val=v then .inl ⟨.inl e.val,Or.inl (congrArg Sum.inl s)⟩
    else oldTarget N pick sw v e.val (e.property.resolve_left s) (selected N pick e.val) rfl

private theorem wordList_cast {a b : ℕ} (h : a=b) (w : Word b) :
    wordList (fun i=>w (Fin.cast h i))=wordList w := by subst b;rfl

theorem old_input (v : N.Site) (read : Local N pick sw (.inl v))
    (pins : (p : Attached (M) (.inl v))→Word (bits p.1)) :
    input (M) read pins∘oldBoundary N pick sw v=
      input N (siteWord N pick sw v read) (fun p=>pins ⟨p.1,congrArg Sum.inl p.property⟩) := by
  funext x
  cases x with
  | inr p => rfl
  | inl e =>
    by_cases src : N.src e.val=v
    · let index : Incident (M) (.inl v) := ⟨.inl e.val,Or.inl (congrArg Sum.inl src)⟩
      have boundary : oldBoundary N pick sw v (.inl e) = .inl index := dite_eq_left src
      have data : siteWord N pick sw v read e = read index := dite_eq_left src
      change input (M) read pins (oldBoundary N pick sw v (.inl e)) = wordList (siteWord N pick sw v read e)
      rw [boundary,data]; rfl
    · let dst := e.property.resolve_left src
      let port := oldTarget N pick sw v e.val dst
      let word : (o : Option (I × Fin 2)) → selected N pick e.val = o → Word (N.width e.val)
        | none, found => read ⟨.inl e.val,Or.inr (by simp [physical,target,found,dst])⟩
        | some t, found => fun j => read ⟨.inr (.inl t),Or.inr (by
            change Sum.inl (N.dst (pick t)) = Sum.inl v
            rw [selected_spec N pick found,dst])⟩
            (Fin.cast (congrArg N.width (selected_spec N pick found).symm) j)
      have routed (o : Option (I × Fin 2)) (found : selected N pick e.val = o) :
          input (M) read pins (port o found) = wordList (word o found) := by
        cases o with
        | none => rfl
        | some t => exact (wordList_cast (congrArg N.width (selected_spec N pick found).symm) _).symm
      have boundary : oldBoundary N pick sw v (.inl e) = port (selected N pick e.val) rfl := dite_eq_right src
      have data : siteWord N pick sw v read e = word (selected N pick e.val) rfl := by
        refine Eq.trans (dite_eq_right src) ?_
        refine congrFun (congrFun (g := word) ?_ (selected N pick e.val)) rfl
        funext o found
        cases o <;> rfl
      change input (M) read pins (oldBoundary N pick sw v (.inl e)) = wordList (siteWord N pick sw v read e)
      rw [boundary,data]
      exact routed (selected N pick e.val) rfl

def nativeRole (i : I) (j : Fin 6) : RolePort j→Boundary (M) (.inr (i,j))
  | .inl (.inl ⟨s,h⟩) => .inl ⟨.inl (pick (i,s)),Or.inr (by simp [physical,target,h])⟩
  | .inl (.inr ⟨s,h⟩) => .inl ⟨.inr (.inl (i,s)),Or.inl (by simp [physical,source,h])⟩
  | .inr (.inl ⟨s,h⟩) => .inl ⟨.inr (.inr (i,s)),Or.inl (by simp [physical,source,h])⟩
  | .inr (.inr ⟨s,h⟩) => .inl ⟨.inr (.inr (i,s)),Or.inr (by simp [physical,target,h])⟩

variable (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,N.width (pick (i,s))=z i*G.b)
variable {Z : ℕ} (room : ∀i,z i≤Z) (profile : I→Profile G.C)
local notation "S" => branchWidth G z profile

def roleRecipe (i : I) (j : Fin 6) : Recipe (GadgetTag G Z) (Boundary (physical N pick S) (.inr (i,j))) :=
  atom (⟨z i,Nat.lt_succ_of_le (room i)⟩,profile i,j) (Fintype.card (RolePort j))
    (nativeRole N pick S i j∘(roleIndex j).symm)

private theorem readWord_cast {a b : ℕ} (h : a=b) (data : Word a) :
    bitsFin b (fun q=>(wordList data).getD q.val false) =
      Fin.cast (congrArg (2^·) h) (bitsFin a data) := by
  subst b
  simp only [wordList,finiteWord_read,Fin.cast_refl,id_eq]

theorem role_read (i : I) (j : Fin 6) (read : Local N pick S (.inr (i,j)))
    (pins : (p : Attached (physical N pick S) (.inr (i,j)))→Word (bits p.1)) :
    (roleRecipe G N pick z room profile i j).value (gadgetScalar G) (input (physical N pick S) read pins)=
      G.fixedMap (z i) (hz i) (profile i) j
        (demandPorts N pick S (fun u=>z u*G.b) fit i j read) (supplyPorts N pick S i j read) := by
  rw [roleRecipe,atom_value]
  simp only [gadgetScalar,hz,dite_eq_left]
  congr 1
  · apply Prod.ext <;> funext s hs <;> simp only [demandPorts,readField,Function.comp_apply,
      finiteWord_read,Equiv.symm_apply_apply,nativeRole,input,Sum.elim_inl]
    all_goals exact readWord_cast (fit i s) _
  · apply Prod.ext <;> funext e he <;> simp only [supplyPorts,readField,Function.comp_apply,
      finiteWord_read,Equiv.symm_apply_apply,nativeRole,input,Sum.elim_inl]
    all_goals exact readWord_cast rfl _

end
end Hierarchy.DescentKernelHistory

end OAI
