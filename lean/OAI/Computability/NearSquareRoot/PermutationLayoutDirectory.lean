import OAI.Computability.NearSquareRoot.PermutationLayoutHeader
import OAI.Computability.NearSquareRoot.PermutationLayoutCompile
import OAI.Computability.NearSquareRoot.CRTPositionCompiledAction

/-! # Actual forward, inverse, and prefix lookup tables for a physical batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Code Reflections

/-- Subtract the position of the first prefix bit from each inverse lookup.
Only inputs prescribed to lie inside the prefix are subsequently read. -/
def relative (x : Tally × Table) : Table := polyPush (fun p : Tally × Tally => (cutLists p).2) x

@[fun_prop] theorem relative_poly : Poly relative :=
  Poly.push [] [] (easy_cut (Easy.identity (X := Tally × Tally))).sndCompose.poly

/-- The preparation and restoration address permutations and the directory of
local prefix offsets indexed by natural address. -/
def directory (x : Tally × Inputs) : (Table × Table) × Table :=
  let out := compile (x.1,assigned x.2)
  (out, relative (prefixStart x.2,out.2))

theorem directory_poly : Poly directory := by
  let X := Tally × Inputs
  have pre : Poly (fun x : X => compile (x.1,assigned x.2)) :=
    ((Easy.fst (X := Tally) (Y := Inputs)).poly.pair (Easy.snd.poly.compose assigned_poly)).compose compile_poly
  exact pre.pair (((Easy.snd.poly.compose prefixStart_poly).pair pre.sndCompose).compose relative_poly)

variable {k b c G low : ℕ} {targets : Fin b → Fin k} {controls : Fin c → Fin k}

def offset (p : Equiv.Perm (Fin k)) (G low b : ℕ) (j : Fin k) :=
  (p.symm j).val - (low+2*((b+1)*G))

theorem directory_spec (ht : Function.Injective targets) (hc : Function.Injective controls)
    (hd : ∀ q j, targets q ≠ controls j) (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) :
    ∃ p : Equiv.Perm (Fin k),
      (∀ q, p (targetPos pos fit q) = targets q) ∧
      (∀ j, p (controlPos fit j) = controls j) ∧
      (∀ j, offset p G low b (controls j) = j.val) ∧
      directory (tally k, inputs targets controls G low) =
        ((table p,table p.symm),List.ofFn fun j => tally (offset p G low b j)) := by
  let cmds := pairs targets controls pos fit
  obtain ⟨p,hp,tableEq⟩ := compile_valid cmds (dest_nodup _ _ _ _) (src_nodup ht hc hd pos fit)
  have targ (q : Fin b) : p (targetPos pos fit q) = targets q :=
    hp (targetPos pos fit q,targets q) (by simp [cmds,pairs]; exact Or.inl ⟨q,rfl,rfl⟩)
  have ctr (j : Fin c) : p (controlPos fit j) = controls j :=
    hp (controlPos fit j,controls j) (by simp [cmds,pairs]; exact Or.inr ⟨j,rfl,rfl⟩)
  refine ⟨p,targ,ctr,?_,?_⟩
  · intro j
    rw [offset,← ctr j,Equiv.symm_apply_apply]
    simp [controlPos, controlOffset]
  · change (compile (tally k,assigned (inputs targets controls G low)),_) = _
    rw [assigned_inputs targets controls pos fit]
    change (compile (tally k,cmds.map ReserveProgram.endpointPair), _) = _
    rw [tableEq]
    congr 1
    simp only [relative,polyPush,table,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    apply List.ext_getElem
    · simp [cutLists,offset,prefixStart_inputs]
    · intros; rfl

end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
