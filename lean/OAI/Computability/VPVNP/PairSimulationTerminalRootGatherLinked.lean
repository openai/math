import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherCode

/-!
# Installing the terminal root gather in the vertex image

The gather occupies the image's root-fields segment. Its nine temporaries
belong to that segment's private register bank. The eleven saved registers
are shared with the bootstrap, and the other three slots refer to the first
three DFS registers. The final exit enters DFS row zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather
open BurstRAM PrivateRAM

variable {S : VertexImage.Part → VertexImage.Segment} {w p r : ℕ}

private noncomputable def slotsPC {s : VertexImage.Segment} (h : s = segment) (i : Fin segment.count) : Fin s.count :=
  Fin.cast (congrArg VertexImage.Segment.count h.symm) i

private noncomputable def slotsWork {s : VertexImage.Segment} (h : s = segment) (work : Fin s.privateRegs ↪ Fin r) :
    Fin 9 ↪ Fin r := (Fin.castOrderIso (congrArg VertexImage.Segment.privateRegs h.symm)).toEquiv.toEmbedding.trans work

variable (A : VertexImage.Placement S p r) (hfield : S .rootFields = segment)

/-- Physical program counter of a gather label in the vertex image's root-fields segment,
obtained from the finite numbering of gather instructions. -/
noncomputable def imagePC (i : PC) : Fin p := A.stage .rootFields (slotsPC hfield (Fintype.equivFin PC i))

/-- Embedding of the nine gather temporaries into the host registers allocated to the
root-fields segment. -/
noncomputable def imageWork : Fin 9 ↪ Fin r := slotsWork hfield (A.localRegs .rootFields)

private noncomputable def registerIndex : Reg → VertexImage.Reg S
  | .inl i => .inr (.inr (.inr ⟨.rootFields, Fin.cast (congrArg VertexImage.Segment.privateRegs hfield.symm) i⟩))
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr i) => .inl (Fin.castAdd 6 i)

/-- Actual placement of the three register groups in the image. -/
noncomputable def imageRegs : Reg ↪ Fin r :=
  (⟨registerIndex hfield, by
    rintro (x | x | x) (y | y | y) he <;> simp [registerIndex] at he ⊢
    all_goals first | exact he | (have hv := congrArg Fin.val he; exact Fin.ext hv)⟩ :
      Reg ↪ VertexImage.Reg S).trans A.reg

@[simp] theorem imageRegs_tmp (i : Fin 9) : imageRegs A hfield (tmp i) = imageWork A hfield i := rfl

@[simp] theorem imageRegs_saved (i : Fin 11) : imageRegs A hfield (save i) = A.saved i := rfl

@[simp] theorem imageRegs_dfs (i : Fin 3) :
    imageRegs A hfield (TerminalSiteStart.work i) = A.dfs (Fin.castAdd 6 i) := rfl

theorem image_entry : imagePC A hfield (.boot 0) = A.entry .rootFields := by
  apply congrArg (A.stage .rootFields)
  apply Fin.ext
  exact (congrArg (fun s : VertexImage.Segment => s.entry.val) hfield).symm

private theorem installed_row {s : VertexImage.Segment} (h : s = segment)
    (lab : Fin s.count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Fin 11 ↪ Fin r)
    (work : Fin s.privateRegs ↪ Fin r) (done : Fin p) (i : PC) :
    (s.row lab dfs saved work done (slotsPC h (Fintype.equivFin PC i))).resize w =
      rows (fun j => lab (slotsPC h (Fintype.equivFin PC j))) (regMap dfs saved (slotsWork h work))
        ((Fin.castAddEmb 4).trans (slotsWork h work)) done i := by
  subst s
  change (rows (lab ∘ Fintype.equivFin PC) (regMap dfs saved work) ((Fin.castAddEmb 4).trans work) done
    ((Fintype.equivFin PC).symm (Fintype.equivFin PC i))).resize w = _
  rw [Equiv.symm_apply_apply,resize_rows]
  rfl

/-- Every instruction of the installed segment has the linked labels, live
registers and DFS continuation of the gather proof. -/
theorem image_linked {M : Machine w p r 11} (h : VertexImage.Contains A M) :
    Linked M (imagePC A hfield) (imageRegs A hfield) (A.dfsPC 0) := by
  intro i
  have regEq : ⇑(imageRegs A hfield) = regMap A.dfs A.saved (imageWork A hfield) := by
    funext j; rcases j with j | j | j <;> rfl
  have bitEq : bitRegs (imageRegs A hfield) = (Fin.castAddEmb 4).trans (imageWork A hfield) := by
    ext j; rfl
  rw [regEq,bitEq]
  exact (VertexImage.stage_linked A M h .rootFields (slotsPC hfield (Fintype.equivFin PC i))).trans
    (installed_row (w := w) hfield (A.stage .rootFields) A.dfs A.saved (A.localRegs .rootFields) (A.dfsPC 0) i)

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
