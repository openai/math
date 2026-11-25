import OAI.Hierarchy.DescentTerminalRoleTableMount

namespace OAI
/-! Original tables retain their values across a frame on their purchased contiguous addresses. -/
namespace Hierarchy.DescentTerminalRoleTables
open DescentEpochTagKeys DescentTerminalCombinedRole ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section
variable {U : Type} {n A G p R N groups w : ℕ} (old : Codec U n) (slots : ℕ)
local notation "field" => fun f:Fin 6=>width n A G p R f*N*groups

theorem preserve_tables (input : Fin 6→Bank) (base : ℕ) (before later : Memory w)
    (roleRead : Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old (role field input base) before)
    (countRead : CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) slots (arity field input base) before)
    (retained : ∀a,base≤a→a<base+count field→later a=before a) :
    Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old (role field input base) later ∧
    CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) slots (arity field input base) later :=by
  have shift (f:Fin 6) (j:Fin (2^(field f))) : later (base+«prefix» field f+j.val)=before (base+«prefix» field f+j.val) := by
    apply retained <;> try omega
    have bound:«prefix» field f+j.val< marks field:=by
      simpa only [finSigmaFinEquiv_apply,«prefix»,marks] using
        (finSigmaFinEquiv (n:=fun f:Fin 6=>2^(field f)) ⟨f,j⟩).isLt
    unfold count;omega
  have r (j:Fin (menus field)):later (base+marks field+j.val)=before (base+marks field+j.val):=by
    have length:=j.isLt
    apply retained
    · omega
    · unfold count;omega
  have a (j:Fin (menus field)):later (base+marks field+menus field+j.val)=before (base+marks field+menus field+j.val):=by
    have length:=j.isLt
    apply retained
    · omega
    · unfold count;omega
  exact ⟨⟨roleRead.radix,fun f j=>(shift f j).trans (roleRead.shift f j),roleRead.slots,roleRead.key,
    fun j=>(r j).trans (roleRead.dictionary j)⟩,
    ⟨countRead.radix,fun f j=>(shift f j).trans (countRead.shift f j),countRead.capacity,countRead.key,
    fun j=>(a j).trans (countRead.table j)⟩⟩

end
end Hierarchy.DescentTerminalRoleTables

end OAI
