import OAI.Computability.NearSquareRoot.CRTTableNativePlanReads
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchBits

/-! # The native masked XOR acting on the original padded CRT records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Native
open IntegerMultiplication Code Adic Controlled Controlled.PermutationLayout

noncomputable section

variable {A b G low n L : ℕ} {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid (maskWidth A b G low) L box)
    [∀ g, NeZero (BoxFin.modulus box g)]
    (sel : Fin b → Fin (targetOrder box.length n).length) (j : ℕ)
    (pos : 0<G)
    (fit : low+2*((b+1)*G)+(controlSlots (axisWidth box) sel j).length ≤ maskWidth A b G low)
    (π : Equiv.Perm (Fin (maskWidth A b G low)))

/-- The per-row controller of the native masked-XOR machine. -/
def ctrl (side inv : Bool) (z : Block 2 A) (q : Fin b) : Bool :=
  (rowMask (model hb sel side inv j (offset π G low b), List.ofFn (Controlled.prefixBit z)))[q.val]?.getD false

omit [∀ g, NeZero (BoxFin.modulus box g)] in
theorem ctrl_word (side inv : Bool) (z : Block 2 A) :
    rowMask (model hb sel side inv j (offset π G low b),List.ofFn (Controlled.prefixBit z)) =
      List.ofFn (ctrl hb sel j π side inv z) := by
  unfold ctrl rowMask model
  simp only [Benes.buildBatch_plan,List.map_ofFn,Function.comp_def]
  simp

def view : Block 2 (maskWidth A b G low) ≃ Packed (BoxFin.modulus box) (axisWidth box) n :=
  ((flatAddress 2 _).trans (BoxFin.recordIndex hb).symm).trans (packAddress _ _ (fitAxis hb) n)

/-- The permutation of tensor addresses that the stage is intended to execute. -/
def subbatch (which : TargetIndex box.length n → ℕ) (batch : ℕ) (side inv : Bool) :=
  Benes.batchStage which (fun r => axisWidth box (targetAxis _ _ r))
    (packedTables _ _ (fitAxis hb) n inv) (side,j) batch

variable (which : TargetIndex box.length n → ℕ) (batch : ℕ) (side inv : Bool)
    (hn : n < Nat.clog 2 box.length) (wide : ∀ q, j < axisWidth box (Chosen sel q))
    (selected : ∀ q, which (targetRank _ _ (sel q)) = batch)
    (complete : ∀ r, which r = batch → j < axisWidth box (targetAxis _ _ r) →
      ∃ q, targetRank _ _ (sel q) = r)
    (placed : ∀ q, π (targetPos pos fit q) = targets _ (total hb) sel j wide q)
    (place : ∀ i, π (controlPos fit i) = controls _ (total hb) sel j i)

include hn wide selected complete placed place in
/-- A physical position permutation, the row mask and the inverse position
permutation together implement exactly the selected CRT Beneš subbatch. -/
theorem execute (x : Block 2 (maskWidth A b G low)) :
    view (n:=n) hb (naturalStage π (ctrl hb sel j π side inv) x) =
      subbatch hb j which batch side inv (view hb x) := by
  let w := axisWidth box
  let c := ctrl hb sel j π side inv
  let y := naturalStage π c x
  have stable (g : Fin box.length) (i : Fin (w g))
      (off : ∀ q, finite hb g i ≠ targets _ (total hb) sel j wide q) :
      localWord hb y g i = localWord hb x g i := by
    rw [← originalPort hb y, ← originalPort hb x]
    exact natural_other pos fit π c x _ fun q => (placed q).symm ▸ off q
  apply Prod.ext
  · funext g
    change address hb y g.val = address hb x g.val
    apply (axisNumber (fitAxis hb g.val)).injective
    apply (wordEquiv (w g.val)).injective
    funext i
    apply stable
    intro q h
    have eq := congrArg Sigma.fst ((Benes.FieldDirectory.finitePort _ (total hb)).injective h)
    exact g.property ⟨targetRank _ _ (sel q), eq.symm⟩
  · funext r i
    rw [subbatch,Benes.batchStage_bit]
    by_cases h : which r = batch ∧ j = i.val
    · obtain ⟨q,rfl⟩ := complete r h.1 (h.2.symm ▸ i.isLt)
      rw [ite_eq_left h]
      have hri : i = ⟨j,wide q⟩ := Fin.ext h.2.symm
      have pslot : π (targetPos pos fit q) = finite hb (Chosen sel q) i := by
        rw [hri]
        exact placed q
      have bit := natural_target pos fit π c x q
      rw [pslot,originalPort hb,originalPort hb] at bit
      have mask := mask_spec hb sel j pos fit π place hn wide inv side x
      have flag := congrArg (fun l : List Bool => l[q.val]?.getD false) mask
      simp only [List.getElem?_ofFn,Fin.is_lt,↓reduceDIte,Option.getD_some] at flag
      change c _ q = flags hb sel j inv side x q at flag
      rw [flag] at bit
      exact bit
    · rw [ite_eq_right h]
      apply stable
      intro q he
      have eq := (Benes.FieldDirectory.finitePort _ (total hb)).injective he
      have hs := targetAxis_injective box.length n (congrArg Sigma.fst eq)
      have hi := congrArg (fun p : Port w => p.2.val) eq
      exact h ⟨hs ▸ selected q,hi.symm⟩


include hn wide selected complete placed place in
/-- Pulling an arbitrary record array through the physical XOR is exactly its
scatter by the selected CRT subbatch. The switch is its own inverse. -/
theorem execute_scatter {V : Type*}
    (v : Packed (BoxFin.modulus box) (axisWidth box) n → V) (x : Block 2 (maskWidth A b G low)) :
    v (view hb (naturalStage π (ctrl hb sel j π side inv) x)) =
      Benes.scatter (subbatch hb j which batch side inv) v (view hb x) := by
  rw [execute hb sel j pos fit π which batch side inv hn wide selected complete placed place x]
  change v (subbatch hb j which batch side inv (view hb x)) = v ((subbatch hb j which batch side inv).symm (view hb x))
  exact congrArg (fun e : Equiv.Perm (Packed (BoxFin.modulus box) (axisWidth box) n) => v (e (view hb x)))
    (Benes.batchStage_selfInverse which _ _ (side,j) batch).symm

end
end CRTTable.Native

end NearSquareRoot
end Computability
end OAI
