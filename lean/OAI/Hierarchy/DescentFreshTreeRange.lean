import OAI.Hierarchy.DescentFallbackRepeatedFields

namespace OAI
/-! # Repeated affine digits of an actual freshly installed exceptional-tree scalar -/
namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs DescentLaneGates DescentBundleHistory
open DescentSIMDLookup DescentDenseHostOrder DescentResetLocalRoster DescentFallbackItemSelect
open DescentRetainedRangeDigits DescentResetPublicOperandBook
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {I K R W : Type} [Fintype I] [Fintype K] [Fintype R] [Fintype W]
variable (D : ℕ) (contact : I→K) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→K→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
variable {n h depth ord : ℕ} (board : NonlinearExpanders.Graph n h) (C : DescentResetPublicOperandBook.Config)
variable (p : ℕ) (hp : 0<p) (s : Bool) (w : W) (book : LinkId owner s w ↪ Node depth) (key : I↪Fin ord)
local notation "wt" => fun _ : I=>C.batches*p
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "prog" => program D contact input site owner align C.batches p hp s w book key
local notation "F" => C.oldConfig

omit [Fintype R] in
/-- Both original public slots and private tree cables sum whole old items. -/
theorem word_multiple (q : Physical.Site depth) (a : Boundary (N) q) :
    boundaryWidth (N) q a=boundaryWidth (N) q a/p*p :=by
  symm
  apply Nat.div_mul_cancel
  rcases a with e|⟨u,_⟩
  · apply Finset.dvd_sum
    intro i _
    exact ⟨C.batches,Nat.mul_comm _ _⟩
  · rcases u with e|(e|pin)
    all_goals
      apply Finset.dvd_sum
      intro i _
      exact ⟨C.batches,Nat.mul_comm _ _⟩

omit [Fintype R] in
theorem fresh_range (Y : ℕ) (q : Physical.Site depth) (u : (prog Y q).Node)
    (multiple : ∀a,boundaryWidth (N) q a=(boundaryWidth (N) q a/p)*p)
    (x : C.Data n) (arg : Fin C.args) (node : Fin C.nodes)
    (root : code C.residual×Option (Fin (2^n))) (ds : List Bool)
    (sh : ↥(roster board C.residual C.maxDepth))
    (active : ((F).header (C.basic x) 0).val≠0)
    (located : ((F).header (C.basic x) 2).val=(localRank board C.residual C.maxDepth sh).val)
    (tag : sh.val=.fall s ((),(root.1.val,root.2)) ds)
    (room : DescentFallbackPeriod.rootCell C.residual n root<DescentFallbackShapeTable.rows C.residual (2^n))
    (positive : 0<C.batches) (j : Fin (F).count) (leaf : ℕ)
    (f : Fin 3) (bits : ℕ) :
    let id:=(⟨_,room⟩ : Fin (DescentFallbackShapeTable.rows C.residual (2^n)))
    let amount:=DescentFallbackPeriod.score ((F).packet (C.basic x)) (id,0,id)
    let items:=(F).rowsAt (C.basic x) s root id amount
    let cell:=rows C.maxDepth ds items
    let advance:=if ds.length=min C.maxDepth (Nat.clog 2 amount) then cell else rows C.maxDepth (DescentFallbackOperandBranch.Config.childPath C.maxDepth ds leaf) items
    select items cell (node.val/C.batches)=some j → (items j).leaf=some leaf →
    measuredWord (F) p (((prog Y q).op u).arg (0 : Fin 2)) items cell j node.val →
    measuredWord (F) p (((prog Y q).op u).arg (1 : Fin 2)) items advance j node.val →
    C.column board bits (some (page f)) (finProdFinEquiv (arg,node)) x=
      ((atSlot (ofProgram (fun a=>boundaryWidth (N) q a/p) multiple hp (prog Y q)) u arg.val f : ℕ) : Cell bits) :=by
  dsimp only
  intro picked landed left right
  rw [C.column_range board,C.tree_dispatch board node.val arg.val x s root ds sh active located tag room]
  apply congrArg (fun t : ℕ=>(t : Cell bits))
  exact DescentFallbackOperandBranch.Config.make_atSlot (F) s _ _ ds root _ node.val j leaf positive picked landed
    hp multiple (prog Y q) u _ _ rfl
    (stride_one D contact input site owner align C.batches p hp s w book key Y q u (0 : Fin 2))
    (stride_one D contact input site owner align C.batches p hp s w book key Y q u (1 : Fin 2)) left right arg.val f

end
end Hierarchy.DescentTreeLaneProgram

end OAI
