import OAI.Hierarchy.DescentTerminalBundleMenu
import OAI.Hierarchy.DescentPrivateSpectrum

namespace OAI
/-! # Terminal scalar rows storing only the private words actually used -/
namespace Hierarchy.DescentTerminalRestrictedRows
open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentEpochTagKeys
open DescentTerminalGraphPositions DescentTerminalRecipeRows DescentTerminalBinReaddress
open scoped Classical BigOperators
noncomputable section

variable {U P F : Type} [Field F] [Fintype P] {D : ℕ} {ew : P→ℕ} {N : Network D P ew}
    {init A G p R H atoms arity verts total W q piece bitsW S : ℕ}
    (L : Order N S p) (bit : SiteBits (U:=U) N) (s : ∀v,Shape p (bit v)) (hp : 0<p)
    (birth : ∀v,(bit v).Node ↪ ℕ) (old : Codec U init) (wp : 0<W) (qp : 0<q)
local notation "book" => DescentBundleTagKeys.codec old A G p R
local notation "rsite" => fun v=>Recipe.restricted (Shape.recipe hp (s v))
local notation "sites" => DescentTerminalBundleRows.site L rsite hp birth
def operandCount (v : N.Site) := ∑u,∑j,∑g,((s v).chunk u j g).count
omit [Fintype P] in
theorem hidden_bound (v : N.Site) : Fintype.card ((s v).recipe hp).UsedWord ≤ operandCount bit s v := by
  apply ((s v).recipe hp).used_le_slots.trans_eq
  apply Finset.sum_congr (congrArg (@Finset.univ (bit v).Node) (Subsingleton.elim _ _))
  intro u _
  exact (s v).recipe_refs hp u

variable (same : p=W*piece) (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q)
      (DescentTerminalBundleRows.site L (fun v=>((s v).recipe hp).restricted) hp birth)) ≤ total)
    (countsFit : ∀v,operandCount bit s v ≤ H) (atomsFit : ∀v,Fintype.card (bit v).Node ≤ atoms)
    (argsFit : ∀v u,(∑j,∑g,((s v).chunk u j g).count) ≤ arity)
    (sitesFit : ∀i,(DescentTerminalBundleRows.site L (fun v=>((s v).recipe hp).restricted) hp birth i).nodes ≤ verts)

def requests (a : N.Assignment) (x : Ports ew) :=
  DescentTerminalRowBooks.request sites wp qp machine
    (DescentTerminalBundleRows.payload L rsite hp birth wp qp same a x) space
    (DescentTerminalBundleRows.recipes L rsite hp birth (book).store)
    (fun i v=>(hidden_bound bit s hp (L.node i v)).trans (countsFit (L.node i v)))
    (fun i v=>atomsFit (L.node i v))
    (fun i v u=>((s (L.node i v)).recipe_refs hp u).symm ▸ argsFit (L.node i v) u)
    (fun _ _ _=>le_refl p) sitesFit

theorem graph_product (fit : ∀i,(sites i).rows q ≤ W) (small : ∀i v,(sites i).arity v ≤ q)
    (scalar : U→List (List Bool)→F) (T : N.Tables F) (valid : ReadsBits N scalar bit T)
    (born : ∀v u,old.fits ((bit v).tag u)) (num : ∀v u,(bit v).arity u ≤ A)
    (groups : ∀v u,(∑j,(s v).groups u j) ≤ G) (stride : ∀v u j g,((s v).chunk u j g).stride ≤ R)
    (a : N.Assignment) (x : Ports ew) (k : ℕ) (multiplicity : (∑v,((s v).recipe hp).deadBits)<2^k) :
    let req:=requests (A:=A) (G:=G) (R:=R) L bit s hp birth old wp qp same machine space countsFit atomsFit argsFit sitesFit a x
    (∏v,N.read T a x v)=
      (∏j : Fin k,if (∑v,((s v).recipe hp).deadBits).testBit j.val then (2:F)^(2^j.val) else 1)*
      (∏u,DescentTerminalRowBooks.menu q H atoms arity p verts (W*piece)
        (fun i xs=>bundleScalar p scalar ((book).read i) xs) (req u)) := by
  intro req
  rw [fixed_powers hp N scalar bit T valid s a x k multiplicity]
  apply congrArg (_*·)
  symm
  apply DescentTerminalBundleRows.requests_site_functions L rsite hp birth wp qp same
    (book).store _ (bundleScalar p scalar) _ _ _ machine space fit small
    (fun v=>(hidden_bound bit s hp v).trans (countsFit v)) atomsFit
    (fun v u=>((s v).recipe_refs hp u).symm ▸ argsFit v u) (fun _ _=>le_refl p) sitesFit a x
  · intro v u xs
    exact DescentBundleTagKeys.value old A G p R scalar _
      (DescentTerminalBundleMenu.tag_fits hp (s v) old u (born v u) (num v u) (groups v u) (stride v u)) xs
  · intros; rfl

end
end Hierarchy.DescentTerminalRestrictedRows

end OAI
