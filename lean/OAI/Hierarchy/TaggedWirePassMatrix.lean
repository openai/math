import OAI.Hierarchy.TaggedWireSiteMatrix

namespace OAI
/-! # The explicit sites of a simultaneous physical repair and its pass-through stock -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators

variable {S n : ℕ} {F : Type*} [Field F] {J : Fin n→Type} [∀i,Fintype (J i)]
variable {demand : Fin n→Widths S} {installed : ∀i,J i→Widths S}
variable (M : ∀i j,SiteMatrix (State (demand i)) (State (installed i j)) F)

def tiles (c : ∀i,J i) := tiledTable (fun i=>M i (c i))

theorem tile_sum (tileLaw : ∀i x,(raw F (demand i)).coeff x=
    ∑j,SiteMatrix.act (M i j) (raw F (installed i j)).coeff x)
    (x : ∀s,State (∑i,demand i) s) : (raw F (∑i,demand i)).coeff x =
      ∑ c : ∀i,J i,SiteMatrix.act (tiles M c) (raw F (∑i,installed i (c i))).coeff x := by
  exact raw_tiled_sum demand installed (fun i j=>SiteMatrix.act (M i j) (raw F (installed i j)).coeff) M
    (fun i=>funext fun v=>(tileLaw i v).trans
      (Finset.sum_apply v Finset.univ (fun j=>SiteMatrix.act (M i j) (raw F (installed i j)).coeff)).symm)
    (fun _ _ _=>rfl) x

/-- The unused stock sees literal equality checks; the selected coordinates see
the product of the actual packet site matrices after their local half-port reads. -/
def matrix (rest : Widths S) (c : ∀i,J i) :=
  productTable (SiteMatrix.identity (F:=F) (State rest)) (tiles M c)

theorem action (tileLaw : ∀i x,(raw F (demand i)).coeff x=
    ∑j,SiteMatrix.act (M i j) (raw F (installed i j)).coeff x)
    (rest : Widths S) (x : ∀s,State (rest+∑i,demand i) s) :
    (raw F (rest+∑i,demand i)).coeff x=∑c : ∀i,J i,SiteMatrix.act (matrix M rest c)
      (raw F (rest+∑i,installed i (c i))).coeff x := by
  let l := fun i=>(splitPortState rest (∑i,demand i) i (x i)).1
  let r := fun i=>(splitPortState rest (∑i,demand i) i (x i)).2
  rw [raw_add_coeff]
  change (raw F rest).coeff l*(raw F (∑i,demand i)).coeff r=_
  rw [tile_sum M tileLaw r,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [←SiteMatrix.act_id (raw F rest).coeff l]
  exact productTable_action (SiteMatrix.identity (State rest)) (tiles M c) x

/-- These two width equalities come from the native per-resource debit/credit
and reserve ledgers. Transport only changes the proofs of the Fin bounds. -/
def actual {before : Widths S} {after : (∀i,J i)→Widths S} (rest : Widths S)
    (entry : rest+∑i,demand i=before)
    (out : ∀c,rest+∑i,installed i (c i)=after c) (c : ∀i,J i) :
    SiteMatrix (State before) (State (after c)) F :=
  entry ▸ (out c) ▸ matrix M rest c

theorem actual_action {before : Widths S} {after : (∀i,J i)→Widths S} (rest : Widths S)
    (entry : rest+∑i,demand i=before)
    (out : ∀c,rest+∑i,installed i (c i)=after c)
    (tileLaw : ∀i x,(raw F (demand i)).coeff x=
      ∑j,SiteMatrix.act (M i j) (raw F (installed i j)).coeff x)
    (x : ∀s,State before s) : (raw F before).coeff x=
      ∑ c : ∀i,J i,SiteMatrix.act (actual M rest entry out c) (raw F (after c)).coeff x := by
  subst before
  have eqn : (fun c=>(rest+∑i,installed i (c i)))=after := funext out
  subst after
  exact action M tileLaw rest x

end Hierarchy.WireTelescope.PassMatrix

end
end OAI
