import OAI.Hierarchy.DescentVenueQuantityPlanes
import OAI.Hierarchy.DescentDatedVenueSources

namespace OAI
/-! # Ordinary rank preservation through rectangular padding of original and successor hosts -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentSIMDLookup DescentVenueQuantityPlanes DescentScalarBookReshape
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {H H₀ Q R G X a m₀ m₁:ℕ}
def extend (value:Fin H₀→Fin G→Cell a)(v:Fin H)(g:Fin G):Cell a:=
  if h:v.val<H₀ then value ⟨v.val,h⟩ g else 0

def widen (le_:H₀≤H)(v:Fin (H₀*Q)):Fin (H*Q):=v.castLE (Nat.mul_le_mul_right _ le_)

theorem endpoints (le_:H₀≤H)(v:Fin (H₀*Q)):
    finProdFinEquiv.symm (widen le_ v)=((finProdFinEquiv.symm v).1.castLE le_,(finProdFinEquiv.symm v).2):=by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  exact ((congrArg Fin.val (finProdFinEquiv.apply_symm_apply v)).symm)

theorem padded_book (v:Fin (H₀*Q))(rows:Fin Q→Fin H₀→Fin (G*X)→Cell a)
    (le_:H₀≤H)(x:Fin X)(g:Fin G):
    book (fun q=>extend (H:=H) (rows q)) x (widen le_ v) g=book rows x v g:=by
  unfold book
  rw [endpoints]
  let z : Fin H₀ × Fin Q := finProdFinEquiv.symm v
  change extend (rows z.2) (z.1.castLE le_) (finProdFinEquiv (g,x)) =
    rows z.2 z.1 (finProdFinEquiv (g,x))
  unfold extend
  exact dite_eq_left z.1.isLt

theorem padded_value (rows:Fin Q→Fin H₀→Fin (G*X)→Cell a)(le_:H₀≤H)(x:Fin X)(h:Fin R)(g:Fin G):
    DescentVenueQuantityPlanes.value (⟨Q,H,R,G,X,a,m₀,m₁⟩:Dims) (widen le_) (fun q=>extend (rows q)) x h g=
    extend (fun v=>book rows x v) h g:=by
  by_cases live : h.val < H₀*Q
  · simpa only [DescentVenueQuantityPlanes.value,extend,dite_eq_left live] using
      padded_book (⟨h.val,live⟩ : Fin (H₀*Q)) rows le_ x g
  · simp only [DescentVenueQuantityPlanes.value,extend,dite_eq_right live]

variable {F P J V:Type} [Field F] [Fintype V][DecidableEq V][Fintype J][DecidableEq J]
  {d k:ℕ}{bits:P→ℕ}{W:DescentSixParty.MarkedWorld F d P bits}{Gd:DescentSixParty.PoweredGadget F}
  {q ε:ℝ}(A:DescentSixParty.GroupStage W Gd q ε J V k)(groups:J≃Fin G)(hosts:V↪Fin H₀)
theorem padded_count (le_:H₀≤H)(h:Fin H)(g:Fin G)(x:Fin (2^k)):
    Census.count A groups (hosts.trans (Fin.castLEEmb le_)) a h g x=
    extend (fun v g=>Census.count A groups hosts a v g x) h g:=by
  classical
  by_cases fit:h.val<H₀
  · let v:Fin H₀:=⟨h.val,fit⟩
    have ident (z:V):(hosts.trans (Fin.castLEEmb le_)) z=h ↔ hosts z=v:=by
      rw [Fin.ext_iff,Fin.ext_iff];rfl
    rw [show extend (fun v g=>Census.count A groups hosts a v g x) h g=Census.count A groups hosts a v g x by simp [extend,fit,v]]
    by_cases got:∃z,hosts z=v
    · let yes:∃z,(hosts.trans (Fin.castLEEmb le_)) z=h:=got.imp fun z hz=>(ident z).mpr hz
      have same:yes.choose=got.choose:=hosts.injective ((ident _).mp yes.choose_spec |>.trans got.choose_spec.symm)
      simp only [Census.count,dite_eq_left yes,dite_eq_left got,same]
    · have miss:¬∃z,(hosts.trans (Fin.castLEEmb le_)) z=h:=fun ⟨z,p⟩=>got ⟨z,(ident z).mp p⟩
      simp only [Census.count,dite_eq_right miss,dite_eq_right got]
  · have miss:¬∃z,(hosts.trans (Fin.castLEEmb le_)) z=h:=by
      rintro ⟨z,eq_⟩
      have low:((hosts.trans (Fin.castLEEmb le_)) z).val<H₀:=(hosts z).isLt
      exact fit (eq_ ▸ low)
    simp only [extend,dite_eq_right fit,Census.count,dite_eq_right miss]

end
end Hierarchy.DescentOrdinaryRasterReturn

end OAI
