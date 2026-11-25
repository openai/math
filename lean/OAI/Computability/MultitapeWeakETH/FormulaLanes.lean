import OAI.Computability.MultitapeWeakETH.RoutedFormula
import OAI.Computability.MultitapeWeakETH.SwitchContraction

/-! # Formula validation at the input and output banks of the packed lanes -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT NearSquareRoot.Benes VPVNP VPVNP.Compression
open PackedSwitches Finset
open scoped Classical
noncomputable section

variable {n g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r))
    (width : SAT.WidthAtMost 3 F)

def siteLane (v : Site F) : BitWord g := lane (siteCode F fit v)

theorem end_lane (e : End F) :
    lane (g:=g) (l:=r+2) (addresses F fit width e) = siteLane F fit (host F e) := by
  funext i
  apply congrArg finTwoEquiv.symm
  exact address_prefix F fit width e (i.castAdd r)

def portOffset (e : End F) : Fin (2^(r+2)) := (packed g (r+2) (addresses F fit width e)).2

theorem address_offset (e : End F) :
    addressAt (siteLane F fit (host F e)) (portOffset F fit width e) = addresses F fit width e := by
  rw [← end_lane F fit width e]; exact (packed g (r+2)).symm_apply_apply _

/-- Test the source clamp on the current lane before evaluating its local
formula factors. Each site uses just the offsets of its incident ports. -/
def validator (R : Type) [CommSemiring R] : Validator g (r+2) R :=
  fun v input output =>
    let source := Function.Embedding.inl.trans (addresses F fit width)
    if ∀ s, addressAt (g:=g) (l:=r+2) v s ∉ Set.range source → input s = false then
      ∏ u, if siteLane F fit u = v then
        tables F R u (fun e _ => input (portOffset F fit width (.inl e)),
          fun e _ => output (portOffset F fit width (.inr e))) else 1
    else 0

theorem validator_product (R : Type) [CommSemiring R] (x y : Word (g+(r+2)) → Bool) :
    (∏ v, validator F fit width R v (localBank x v) (localBank y v)) =
      if Padded F (Function.Embedding.inl.trans (addresses F fit width)) x then
        ∏ u, tables F R u (routedHalf F (addresses F fit width) x y u) else 0 := by
  let source := Function.Embedding.inl.trans (addresses F fit width)
  let ok (v : BitWord g) := ∀ s, addressAt (g:=g) (l:=r+2) v s ∉ Set.range source → localBank x v s = false
  have allOk : (∀ v, ok v) ↔ Padded F source x := by
    constructor
    · intro h i hi
      have heq : addressAt (g:=g) (l:=r+2) (lane (g:=g) (l:=r+2) i) (packed g (r+2) i).2 = i := (packed g (r+2)).symm_apply_apply _
      simpa only [localBank,heq] using h (lane (g:=g) (l:=r+2) i) (packed g (r+2) i).2 (heq.symm ▸ hi)
    · exact fun h v s => h _
  by_cases good : Padded F source x
  · rw [ite_eq_left good]
    have goodLane := allOk.mpr good
    let entry (v : BitWord g) (u : Site F) := tables F R u
      (fun e _ => localBank x v (portOffset F fit width (.inl e)),
       fun e _ => localBank y v (portOffset F fit width (.inr e)))
    trans ∏ v, ∏ u, if siteLane F fit u = v then entry v u else 1
    · apply prod_congr rfl
      intro v _
      exact ite_eq_left (goodLane v)
    rw [prod_comm]
    apply prod_congr rfl
    intro u _
    rw [prod_eq_single (siteLane F fit u)]
    · simp only [ite_true]
      apply congrArg (tables F R u)
      apply Prod.ext
      · funext e he
        change x (addressAt (siteLane F fit u) (portOffset F fit width (.inl e))) = _
        exact congrArg x (he.symm ▸ address_offset F fit width (.inl e))
      · funext e he
        change y (addressAt (siteLane F fit u) (portOffset F fit width (.inr e))) = _
        exact congrArg y (he.symm ▸ address_offset F fit width (.inr e))
    · intro v _ ne; simp [Ne.symm ne]
    · simp
  · rw [ite_eq_right good]
    obtain ⟨v,hv⟩ := not_forall.mp (fun h => good (allOk.mp h))
    exact prod_eq_zero (mem_univ v) (ite_eq_right hv)

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
