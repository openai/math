import OAI.Computability.IntegerMultiplication.Wave.Ordinal
import OAI.Computability.IntegerMultiplication.Atoll.Ensemble

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Strip Dims Loom Cap Atoll
variable {d:ℕ}(s:Bounds d)(u:Bool)(i:Fin d)
abbrev road : Series (Vector_ s):=bif u then top s else bot s
abbrev nose : Tape:= bif u then (window s i).p else (drawer s i).p
abbrev stem : Tape:= bif u then (window s i).q else (drawer s i).q
abbrev prefixS := layout (nose s u i)
abbrev suffixS := layout (stem s u i)
abbrev botS := Series.natural (s i)
abbrev lookS := (prefixS s u i).cart ((botS s i).cart (suffixS s u i))
def routeS : Slot (road s u) (nose s u i) (botS s i) (stem s u i):= by
  cases u
  · exact (drawer s i).cam
  exact (window s i).cam
abbrev afterS:=(suffixS s u i).count
abbrev beforeS := (prefixS s u i).count
abbrev Person := Dims.Pin (nose s u i)
abbrev Zone:=Dims.Pin (stem s u i)

abbrev offered (x: Person s u i)(v:Fin (s i))(z:Zone s u i):Vector_ s:=(routeS s u i).view.cast.symm (x,v,z)
theorem ordinal_ (x v z):
    ((road s u).index (offered s u i x v z)).val=((prefixS s u i).index x).val*((s i)*afterS s u i)+
      v.val*afterS s u i+((suffixS s u i).index z).val := by
  rw [rank_ _ _ ((routeS s u i).view)]
  change ((lookS s u i).index (x,v,z)).val=_
  rw [lookS,cart_rank,cart_rank,Series.count_cart,botS,natural_rank,Series.count_natural]
  unfold afterS;omega
theorem locS (x v z):
    offered s u i x v z i=v:=by
  let b:=routeS s u i
  have U (t:Vector_ s): b.read t=t i := by
    subst b; cases u
    · exact (drawer s i).sees t
    exact (window s i).sees t
  change b.view.cast.symm (x,v,z) i=v
  rw [← U (b.view.cast.symm (x,v,z))]; unfold Slot.read; rw [Equiv.apply_symm_apply]
theorem locO (x:Person s true i)(v : Fin (s i))(z : Zone s true i) (a):
    (routeS s true i).alter (offered s true i x v z) a=offered s true i x a z:= by
  unfold Slot.alter offered; rw [Equiv.apply_symm_apply]
theorem setO (x v z a):
    Function.update (offered s true i x v z) i a=offered s true i x a z:= by
  have g:= (window s i).gives
  change Function.update (offered s true i x v z) i a=_
  rw [← g]
  exact locO s i x v z a
theorem earlier (x:Person s true i) (v w : Fin (s i))(z y: Zone s true i) :
    ∀ j,j < i → offered s true i x v z j=offered s true i x w y j := by
  apply (window s i).prior
  change ((window s i).cam.view.cast ((window s i).cam.view.cast.symm _)).1=((window s i).cam.view.cast ((window s i).cam.view.cast.symm _)).1
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
theorem rankA (x:Vector_ s) :
    (x i).val=((road s u).index x).val/afterS s u i%(s i):=by
  let t:=(routeS s u i)
  obtain ⟨⟨y,v,z⟩,rfl⟩:=t.view.cast.symm.surjective x
  change (offered s u i y v z i).val=_
  rw [locS]
  change _=((road s u).index (offered s u i y v z)).val/afterS s u i%(s i)
  rw [ordinal_]
  let a:= afterS s u i; let b:=s i; let p:=((suffixS s u i).index z).val
  let l:= ((prefixS s u i).index y).val
  have h:p<a:=((suffixS s u i).index z).isLt
  have o:=v.isLt
  have h0:0<a:=by omega
  change v.val=(l*(b*a)+v.val*a+p)/a%b
  rw [show l*(b*a)+v.val*a+p=p+a*(v.val+b*l) by ring,Nat.add_mul_div_left _ _ h0,Nat.div_eq_of_lt h,Nat.zero_add,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt o]
variable [∀ i,NeZero (s i)]
private theorem pos(s:Bounds d)[∀ i,NeZero (s i)]:0< Cap.space s:= Finset.prod_pos (fun _i _=> Nat.pos_of_neZero _)
omit [∀ (i : Fin d), NeZero (s i)] in
theorem space_sum :
    Cap.space s=beforeS s u i*(s i*afterS s u i) := by
  have t:=(routeS s u i).view.cost
  change (road _ _).count=((prefixS s u i).cart _).count at t
  rw [Series.count_cart,Series.count_cart,Series.count_natural] at t -- botS abbreviation
  exact Cap.card s ▸ (Series.total (road s u) ▸ t)
theorem posA:0<afterS s u i := by
  have p:= pos s; rw [space_sum s u i] at p; contrapose! p; rw [show afterS s u i=0 by omega]; simp
theorem posB :0<beforeS s u i := by
  have p:= pos s; rw [space_sum s u i] at p; contrapose! p; rw [show beforeS s u i=0 by omega]; simp

omit [∀ (i : Fin d), NeZero (s i)] in
theorem baseA :afterS s false i=Cap.base s i :=
  (Dims.space _).trans (drawer s i).fee
omit [∀ (i : Fin d), NeZero (s i)] in
theorem baseB :beforeS s true i=Cap.base s i :=
  (Dims.space _).trans (window s i).fee
theorem complement :
    let d:=Cap.space s/(Cap.base s i*s i)
    afterS s true i=d ∧ beforeS s false i=d:= by
  constructor
  · rw [space_sum s true i,← baseB]
    rw [← Nat.mul_assoc,Nat.mul_div_cancel_left _ (Nat.mul_pos (posB s true i) (Nat.pos_of_neZero _))]
  · rw [space_sum s false i,← baseA,Nat.mul_comm (s i),Nat.mul_div_cancel _ (Nat.mul_pos (posA s false i) (Nat.pos_of_neZero _))]

-- math only control
abbrev Crown (x:Person s true i): Vector_ s:=
  offered s true i x (⟨0,Nat.pos_of_neZero _⟩:Fin (s i)) ((suffixS s true i).follow ⟨0,posA s true i⟩)
theorem crown_ (x:Person s true i):
    ((top s).index (Crown s i x)).val=((prefixS s true i).index x).val*(s i*afterS s true i):= by
  change ((road s true).index (offered s true i x (⟨0,Nat.pos_of_neZero _⟩:Fin (s i)) ((suffixS s true i).follow ⟨0,posA s true i⟩))).val=_
  rw [ordinal_,Series.index_follow]; simp
theorem crownV (x:Person s true i) (j):
    (Crown s i x j).val = (((prefixS s true i).index x).val*(s i*afterS s true i))/(afterS s true j)%s j := by
  rw [rankA s true j]
  change ((top s).index _).val/_%_=_
  rw [crown_]

abbrev wheel (r:Bounds d)(x) :=
  Atoll.leanValue r i (Crown s i x)
theorem wheel_r (r:Bounds d)(x p z):
    Atoll.leanValue r i (offered s true i x p z)=wheel s i r x:=
  constantV _ _ _ (earlier s i x p _ z _)

end Wave

end IntegerMultiplication
end Computability
end OAI
