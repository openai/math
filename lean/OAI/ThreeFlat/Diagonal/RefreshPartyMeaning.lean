import OAI.ThreeFlat.Diagonal.RefreshPartyAddress

namespace OAI
/-! # Meaning of the numerical refresh pin scope at every local endpoint -/

namespace ThreeFlat.Diagonal.RefreshParty

open LinearAlgebra.SpectralBooks RefreshTies Expander
open scoped Classical BigOperators
noncomputable section

variable {U : Type} [Fintype U] {m h pad pins : ℕ} (π : Equiv.Perm (Address U m))
    (δ : U×Fin m → U×Fin m) (dest : ∀ e : Address U m,δ (e.1,e.2.2)=((π e).1,(π e).2.2))
    (c : Fin m → Fin m → ℕ) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (w : Address U m → ℕ) (s : U → Arc c → ℕ) (u : U) (p : Fin m)

/-- Mathematical address within the old site or the singleton bundle half.
The bundle prefix depends on the inverse arrival map on incoming ties. -/
def demandLocation (edge : (RefreshMotif.denseGraph m).Port p) (bit : ℕ) : Location ℕ :=
  let e := addr π u edge.1.1
  let dir := edge.1.1.1
  let side := edge.1.2
  let degree := 1+h+pad
  let before := ∑ i : Fin e.2.1.val,w (e.1,Fin.castLE e.2.1.isLt.le i,e.2.2)
  ⟨if bit<w e then (if side then 2 else 1) else 0,0,
    if side then (if dir then degree else 0) else edge.1.1.2.2.val+(if dir then m else 0),
    if side then before+bit else bit⟩

def sparseLocation (edge : (ports c).Port p) (bit : ℕ) : Location ℕ :=
  let side := edge.1.2
  let localSlot := (numbering c rows (if side then DoublePorts.reverseArc c sym edge.1.1 else edge.1.1)).2
  ⟨if bit<s u edge.1.1 then 2 else 0,0,1+(if side then 1+h+pad else 0)+localSlot.val,bit⟩

/-- Old numerical half ordinals and new external/sparse half ordinals. -/
def oldHalf (q : (oldPortGraph π).Port (u,p)) : ℕ :=
  if q.1.2 then m+(π q.1.1).2.2.val else q.1.1.2.2.val

def freshHalf (q : (rawGraph δ (fun _=>ports c)).Port (u,p)) : ℕ :=
  match q.1.1 with
  | .inl _ => if q.1.2 then 1+h+pad else 0
  | .inr a => 1+(if q.1.2 then 1+h+pad else 0)+
      (numbering c rows (if q.1.2 then DoublePorts.reverseArc c sym a.2 else a.2)).2.val

def resolve (fallback : Fin pins) (old fresh : ℕ → ℕ → Fin pins) (a : Location ℕ) :=
  if a.scope=1 then old a.half a.bit else if a.scope=2 then fresh a.half a.bit else fallback

omit [Fintype U] in
theorem demandLocation_pin (fallback : Fin pins) (old fresh : ℕ → ℕ → Fin pins)
    (q : (RefreshMotif.denseGraph m).Port p) (j : Fin (w (addr π u q.1.1))) :
    resolve fallback old fresh (demandLocation (h:=h) (pad:=pad) π w u p q j.val)=
      demandPin π δ dest (fun _=>ports c) w s u p
        (fun q i=>old (oldHalf π u p q) i.val)
        (fun q i=>fresh (freshHalf (pad:=pad) δ c sym rows u p q) i.val) q j := by
  obtain ⟨⟨⟨dir,i,k⟩,side⟩,hp⟩ := q
  cases side with
  | false =>
    change i=p at hp
    subst p
    cases dir <;>
      simp [resolve,demandLocation,demandPin,portFields,oldAt,oldHalf,j.isLt,Nat.add_comm] <;> rfl
  | true =>
    change k=p at hp
    subst p
    cases dir <;>
      simp [resolve,demandLocation,demandPin,portFields,bundleAt,rawPointer,freshHalf,finSigmaFinEquiv_apply,j.isLt] <;> rfl

omit [Fintype U] in
theorem sparseLocation_pin (fallback : Fin pins) (old fresh : ℕ → ℕ → Fin pins)
    (q : (ports c).Port p) (j : Fin (s u q.1.1)) :
    resolve fallback old fresh (sparseLocation (pad:=pad) c sym rows s u p q j.val)=
      sparsePin δ (fun _=>ports c) w s u p (fun q i=>fresh (freshHalf (pad:=pad) δ c sym rows u p q) i.val) q j := by
  obtain ⟨⟨e,b⟩,eq⟩ := q
  cases b <;> simp [resolve,sparseLocation,sparsePin,sparseAt,rawPointer,freshHalf,j.isLt]


end
end ThreeFlat.Diagonal.RefreshParty

end OAI
