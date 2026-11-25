import OAI.Hierarchy.TaggedWireEndpointVisits
import OAI.Hierarchy.TaggedWirePublicSeatOrder

namespace OAI
/-! # Injecting chronological live route-boundary rows into the public turn seats -/

noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxSize 1024
namespace Hierarchy.WireTelescope
open scoped Classical

/-- Translating the ordered path coordinate recovers a unique forward
boundary, also for a zero-length path. -/
def boundaryIndex {K : ℕ} {E : Type} (a b : Fin K) (xs : List E) :
    Fin ((oriented a b xs).length+1) ↪ Fin (xs.length+1) where
  toFun j := ⟨forwardBoundary a b xs.length j.val,by
    by_cases h : a<b
    · simpa [forwardBoundary,oriented,h] using j.isLt
    · simp only [forwardBoundary,ite_eq_right h];omega⟩
  inj' := by
    intro j l eq
    have same := congrArg Fin.val eq
    have hj:=j.isLt
    have hl:=l.isLt
    by_cases h:a<b <;> simp [forwardBoundary,oriented,h] at same hj hl <;> apply Fin.ext <;> omega

end Hierarchy.WireTelescope
namespace Hierarchy.ProbeStage.CoreBoard.WordSeats
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor WireTelescope AdaptiveProbe ReportSockets
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
    (pad : Chord (siteLast h (2^W) k+1)) (fixed : Fin edges→ℕ)
    (ident : {i // 0<fixed i} ↪ Catalogue S π depth marked)

local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
abbrev GoodVisit := (i : Commodity (Fin (2^h)) (Stages h (2^W)) k) × Fin (((L).steps (.inr (.inl i))).length+1)
abbrev CatVisit := (c : Columns h (2^W) × Fin k) × Fin (((L).steps (.inr (.inr c))).length+1)
abbrev LiveVisit := ({e // 0<fixed e} × Bool) ⊕ (GoodVisit S π B pad ⊕ CatVisit S π B pad)

def goodsTurn (x : GoodVisit S π B pad) : Turn h (2^W) k := commodityTurn x.1
  (boundaryIndex ((L).goods.tail x.1) ((L).goods.head x.1) (B.ordinary x.1) x.2).val

def catTurn (x : CatVisit S π B pad) : Turn h (2^W) k := reserveTurn x.1
  (boundaryIndex ((L).reserve.tail x.1) ((L).reserve.head x.1) (B.centers x.1) x.2).val

theorem goodsTurn_injective : Function.Injective (goodsTurn S π B pad) := by
  rintro ⟨i,j⟩ ⟨l,t⟩ eq
  let ix (i) := boundaryIndex ((L).goods.tail i) ((L).goods.head i) (B.ordinary i)
  have bound (a) (b : Fin (((L).steps (.inr (.inl a))).length+1)) :
      (ix a b).val≤(commodityWalk (S:=S) π a).length := by
    simpa [Mount.ordinary] using Nat.le_of_lt_succ (ix a b).isLt
  obtain ⟨rfl,ord⟩ := commodity_eq (S:=S) π (bound i j) (bound l t) eq
  exact Sigma.ext rfl (heq_of_eq ((ix i).injective (Fin.ext ord)))

theorem catTurn_injective : Function.Injective (catTurn S π B pad) := by
  rintro ⟨c,j⟩ ⟨d,t⟩ eq
  let ix (c) := boundaryIndex ((L).reserve.tail c) ((L).reserve.head c) (B.centers c)
  have bound (a) (b : Fin (((L).steps (.inr (.inr a))).length+1)) : (ix a b).val≤2 := by
    simpa [Mount.centers,catalystWalk] using Nat.le_of_lt_succ (ix a b).isLt
  obtain ⟨rfl,ord⟩ := reserve_eq (bound c j) (bound d t) eq
  exact Sigma.ext rfl (heq_of_eq ((ix c).injective (Fin.ext ord)))

def fixedVisit : {e // 0<fixed e} × Bool ↪ Catalogue S π depth marked × Bool where
  toFun x := (ident x.1,HistoryRoles.swap S π depth marked (.inl (ident x.1)) x.2)
  inj' := by
    rintro ⟨i,b⟩ ⟨l,c⟩ eq
    obtain rfl := ident.injective (congrArg Prod.fst eq)
    have s := congrArg Prod.snd eq
    by_cases h : HistoryRoles.name (actualEnds S π depth marked (ident i)).1 <
        HistoryRoles.name (actualEnds S π depth marked (ident i)).2 <;>
      cases b <;> cases c <;> simp [HistoryRoles.swap,HistoryRoles.physicalEnds,h] at s ⊢

def liveVisit : LiveVisit S π B pad fixed ↪ All S π depth marked :=
  (fixedVisit S π depth marked fixed ident).sumMap
    { toFun := Sum.elim (goodsTurn S π B pad) (catTurn S π B pad)
      inj' := by
        rintro (i|c) (l|d) eq
        · exact congrArg Sum.inl (goodsTurn_injective S π B pad eq)
        · exact (commodity_ne_reserve _ _ _ _ eq).elim
        · exact (commodity_ne_reserve _ _ _ _ eq.symm).elim
        · exact congrArg Sum.inr (catTurn_injective S π B pad eq) }

def sourceOf : LiveVisit S π B pad fixed →
    SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k) (Columns h (2^W)×Fin k)
  | .inl (e,_) => .inl e.val
  | .inr (.inl x) => .inr (.inl x.1)
  | .inr (.inr x) => .inr (.inr x.1)

def boundaryOf (x : LiveVisit S π B pad fixed) : Fin (((L).steps (sourceOf S π B pad fixed x)).length+1) :=
  match x with
  | .inl (_,false) => 0
  | .inl (_,true) => 1
  | .inr (.inl g) => g.2
  | .inr (.inr c) => c.2

/-- The address stored for a surviving chronological row belongs to
exactly the party that enforces that boundary's equality gate. -/
theorem live_site
    (positions : ∀i : {i // 0<fixed i},filledChord B.actual pad i.val=
      HistoryRoles.sorted S π depth marked (.inl (ident i)))
    (x : LiveVisit S π B pad fixed)
    (sp : Spine (rowGraph (L).edge) ((L).original (sourceOf S π B pad fixed x)).1.1
      ((L).steps (sourceOf S π B pad fixed x)) ((L).original (sourceOf S π B pad fixed x)).1.2) :
    sp.visit (boundaryOf S π B pad fixed x) =
      HistoryRoles.name (allSite S π depth marked (liveVisit S π depth marked B pad fixed ident x)) := by
  rcases x with ⟨e,b⟩|g|c
  · have fixed_read := visit_fixed B (siteNumber h (2^W) k).injective pad e.val sp
      (boundaryOf S π B pad fixed (.inl (e,b)))
    refine fixed_read.trans ?_
    let z := actualEnds S π depth marked (ident e)
    have geometric (u v : Site h (2^W) k) (neq : HistoryRoles.name u ≠ HistoryRoles.name v) (side : Bool) :
        (portGraph _).vertex (orderedChord (HistoryRoles.name u) (HistoryRoles.name v) neq) side =
          HistoryRoles.name (Incident.choose (u,v) (if HistoryRoles.name u < HistoryRoles.name v then side else !side)) := by
      by_cases ord : HistoryRoles.name u < HistoryRoles.name v <;> cases side <;>
        simp only [orderedChord,dite_eq_left,ite_eq_left,ord,PortGraph.vertex,portGraph,Incident.choose,
          Bool.not_false,Bool.not_true] <;> rfl
    have normalized : (portGraph _).vertex (filledChord B.actual pad e.val) b =
        HistoryRoles.name (Incident.choose z (HistoryRoles.swap S π depth marked (.inl (ident e)) b)) := by
      rw [positions e]
      exact geometric z.1 z.2 (HistoryRoles.name.injective.ne (actual_distinct S π depth marked (ident e))) b
    cases b <;> exact normalized
  · exact visit_commodity B (siteNumber h (2^W) k).injective pad g.1 sp g.2
  · exact visit_reserve B (siteNumber h (2^W) k).injective pad c.1 sp c.2

theorem live_card (unique : Exclusive marked) (v : Site h (2^W) k) :
    Fintype.card (Incident.Fiber (allSite S π depth marked ∘ liveVisit S π depth marked B pad fixed ident) v)
      ≤ room (k:=k) (attempts:=attempts) S := by
  let e := liveVisit S π depth marked B pad fixed ident
  let f : Incident.Fiber (allSite S π depth marked ∘ e) v ↪ Incident.Fiber (allSite S π depth marked) v :=
    { toFun t := ⟨e t.val,t.property⟩
      inj' _ _ eq := Subtype.ext (e.injective (congrArg Subtype.val eq)) }
  exact (Fintype.card_le_of_injective _ f.injective).trans (all_card S π depth marked unique v)

end Hierarchy.ProbeStage.CoreBoard.WordSeats

end
end OAI
