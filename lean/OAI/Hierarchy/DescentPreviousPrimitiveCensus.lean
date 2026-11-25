import OAI.Hierarchy.DescentPrimaryOriginalRole
import OAI.Hierarchy.DescentCalendarMatrixDigits

namespace OAI
/-! # Occupancy and values of the predecessor's complete packed primitive page -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentCompiler DescentSIMDLookup
open DescentColonies DescentGL DescentOrdinaryAtomFieldRAM DescentIssuedFallbackPanel
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ} (cap : Reached W G q ε S k i z D wire hist)
  (B : BitDescription W) (ord : Local B) (v : DescentResetRetainedSetup.Layout)
  (blocks:v.blocks=2^k) (groups:v.groups=S.groupCount i) (token : NodeOrder.All B→Cell v.bits)
  (positive:∀u,(token u).val≠0)
local notation:max "atOld" b:arg j:arg h:arg g:arg => atPhysical cap B ord (Fin.cast blocks b) j h (Fin.cast groups g)
local notation:max "name" room:arg => cap.vertex.trans (Fin.castLEEmb room)

/-- The predecessor's packed page, including its physical external actors and zero padding. -/
def previousTokens (b : Fin v.blocks) (h : Fin v.hosts) (g : Fin v.groups) : Cell v.wholeWord :=
  encode v.bits v.previousNodes (fun j=>(atOld b j h g).elim 0 token)

local notation "X" => previousTokens cap B ord v blocks groups token

theorem previous_at (b : Fin v.blocks) (h : Fin v.hosts) (g : Fin v.groups) (j : Fin v.previousNodes) :
    ScalarOperand.take j (X b h g)=(atOld b j h g).elim 0 token :=
  congrFun ((encode v.bits v.previousNodes).symm_apply_apply _) j

variable (room : Fintype.card cap.V≤v.hosts) {m : ℕ}
    (digits : Block m ≃ Fin (S.groupCount i) × Block k)
local notation:max "filled" u:arg => StarKeys.filled W.graph cap.placement.pos cap.placement.block digits u
local notation:max "count" actor:arg r:arg => ∑u : W.graph.Site,
  if (cap.placement.pos u).2=actor ∧ filled u=r then Fintype.card (B.recipe u).Node else 0
local notation:max "oldBlock" r:arg => ((digits r).2.cast blocks.symm)
local notation:max "oldGroup" r:arg => ((digits r).1.cast groups.symm)
local notation:max "host" actor:arg => ((name room) actor)

private theorem occupies_raw (actor : cap.V) (r : Block m) (u : W.graph.Site) :
    DescentPaidResidentCount.occupies cap.placement (Equiv.refl _) (name room) (host actor)
      (digits r).1 (digits r).2 u ↔ (cap.placement.pos u).2=actor ∧ filled u=r:=by
  constructor
  · rintro ⟨hv,hg,hx⟩
    refine ⟨(name room).injective hv,?_⟩
    apply digits.injective
    simpa only [StarKeys.filled,Equiv.apply_symm_apply] using Prod.ext hg hx
  · rintro ⟨hv,hr⟩
    have loc:=congrArg digits hr
    simp only [StarKeys.filled,Equiv.apply_symm_apply] at loc
    exact ⟨congrArg (name room) hv,congrArg Prod.fst loc,congrArg Prod.snd loc⟩

theorem population_bound (actor : cap.V) (r : Block m) (enough : ∀u,Fintype.card (B.recipe u).Node≤v.previousNodes) :
    count actor r≤v.previousNodes:=by
  let live u := (cap.placement.pos u).2=actor ∧ filled u=r
  by_cases has:∃u,live u
  · obtain ⟨u,h⟩:=has
    have unique x (hx:live x):x=u:=by
      have same:=congrArg digits (hx.2.trans h.2.symm)
      simp only [StarKeys.filled,Equiv.apply_symm_apply] at same
      have group : (cap.placement.pos x).1 = (cap.placement.pos u).1 := congrArg (fun pair : Fin (S.groupCount i) × Block k => pair.1) same
      have block : cap.placement.block x = cap.placement.block u := congrArg (fun pair : Fin (S.groupCount i) × Block k => pair.2) same
      exact cap.valid.coordinates (Prod.ext (Prod.ext group (hx.1.trans h.1.symm)) block)
    rw [Finset.sum_eq_single u]
    · change (if live u then Fintype.card (B.recipe u).Node else 0) ≤ v.previousNodes
      rw [ite_eq_left h]
      exact enough u
    · intro x _ away
      exact ite_eq_right (fun hx=>away (unique x hx))
    · simp
  · have none u:¬live u:=fun h=>has ⟨u,h⟩
    change (∑u : W.graph.Site,if live u then _ else 0)≤_
    simp [none]

include positive in
theorem previous_population (actor : cap.V) (r : Block m) (j : Fin v.previousNodes) :
    (ScalarOperand.take j (X (oldBlock r) (host actor) (oldGroup r))).val≠0 ↔ j.val<count actor r:=by
  rw [previous_at]
  simp only [Fin.cast_cast,Fin.cast_eq_self]
  let live u := (cap.placement.pos u).2=actor ∧ filled u=r
  have uniq {u t : W.graph.Site} (a : live u) (b : live t) : u=t:=by
    have l:=(occupies_raw cap v room digits actor r u).mpr a
    have h:=(occupies_raw cap v room digits actor r t).mpr b
    exact cap.valid.coordinates (Prod.ext (Prod.ext (l.2.1.trans h.2.1.symm)
      ((name room).injective (l.1.trans h.1.symm))) (l.2.2.trans h.2.2.symm))
  have someNode: (∃u,atPhysical cap B ord (digits r).2 j (host actor) (digits r).1=some u) ↔
      ∃u,live u ∧ j.val<Fintype.card (B.recipe u).Node:=by
    rw [atPhysical_live cap B ord (digits r).2 j (host actor) (digits r).1 (name room) (fun _=>rfl)]
    simp only [occupies_raw,live]
  have occupied : ((atPhysical cap B ord (digits r).2 j (host actor) (digits r).1).elim 0 token).val≠0 ↔
      ∃u,live u ∧ j.val<Fintype.card (B.recipe u).Node:=by
    rw [←someNode]
    cases e:atPhysical cap B ord (digits r).2 j (host actor) (digits r).1 with
    | none=>simp
    | some u=>simp [positive u]
  rw [occupied]
  by_cases has:∃u,live u
  · obtain ⟨u,h⟩:=has
    have total:count actor r=Fintype.card (B.recipe u).Node:=by
      rw [Finset.sum_eq_single u]
      · exact ite_eq_left h
      · intro v _ away
        exact ite_eq_right (fun atv=>away (uniq atv h))
      · simp
    rw [total]
    exact ⟨fun ⟨t,at_,size⟩=>uniq at_ h ▸ size,fun size=>⟨u,h,size⟩⟩
  · have blank u:¬live u:=fun yes=>has ⟨u,yes⟩
    change (∃u,live u ∧ _) ↔ _<∑u : W.graph.Site,if live u then _ else _
    simp [blank]

theorem previous_at_original (u : W.graph.Site) (a : (B.recipe u).Node)
    (j : Fin v.previousNodes) (rank : j.val=(ord u a).val) :
    ScalarOperand.take j (X (oldBlock (filled u)) (host (cap.placement.pos u).2) (oldGroup (filled u)))=token ⟨u,a⟩:=by
  rw [previous_at]
  simp only [Fin.cast_cast,Fin.cast_eq_self,StarKeys.filled,Equiv.apply_symm_apply]
  have atNode := (atPhysical_some cap B ord (cap.placement.block u) j (host (cap.placement.pos u).2) (cap.placement.pos u).1 u a).mpr ⟨rfl,rfl,rfl,rank⟩
  exact congrArg (fun x : Option (NodeOrder.All B) => x.elim 0 token) atNode

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
