import OAI.Hierarchy.DescentNodeLocalEnumeration
import OAI.Hierarchy.DescentReached

namespace OAI
/-! # Physical packed cell of every reached scalar node, including vacant rows -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist)
local notation "H" => S.hostSize age
local notation "J" => S.groupCount age
local notation "A" => cap.placement

def coordinate (u : W.graph.Site) : Fin H×(Fin J×Block k) :=
  ⟨(cap.vertex ((A).pos u).2).castLE cap.valid.host,((A).pos u).1,(A).block u⟩

theorem coordinate_injective : Function.Injective (coordinate cap):=by
  intro u v hit
  have host : ((A).pos u).2=((A).pos v).2:=cap.vertex.injective (Fin.ext (congrArg (fun p=>p.1.val) hit))
  have group : ((A).pos u).1=((A).pos v).1:=congrArg (fun p=>p.2.1) hit
  have block : (A).block u=(A).block v:=congrArg (fun p=>p.2.2) hit
  exact cap.valid.coordinates (Prod.ext (Prod.ext group host) block)

def siteAt (x : Block k) (h : Fin H) (g : Fin J) : Option W.graph.Site :=
  if occupied : ∃u,coordinate cap u=(h,g,x) then some occupied.choose else none

theorem siteAt_some (x : Block k) (h : Fin H) (g : Fin J) (u : W.graph.Site) :
    siteAt cap x h g=some u ↔ coordinate cap u=(h,g,x):=by
  unfold siteAt
  split
  next occupied =>
    constructor
    · intro yes
      obtain rfl:=Option.some.inj yes
      exact occupied.choose_spec
    · intro hit
      exact congrArg some (coordinate_injective cap (occupied.choose_spec.trans hit.symm))
  next missing =>
    constructor
    · intro present
      cases present
    · intro hit
      exact (missing ⟨u,hit⟩).elim

theorem siteAt_none (x : Block k) (h : Fin H) (g : Fin J) :
    siteAt cap x h g=none ↔ ∀u,coordinate cap u≠(h,g,x):=by
  classical
  simp [siteAt]

variable (B : BitDescription W) (localOrder : Local B)
def atomAt (u : W.graph.Site) (n : ℕ) : Option (NodeOrder.All B) :=
  if live : n<Fintype.card (B.recipe u).Node then some ⟨u,(localOrder u).symm ⟨n,live⟩⟩ else none

def whereAt {N : ℕ} (x : Block k) (n : Fin N) (h : Fin H) (g : Fin J) : Option (NodeOrder.All B) :=
  (siteAt cap x h g).bind (fun u=>atomAt B localOrder u n.val)

theorem atomAt_at (u : W.graph.Site) (a : (B.recipe u).Node) :
    atomAt B localOrder u (localOrder u a).val=some ⟨u,a⟩:=by
  simp [atomAt,(localOrder u a).isLt]

theorem whereAt_at {N : ℕ} (x : Block k) (n : Fin N) (h : Fin H) (g : Fin J)
    (u : W.graph.Site) (a : (B.recipe u).Node) (home : coordinate cap u=(h,g,x)) (rank : n.val=(localOrder u a).val) :
    whereAt cap B localOrder x n h g=some ⟨u,a⟩:=by
  rw [whereAt,(siteAt_some cap x h g u).mpr home,Option.bind_some,rank,atomAt_at]

theorem whereAt_pad {N : ℕ} (x : Block k) (n : Fin N) (h : Fin H) (g : Fin J) :
    whereAt cap B localOrder x n h g=none ↔ ∀u,coordinate cap u=(h,g,x)→Fintype.card (B.recipe u).Node≤n.val:=by
  cases hs:siteAt cap x h g with
  | none =>
    simp only [whereAt,hs,Option.bind_none,true_iff]
    intro u eqn
    have impossible:=(siteAt_none cap x h g).mp hs u eqn
    contradiction
  | some u =>
    have hu:=(siteAt_some cap x h g u).mp hs
    simp only [whereAt,hs,Option.bind_some,atomAt]
    by_cases live:n.val<Fintype.card (B.recipe u).Node
    · rw [dite_eq_left live]
      constructor
      · intro vacant
        cases vacant
      · intro bounded
        exact (live.not_ge (bounded u hu)).elim
    · simp only [dite_eq_right live,true_iff]
      intro v hv
      have same:=coordinate_injective cap (hv.trans hu.symm)
      subst v
      exact Nat.le_of_not_lt live

theorem whereAt_some {N : ℕ} (x : Block k) (n : Fin N) (h : Fin H) (g : Fin J)
    (u : W.graph.Site) (a : (B.recipe u).Node) :
    whereAt cap B localOrder x n h g=some ⟨u,a⟩ ↔ coordinate cap u=(h,g,x) ∧ n.val=(localOrder u a).val:=by
  refine ⟨?_,fun r=>whereAt_at cap B localOrder x n h g u a r.1 r.2⟩
  cases hs:siteAt cap x h g with
  | none=>simp [whereAt,hs]
  | some v=>
    simp only [whereAt,hs,Option.bind_some,atomAt]
    split
    next live =>
      intro yes
      have eqn:=Option.some.inj yes
      cases eqn
      exact ⟨(siteAt_some cap x h g _).mp hs,by simp⟩
    next =>simp

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
