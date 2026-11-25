import OAI.Hierarchy.DescentHostMaskCore
import OAI.Hierarchy.DescentSeedInitialRoster
import OAI.Hierarchy.DescentSeedOriginIdentity
import OAI.Hierarchy.DescentPaidSeedSites
import OAI.Hierarchy.DescentPaidCensusRead

namespace OAI
/-! # The prior host, paid atom and occupation cells of the physically named seed -/
namespace Hierarchy.DescentSeedInitialTable
open DescentSixParty DescentSixParty.SeedNamed DescentSixParty.Chronology DescentCompiler
open DescentInitialHost DescentInitialHost.PackedSeed DescentSeedRoot DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage DescentPaidResidentCount DescentColonies
open Catalyst
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
  {k cp pins wire s z H b : ℕ} (X : Approximation F cp pins)
  {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
  (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) (s:=s) c digits)
local notation "r" => o.raw
local notation "next" => placed (r)
local notation "E" => Fintype.card (Vertex X)
variable (wide : Fintype.card o.raw.V ≤ H)
local notation "host" => (r).vertex.trans (Fin.castLEEmb wide)

local notation "orig" => originalHosts X o wide
private theorem present_host (h : Fin H) : (∃v,orig v=h) ↔ ∃v,host v=h := by
  have left := DescentHostCount.prefix_live (Fintype.equivFin (Vertex X)).toEmbedding
    (o.seed.hostSize ▸ wide) h
  have right := DescentHostCount.prefix_live (r).vertex wide h
  have card : h.val<Fintype.card (Vertex X) ↔ h.val<Fintype.card (r).V :=
    Iff.of_eq (congrArg (fun n => h.val<n) o.seed.hostSize.symm)
  exact left.symm.trans (card.trans right)

theorem records_at (v : ((initialGroup X S.copies s).state c).graph.Site) :
    ((next).records (site (r) v)).length=records X v.2 := by
  refine (congrArg List.length (position (r) v).2.2).trans ?_
  refine (o.seed.counts v).trans ?_
  rcases v with ⟨j,v|ext⟩ <;> rfl

/-- Every actual seed host has a site at each group and block, including an
exterior site with an empty list of paid atoms. -/
theorem named_present (v : (r).V) (g : Fin (S.groupCount 0)) (x : Block k) :
    ∃u, (next).pos u=(g,v) ∧ (next).block u=x := by
  obtain ⟨u,pos,blk⟩:=Seed.at_site X o.seed g v x
  exact ⟨site (r) u,(position (r) u).1.trans pos,(position (r) u).2.1.trans blk⟩

private theorem emptyMask : encode 1 (2^k) (fun _=>0)=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin (2^k)=>(0:Cell 1))).val=0
  simp []

theorem previous_actors (h : Fin H) (g : Fin (S.groupCount 0)) :
    Prepare.actors (next) (Function.Embedding.refl _) host h g=actorRow X orig k h := by
  by_cases real : ∃v,host v=h
  · have row : ∃a : Fin (S.groupCount 0)×(r).V,a.1=g ∧ host a.2=h :=by
      obtain ⟨v,hit⟩:=real;exact ⟨(g,v),rfl,hit⟩
    unfold Prepare.actors Prepare.spreadField
    simp only [Function.Embedding.refl_apply,dite_eq_left row]
    unfold actorRow DescentActorRaster.actorMask
    apply congrArg (encode 1 (2^k))
    funext x
    have occupied : ∃u, (next).pos u=row.choose ∧ (next).block u=x :=
      named_present X o row.choose.2 row.choose.1 x
    simp only [DescentActorRaster.present,ite_eq_left occupied,ite_eq_left ((present_host X o wide h).2 real)]
  · have no : ¬∃a : Fin (S.groupCount 0)×(r).V,a.1=g ∧ host a.2=h :=
      fun ⟨a,_,hit⟩=>real ⟨a.2,hit⟩
    simp only [Prepare.actors,Prepare.spreadField,Function.Embedding.refl_apply,dite_eq_right no,actorRow,
      ite_eq_right (fun h'=>real ((present_host X o wide h).1 h')),emptyMask]

omit [Field F] in
private theorem missing_rack (names : Vertex X↪Fin H) (h : Fin H) (absent : ¬∃v,names v=h) :
    rack X names h=none := by
  unfold rack
  exact dite_eq_right absent

theorem previous_hub (h : Fin H) :
    (Census.hub (next) host h).val=((rack X orig h).elim 0 (fun v=>(hubFlag X.network.copyGraph v).toNat)) := by
  by_cases real : ∃v,host v=h
  · obtain ⟨v,rfl⟩:=real
    obtain ⟨u,id,tag⟩:=o.seed.hostHubs v
    have hu : orig u=host v:=Fin.ext id.symm
    have original : rack X orig (host v)=some u :=
      (congrArg (rack X orig) hu.symm).trans (rack_real X orig u)
    rw [original]
    have ex : ∃v',host v'=host v:=⟨v,rfl⟩
    have eqn:=(host).injective ex.choose_spec
    simp only [Census.hub,dite_eq_left ex,eqn,Option.elim_some]
    change (if (r).placement.hub v then (1:Cell 1) else 0).val=_
    rw [tag];cases hubFlag X.network.copyGraph u <;> rfl
  · have no:¬∃v,orig v=h:=fun x=>real ((present_host X o wide h).1 x)
    have word : Census.hub (next) host h=0 := by
      unfold Census.hub
      exact dite_eq_right real
    rw [word,missing_rack X orig h no]; rfl

theorem previous_count (h : Fin H) (g : Fin (S.groupCount 0)) (x : Block k) :
    Census.count (next) (Equiv.refl _) host b h g x=((rack X orig h).elim 0 (records X):ℕ) := by
  by_cases real : ∃v,host v=h
  · obtain ⟨v,rfl⟩:=real
    obtain ⟨u,pos,blk⟩:=Seed.at_site X o.seed g v x
    have loc:=position (r) u
    have live:=DescentPaidResidentCount.live (next) S (bounds (r)) (Equiv.refl _) host b (site (r) u)
    have origin:=o.seed.coordinates_read u
    have key : orig u.2=host v :=Fin.ext (by rw [pos] at origin;exact origin.2.symm)
    change Census.count (next) (Equiv.refl _) host b (host ((next).pos (site (r) u)).2)
      ((next).pos (site (r) u)).1 ((next).block (site (r) u))=_ at live
    rw [loc.1,pos,loc.2.1,blk,records_at X o] at live
    have original : rack X orig (host v)=some u.2 :=
      (congrArg (rack X orig) key.symm).trans (rack_real X orig u.2)
    rw [original]
    exact live
  · have no:¬∃v,orig v=h:=fun yes=>real ((present_host X o wide h).1 yes)
    have word : Census.count (next) (Equiv.refl _) host b h g x=0 := by
      unfold Census.count
      exact dite_eq_right real
    rw [word,missing_rack X orig h no]; rfl

open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
variable {M w : ℕ} (base wireBits hist quantity countBits : ℕ) (m : Memory w)
local notation "G₀" => S.groupCount 0
local notation "vals" => fields X orig k G₀ M wireBits hist quantity countBits
local notation "final" => image base H G₀ M 3 vals m

private theorem hubWord {V : Type} (w : ℕ) (u : Option V) (f : V→Bool) :
    u.elim (0:Word w) (fun v=>if f v then 1 else 0) =
      ((u.elim 0 (fun v=>(f v).toNat):ℕ):Word w) := by
  cases u with
  | none => rfl
  | some v => cases tag : f v <;> simp only [Option.elim_some,tag] <;> rfl

/-- All three nonlinear chooser inputs refer to the same post-installation
heap. The precedence of the first physical choice is preserved. -/
theorem node_inputs :
    Reads (bank base H G₀ M 3 3) (Prepare.actors (next) (Function.Embedding.refl _) host) M final ∧
    (∀v : Fin H,final ((bank base H G₀ M 3 4).base+v.val)=((Census.hub (next) host v).val:Word w)) ∧
    ∀x : Block k,Reads (bank base H G₀ M 3 5) (fun h g=>Census.count (next) (Equiv.refl _) host countBits h g x) M final := by
  constructor
  · have same : Prepare.actors (next) (Function.Embedding.refl _) host =
        (fun h (_ : Fin (S.groupCount 0))=>actorRow X orig k h) :=
      funext fun h=>funext fun g=>previous_actors X o wide h g
    rw [same]
    exact actors X orig (G:=G₀) (M:=M) base k wireBits hist quantity countBits m
  constructor
  · intro v
    exact (hubs X orig (G:=G₀) (M:=M) base k wireBits hist quantity countBits m v).trans
      ((hubWord w (rack X orig v) (hubFlag X.network.copyGraph)).trans
        (congrArg (fun n : ℕ=>(n:Word w)) (previous_hub X o wide v).symm))
  · intro x
    have same : (fun h g=>Census.count (next) (Equiv.refl _) host countBits h g x) =
        (fun h (_ : Fin (S.groupCount 0))=>(((rack X orig h).elim 0 (records X):ℕ):Cell countBits)) :=
      funext fun h=>funext fun g=>previous_count X o wide (b:=countBits) h g x
    rw [same]
    exact atoms X orig (G:=G₀) (M:=M) base k wireBits hist quantity countBits m

private theorem carryInputs {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (prior : Reached W G q ε S k 0 z 3 wire s) (eqn : world prior=W')
    (room : Fintype.card prior.V≤H) (result : Memory w)
    (a h n : ProtocolRAM.Bank)
    (given :
      Reads a (Prepare.actors (placed prior) (Function.Embedding.refl _) (prior.vertex.trans (Fin.castLEEmb room))) M result ∧
      (∀v : Fin H,result (h.base+v.val)=((Census.hub (placed prior) (prior.vertex.trans (Fin.castLEEmb room)) v).val : Word w)) ∧
      ∀x : Block k,Reads n (fun rowHost g=>Census.count (placed prior) (Equiv.refl _)
        (prior.vertex.trans (Fin.castLEEmb room)) countBits rowHost g x) M result) :
    let target := SeedNamed.transport prior eqn
    ∃fit : @Fintype.card target.V target.finite ≤ H,
      Reads a (Prepare.actors target.placement (Function.Embedding.refl _) (target.vertex.trans (Fin.castLEEmb fit))) M result ∧
      (∀v : Fin H,result (h.base+v.val)=((Census.hub target.placement (target.vertex.trans (Fin.castLEEmb fit)) v).val : Word w)) ∧
      ∀x : Block k,Reads n (fun rowHost g=>Census.count target.placement (Equiv.refl _)
        (target.vertex.trans (Fin.castLEEmb fit)) countBits rowHost g x) M result := by
  cases eqn
  exact ⟨room,given⟩

/-- The very same installed rows are the inputs of the operative named first date. -/
theorem source_inputs :
    ∃room : @Fintype.card o.source.V o.source.finite ≤ H,
      Reads (bank base H G₀ M 3 3) (Prepare.actors o.source.placement
        (Function.Embedding.refl _) (o.source.vertex.trans (Fin.castLEEmb room))) M final ∧
      (∀v : Fin H,final ((bank base H G₀ M 3 4).base+v.val)=
        ((Census.hub o.source.placement (o.source.vertex.trans (Fin.castLEEmb room)) v).val:Word w)) ∧
      ∀x : Block k,Reads (bank base H G₀ M 3 5) (fun h g=>Census.count o.source.placement (Equiv.refl _)
        (o.source.vertex.trans (Fin.castLEEmb room)) countBits h g x) M final := by
  have rows := node_inputs X o wide (M := M) base wireBits hist quantity countBits m
  have carried := carryInputs (W := (initialGroup X S.copies s).state c)
    (W' := initial_world X S.copies s (S.groupCount 0) k digits c)
    (G := G) (S := S) (q := q) (ε := ε) (k := k) (z := z) (wire := wire) (s := s)
    (H := H) (M := M) (w := w) (countBits := countBits)
    o.raw (linked_world X c digits o.seed) wide final
    (bank base H G₀ M 3 3) (bank base H G₀ M 3 4) (bank base H G₀ M 3 5) rows
  unfold Origin.source
  exact carried

end
end Hierarchy.DescentSeedInitialTable

end OAI
