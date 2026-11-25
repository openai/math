import OAI.Hierarchy.DescentSeedCableRanks
import OAI.Hierarchy.DescentSeedSignedStencil
import OAI.Hierarchy.DescentSeedCableMeaning

namespace OAI
/-! Complete initial signed cable bank, including both occurrences of a loop and all ghost slots. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentSixParty DescentColonies DescentSharedCableNames
open Computability.BorderVNP.Crossing Catalyst CorrectionBatch
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k n R s r : ℕ}
    (X : Approximation F k n) (G : PoweredGadget F) (digits : Fin R ≃ J×Block r)
    (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c
local notation "N" => X.network.copyGraph
variable {ε : ℝ} (q : ℝ) (w hist z : ℕ) (field : 0<r) (hq : 0<q)
    (hw : 0<w) (hz : 0<z) (units : s=z*G.b) (room : 3*(w*s)+hist≤256*(w*s))
    (retained : (q*hist)*((R*Fintype.card X.network.copyGraph.Site:ℕ):ℝ)≤ε)
    (root : ((Fintype.card J*Fintype.card (Vertex X):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*((w*s*256:ℕ):ℝ)))≤ε)
local notation "T" => source_group X G digits c q w hist z field hq hw hz units room retained root
local notation "U" => initial_units X G digits c q w hist z field hq hw hz units room retained root
local notation "CH" => chart X G digits c T U (initial_home X G digits c q w hist z field hq hw hz units room retained root)
local notation "B" => Stage.source T (native X c)
local notation "host" => vertexChart X digits

def Fiber (v : Vertex X) := Σ b : Bool,{e : Cable X // atEnd X b e=v}

def actualPort (j : Fin R) (v : Vertex X) (f : Fiber X v) :
    (T).CellPorts (host (j,v)).1.1 (host (j,v)).1.2 (host (j,v)).2 := by
  rcases f with ⟨b,e,h⟩
  cases b with
  | false=>exact .inl ⟨⟨⟨j,e⟩,Prod.ext rfl h,rfl⟩,one X G c T U j e⟩
  | true=>exact .inr ⟨⟨⟨j,e⟩,Prod.ext rfl h,rfl⟩,one X G c T U j e⟩

local notation "port" => actualPort X G digits c q w hist z field hq hw hz units room retained root

theorem every (j : Fin R) (v : Vertex X) : Function.Surjective (port j v) := by
  rintro (⟨⟨⟨a,e⟩,ep⟩,g⟩|⟨⟨⟨a,e⟩,ep⟩,g⟩)
  · have whereAt : host (a,source N e)=host (j,v):=Prod.ext ep.1 ep.2
    obtain ⟨rfl,eqn⟩:=Prod.mk.inj ((host).injective whereAt)
    have zero : g=one X G c T U a e := by apply Fin.ext; have := g.isLt.trans_eq (U ⟨a,e⟩); change g.val=0; omega
    subst g;exact ⟨⟨false,e,eqn⟩,rfl⟩
  · have whereAt : host (a,target N e)=host (j,v):=Prod.ext ep.1 ep.2
    obtain ⟨rfl,eqn⟩:=Prod.mk.inj ((host).injective whereAt)
    have zero : g=one X G c T U a e := by apply Fin.ext; have := g.isLt.trans_eq (U ⟨a,e⟩); change g.val=0; omega
    subst g;exact ⟨⟨true,e,eqn⟩,rfl⟩

variable (S : DescentCompiler.AtomSchedule) {i : ℕ} (ready : (source_group X G digits c q w hist z field hq hw hz units room retained root).StateBounds S i) (group : J↪ℕ)
local notation "names" => initialNames X (r:=r) group
local notation "fit" => Stage.measured T (native X c) S ready

private theorem grain (j : Fin R) (v : Vertex X) (f : Fiber X v) :
    (Stage.ofPort T (native X c) (host (j,v)) (port j v f)).val=(CH).wire (j,f.2.val) := by
  rcases f with ⟨b,e,h⟩;cases b <;> rfl

private theorem sign (j : Fin R) (v : Vertex X) (f : Fiber X v) :
    Stage.signedBit T (host (j,v)) (port j v f)=finTwoEquiv.symm f.1 := by
  rcases f with ⟨b,e,h⟩;cases b <;> rfl

def atSlot (v : Vertex X) (f : Fiber X v) : Fin (2*256) :=
  finProdFinEquiv (finTwoEquiv.symm f.1,
    (⟨position X v f.2.val,(position_short X _ _ (Eq.mp (congrArg (fun t => present X t f.2.val) f.2.property) (belongs X f.1 f.2.val))).trans (by decide)⟩:Fin 256))

theorem actual_slot (j : Fin R) (v : Vertex X) (f : Fiber X v) :
    Stage.signed T (native X c) S ready (host (j,v)).1 (host (j,v)).2 (port j v f)=atSlot X v f := by
  let a:=Stage.ofPort T (native X c) (host (j,v)) (port j v f)
  have eqn : a.val=(CH).wire (j,f.2.val):=grain X G digits c q w hist z field hq hw hz units room retained root j v f
  change finProdFinEquiv (Stage.signedBit T (host (j,v)) _,(B).position fit _ a)=_
  rw [sign X G digits c q w hist z field hq hw hz units room retained root]
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · rfl
  apply Fin.ext
  obtain ⟨wire,mem⟩:=a
  change wire=(CH).wire _ at eqn
  subst wire
  exact (CH).position_eq fit j v f.2.val mem

private theorem marked (j : Fin R) (e : Cable X) : decide ((⟨j,e⟩:(W).graph.Edge)∈(W).core)=paid X e := by
  have entry (a : (markedInput X).graph.Edge) :
      (⟨j,a⟩ : (W).graph.Edge) ∈ (W).core ↔ a ∈ (markedInput X).core := by
    change (⟨j,a⟩ : Σ _ : Fin R, (markedInput X).graph.Edge) ∈
      Finset.univ.sigma (fun _ : Fin R => (markedInput X).core) ↔ a ∈ (markedInput X).core
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
  calc
    _ = decide (e ∈ (markedInput X).core) := Bool.decide_congr (entry e)
    _ = _ := by
      cases e with
      | inl e =>
        apply decide_eq_true
        exact Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩
      | inr p =>
        apply decide_eq_false
        intro h
        obtain ⟨e, _, eqn⟩ := Finset.mem_map.mp h
        cases eqn

set_option maxHeartbeats 500000 in
theorem actual_record (j : Fin R) (v : Vertex X) (f : Fiber X v) :
    Stage.live T (native X c) S ready names (host (j,v)) (port j v f)=record X f.1 f.2.val := by
  let a:=Stage.ofPort T (native X c) (host (j,v)) (port j v f)
  let e:=f.2.val
  have eqn : a.val=(CH).wire (j,e):=grain X G digits c q w hist z field hq hw hz units room retained root j v f
  have belongsHere : present X v e:=Eq.mp (congrArg (fun t => present X t e) f.2.property) (belongs X f.1 e)
  let src:=incident X G digits c T U (initial_home X G digits c q w hist z field hq hw hz units room retained root)
  have agrees : a=src j v ⟨e,belongsHere⟩:=Subtype.ext eqn
  have nb:=slot X G digits c T U (initial_home X G digits c q w hist z field hq hw hz units room retained root)
    names (initialNames_lt X digits group) (initial_near X G digits c q w hist z field hq hw hz units room retained root) j v ⟨e,belongsHere⟩
  have atSource : (Stage.outgoing T (native X c) S ready ⟨⟨j,e⟩,Nat.zero_lt_one.trans_eq (U ⟨j,e⟩).symm⟩).val=position X (source N e) e := by
    apply (CH).position_eq fit j (source N e) e
  rcases f with ⟨b,y,eqy⟩
  subst v
  cases b with
  | false =>
    have nbh : (Stage.live T (native X c) S ready names _ (port j _ ⟨false,y,rfl⟩)).neighbor.val=seedPeer X (source N y) y :=
      (congrArg (fun z=>(Stage.neighbors T (native X c) names).slot _ z |>.val) agrees).trans nb
    apply record_ext
    · exact Fin.ext nbh
    · exact Fin.ext ((CH).serial j (source N y) y)
    · exact Fin.ext atSource
    · rfl
    · rfl
    · simp [Stage.live, Stage.isMarkedOut, actualPort, one, record]
      refine Eq.trans ?_ (marked X c j y)
      exact Bool.decide_congr Iff.rfl
  | true =>
    have nbh : (Stage.live T (native X c) S ready names _ (port j _ ⟨true,y,rfl⟩)).neighbor.val=seedPeer X (target N y) y :=
      (congrArg (fun z=>(Stage.neighbors T (native X c) names).slot _ z |>.val) agrees).trans nb
    apply record_ext
    · exact Fin.ext nbh
    · exact Fin.ext ((CH).serial j (target N y) y)
    · exact Fin.ext atSource
    · rfl
    · rfl
    · rfl

theorem signed_at (j : Fin R) (v : Vertex X) (s : Fin (2*256)) :
    Stage.signedPanel T (native X c) S ready names (host (j,v)) s=panelAt X v s := by
  let ar:=Stage.signed T (native X c) S ready (host (j,v)).1 (host (j,v)).2
  by_cases hit : ∃p,ar p=s
  · obtain ⟨p,rfl⟩:=hit
    obtain ⟨f,rfl⟩:=(every X G digits c q w hist z field hq hw hz units room retained root j v) p
    rw [Stage.signed_read,actual_record X G digits c q w hist z field hq hw hz units room retained root S ready group]
    have addr:=actual_slot X G digits c q w hist z field hq hw hz units room retained root S ready j v f
    change some _=panelAt X v (Stage.signed T (native X c) S ready _ _ _)
    rw [addr]
    simp only [panelAt,atSlot,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    rcases f with ⟨b,y,eqn⟩;subst v;exact (at_wire X b y).symm
  · rw [Stage.signed_empty T (native X c) S ready names _ _ (fun p h=>hit ⟨p,h⟩)]
    let t : Fin 2 × Fin 256:=finProdFinEquiv.symm s
    change none=panel X v (finTwoEquiv t.1) t.2.val
    apply Eq.symm
    unfold panel
    split
    · rename_i yes
      obtain ⟨y,whereAt,pos⟩:=yes
      let f : Fiber X v:=⟨finTwoEquiv t.1,y,whereAt⟩
      have addr:=actual_slot X G digits c q w hist z field hq hw hz units room retained root S ready j v f
      exfalso;apply hit;refine ⟨port j v f,addr.trans ?_⟩
      rw [←finProdFinEquiv.apply_symm_apply s]
      apply congrArg finProdFinEquiv
      exact Prod.ext (finTwoEquiv.symm_apply_apply _) (Fin.ext pos)
    · rfl

end
end Hierarchy.DescentPackedSeed.Signed.Plane

/-! Both endpoint names on the first physical grain of every initialized cable. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentColonies DescentSixParty DescentSharedCableNames
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp pins r s : ℕ} (X : Approximation F cp pins)
    (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block r) (c : (initialGroup X S.copies s).Choice)
    {ε : ℝ} (q : ℝ) (w hist z : ℕ) (field : 0<r) (hq : 0<q)
    (hw : 0<w) (hz : 0<z) (eqn : s=z*G.b) (room : 3*(w*s)+hist≤256*(w*s))
    (retained : (q*hist)*((S.copies*Fintype.card X.network.copyGraph.Site:ℕ):ℝ)≤ε)
    (root : ((Fintype.card (Fin (S.groupCount 0))*Fintype.card (Vertex X):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*((w*s*256:ℕ):ℝ)))≤ε)
set_option quotPrecheck false
local notation "T" => source_group X G digits c q w hist z field hq hw hz eqn room retained root

/-- The actual stream index of the chosen incidence is the original cable's
unique grain. This also treats a loop whose two ends both lie at the same vertex. -/
theorem source_cable_fields : CableFields X S (T) ((oldOrder X c).trans Fin.valEmbedding)
    (Fintype.equivFin _).toEmbedding :=by
  intro valid j v e alive
  let unit:=initial_units X G digits c q w hist z field hq hw hz eqn room retained root
  let host:=initial_home X G digits c q w hist z field hq hw hz eqn room retained root
  let h:=vertexChart X digits (j,v)
  let origin:=liftCable X c j v e
  let port:=DescentTerminalPortChart.first (T) ⟨j,v⟩ origin alive
  let which:=incident X G digits c (T) unit host j v e
  have physical : Stage.ofPort (T) (native X c) h port=which :=by
    apply Subtype.ext
    exact DescentTerminalPortChart.first_number (T) (native X c) ⟨j,v⟩ origin alive
  let names:=initialNames X (r:=r) (Fin.valEmbedding (n:=S.groupCount 0))
  let src:=Stage.source (T) (native X c)
  change ((Stage.neighbors (T) (native X c) names).slot h (Stage.ofPort _ _ _ port)).val=_ ∧
    src.serial h (src.peer h (Stage.ofPort (T) (native X c) h port).val)
      (Stage.ofPort (T) (native X c) h port).val=_
  rw [physical]
  exact ⟨slot X G digits c (T) unit host names (initialNames_lt X digits Fin.valEmbedding)
    (initial_near X G digits c q w hist z field hq hw hz eqn room retained root) j v e,
    (chart X G digits c (T) unit host).serial j v e.val⟩

end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
