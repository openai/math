import OAI.Hierarchy.DescentSeedInitialWidths
import OAI.Hierarchy.DescentSeedCableChart
import OAI.Hierarchy.DescentSeedRootRows
import OAI.Hierarchy.DescentHostRosterOrder
import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentGroupStage
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! Original cable and peer fields agree with the first physical signed group-stage panel. -/
namespace Hierarchy.DescentPackedSeed.Signed
open DescentSeedRoot DescentInitialHost DescentColonies DescentSixParty
open DescentSharedCableNames Computability.BorderVNP.Crossing Catalyst CorrectionBatch
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k n R s r : ℕ}
    (X : Approximation F k n) (G : PoweredGadget F)
    (digits : Fin R≃J×Block r) (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c
local notation "N" => X.network.copyGraph

def vertexChart : Fin R × Vertex X ↪ Stage.Host J (Vertex X) r where
  toFun p:=(( (digits p.1).1,p.2),(digits p.1).2)
  inj' _a _b h := Prod.ext (digits.injective (Prod.ext (congrArg (fun x : Stage.Host J (Vertex X) r => x.1.1) h) (congrArg (fun x : Stage.Host J (Vertex X) r => x.2) h)))
    (congrArg (fun x=>x.1.2) h)

/-- The physical group/vertex/block numbering in the matching advertisement. -/
def initialNames (group : J ↪ ℕ) :=
  DescentPacking.PackedMatch.Local.Stage.cableNames r (DescentStageEdgeReceipt.groupRank group (vertexName X))

omit [Field F] [Fintype J] [DecidableEq J] in
theorem initialNames_lt (group : J ↪ ℕ) (j : Fin R) (v t : Vertex X) :
    initialNames X (r:=r) group (vertexChart X digits (j,v)) <
      initialNames X (r:=r) group (vertexChart X digits (j,t)) ↔ index v< index t := by
  change (group (digits j).1*DescentStageEdgeReceipt.pitch (vertexName X)+index v)*2^r+(digits j).2.val <
    (group (digits j).1*DescentStageEdgeReceipt.pitch (vertexName X)+index t)*2^r+(digits j).2.val ↔ _
  simp only [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos r),Nat.add_lt_add_iff_left]

abbrev native := (cableOrder X c).trans Fin.valEmbedding

variable {q ε : ℝ} (A : GroupStage ((initialGroup X R s).state c) G q ε J (Vertex X) r)
variable (units : ∀ e : ((initialGroup X R s).state c).graph.Edge,A.grainCount e=1)

include units in
def one (j : Fin R) (e : Cable X) : Fin (A.grainCount ⟨j,e⟩) := ⟨0, Nat.zero_lt_one.trans_eq (units ⟨j,e⟩).symm⟩

include units in
def unitEquiv : Fin R × Cable X ≃ Stage.Grain A where
  toFun p:=⟨⟨p.1,p.2⟩,one X G c A units p.1 p.2⟩
  invFun p:=(p.1.1,p.1.2)
  left_inv _:=rfl
  right_inv := by
    rintro ⟨⟨j,e⟩,u⟩
    have single : one X G c A units j e = u := by
      apply Fin.ext
      have hi := u.isLt.trans_eq (units ⟨j,e⟩)
      change 0=u.val
      omega
    exact congrArg (fun t : Fin (A.grainCount ⟨j,e⟩) => (⟨⟨j,e⟩, t⟩ : Stage.Grain A)) single

variable (home : ∀ (j : Fin R) (v : Vertex X),Stage.home A ⟨j,v⟩=vertexChart X digits (j,v))
local notation "B" => Stage.source A (native X c)

include units home in
def chart : Chart X B R where
  vertex:=vertexChart X digits
  wire:=(unitEquiv X G c A units).trans (Stage.stream A (native X c))
  src j e:=by
    change Stage.home A ((W).graph.src (((Stage.stream A (native X c)).symm
      ((Stage.stream A (native X c)) ⟨⟨j,e⟩,one X G c A units j e⟩)).1))=_
    rw [Equiv.symm_apply_apply]
    exact home j (source N e)
  dst j e:=by
    change Stage.home A ((W).graph.dst (((Stage.stream A (native X c)).symm
      ((Stage.stream A (native X c)) ⟨⟨j,e⟩,one X G c A units j e⟩)).1))=_
    rw [Equiv.symm_apply_apply]
    exact home j (target N e)
  lt j e f:=by
    have forward (a b : Cable X) (old : index a< index b) :
        (Stage.stream A (native X c) ⟨⟨j,a⟩,one X G c A units j a⟩).val<
        (Stage.stream A (native X c) ⟨⟨j,b⟩,one X G c A units j b⟩).val := by
      have order : native X c ⟨j,a⟩<native X c ⟨j,b⟩ := by
        change (cableOrder X c ⟨j,a⟩).val<(cableOrder X c ⟨j,b⟩).val
        simpa only [cableOrder_val,cableID,Nat.add_lt_add_iff_left] using old
      have before:=ProtocolRAMPortRanks.prefix_disjoint A.grainCount (native X c) order
      have positive := Nat.zero_lt_one.trans_eq (units ⟨j,a⟩).symm
      have prior : ProtocolRAMPortRanks.prefix A.grainCount (native X c) ⟨j,a⟩ <
          ProtocolRAMPortRanks.prefix A.grainCount (native X c) ⟨j,b⟩ :=
        (Nat.lt_add_of_pos_right positive).trans_le before
      exact prior
    rcases lt_trichotomy (index e) (index f) with ef|eq|fe
    · exact iff_of_true (forward e f ef) ef
    · have eqn : e=f:=(Fintype.equivFin _).injective (Fin.ext eq)
      subst f;simp
    · exact iff_of_false (not_lt_of_ge (forward f e fe).le) (not_lt_of_ge fe.le)

include units home in
def incident (j : Fin R) (v : Vertex X) (e : {e : Cable X // source N e=v ∨ target N e=v}) :
    ↥((B).incident (vertexChart X digits (j,v))) := by
  let C := chart X G digits c A units home
  refine ⟨C.wire (j,e.val),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  exact e.property.imp (fun h=>by rw [C.src,h];rfl) (fun h=>by rw [C.dst,h];rfl)

variable (rank : Stage.Host J (Vertex X) r ↪ ℕ)
variable (names : ∀ (j : Fin R) (v t : Vertex X), rank (vertexChart X digits (j,v))<rank (vertexChart X digits (j,t)) ↔ index v< index t)
variable (nearby : A.near=DescentInitialHost.near X.network.copyGraph)

include nearby in
private theorem near_map (j : Fin R) (v : Vertex X) :
    Stage.near A (vertexChart X digits (j,v))=(near N v).map
      ⟨fun t=>vertexChart X digits (j,t),fun _ _ h=>congrArg (fun z=>z.1.2) h⟩ := by
  ext y
  simp only [Stage.near,DescentHostDirectory.groupedNear,vertexChart,Function.Embedding.coeFn_mk,Finset.mem_map]
  rw [nearby]
  constructor
  · rintro ⟨a,⟨t,ht,rfl⟩,rfl⟩;exact ⟨t,ht,rfl⟩
  · rintro ⟨t,ht,rfl⟩;exact ⟨_,⟨t,ht,rfl⟩,rfl⟩

set_option maxHeartbeats 450000 in
include units home names nearby in
theorem slot (j : Fin R) (v : Vertex X) (e : {e : Cable X // source N e=v ∨ target N e=v}) :
    ((Stage.neighbors A (native X c) rank).slot (vertexChart X digits (j,v))
      (incident X G digits c A units home j v e)).val=seedPeer X v e.val := by
  let C:=chart X G digits c A units home
  change (Ends.neighborOrder _ rank _ _ _).val=_
  rw [DescentPacking.PackedMatch.Local.Stage.nb_val]
  change ((Stage.near A (vertexChart X digits (j,v))).filter
    (fun t=>rank t<rank ((B).peer (C.vertex (j,v)) (C.wire (j,e.val))))).card=_
  rw [C.peer,near_map X G digits c A nearby j v]
  let embed : Vertex X ↪ Stage.Host J (Vertex X) r :=
    ⟨fun t=>vertexChart X digits (j,t),fun _ _ h=>congrArg (fun z=>z.1.2) h⟩
  have eqn : (((near N v).map embed).filter (fun t=>rank t<rank (C.vertex (j,other X v e.val))))=
      (((near N v).filter (fun t=>index t< index (other X v e.val))).map embed) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨⟨u,hu,rfl⟩,lt⟩;exact ⟨u,⟨hu,(names ..).mp lt⟩,rfl⟩
    · rintro ⟨u,⟨hu,lt⟩,rfl⟩;exact ⟨⟨u,hu,rfl⟩,(names ..).mpr lt⟩
  rw [eqn,Finset.card_map]
  rfl

private theorem of_as (h : Stage.Host J (Vertex X) r) (y : ↥((B).incident h)) :
    Stage.ofPort A (native X c) h (Stage.asPort A (native X c) h y)=y := by
  apply Subtype.ext
  have val (p : A.CellPorts h.1.1 h.1.2 h.2) :
      (Stage.ofPort A (native X c) h p).val =
        (Stage.stream A (native X c)) (Stage.recover A h p) := by cases p <;> rfl
  rw [val, Stage.recover_port]
  exact (Stage.stream A (native X c)).apply_symm_apply y.val

include units home names nearby in
theorem physical_panel (S : DescentCompiler.AtomSchedule) {i : ℕ} (ready : A.StateBounds S i)
    (j : Fin R) (v : Vertex X) (e : {e : Cable X // source N e=v ∨ target N e=v}) :
    let h:=vertexChart X digits (j,v)
    let y:=incident X G digits c A units home j v e
    let p:=Stage.asPort A (native X c) h y
    let record:=Stage.live A (native X c) S ready rank h p
    Stage.signedPanel A (native X c) S ready rank h (Stage.signed A (native X c) S ready h.1 h.2 p)=some record ∧
      record.neighbor.val=seedPeer X v e.val ∧ record.wire.val=seedParallel X v e.val := by
  dsimp only
  refine ⟨Stage.signed_read ..,?_,?_⟩
  · change ((Stage.neighbors A (native X c) rank).slot _ (Stage.ofPort _ _ _ (Stage.asPort ..))).val=_
    rw [of_as]
    exact slot X G digits c A units home rank names nearby j v e
  · change (B).serial _ ((B).peer _ (Stage.ofPort _ _ _ (Stage.asPort ..)).val) (Stage.ofPort _ _ _ (Stage.asPort ..)).val=_
    rw [of_as]
    exact (chart X G digits c A units home).serial j v e.val

section Seed
variable {ε : ℝ} (q : ℝ) (w hist z : ℕ) (field : 0<r) (hq : 0<q)
    (hw : 0<w) (hz : 0<z) (eqn : s=z*G.b) (room : 3*(w*s)+hist≤256*(w*s))
    (retained : (q*hist)*((R*Fintype.card X.network.copyGraph.Site:ℕ):ℝ)≤ε)
    (root : ((Fintype.card J*Fintype.card (Vertex X):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*((w*s*256:ℕ):ℝ)))≤ε)
local notation "T" => source_group X G digits c q w hist z field hq hw hz eqn room retained root

theorem initial_units (e : (W).graph.Edge) : (T).grainCount e=1 := by
  change (W).graph.width e / (z * G.b) = 1
  rw [source_all_widths X c e, eqn, Nat.div_self (Nat.mul_pos hz G.base_pos)]

theorem initial_home (j : Fin R) (v : Vertex X) : Stage.home T ⟨j,v⟩=vertexChart X digits (j,v) := rfl

theorem initial_near : (T).near=DescentInitialHost.near N := rfl

theorem seed_cable (S : DescentCompiler.AtomSchedule) {i : ℕ} (ready : (T).StateBounds S i)
    (group : J ↪ ℕ) (j : Fin R) (v : Vertex X) (e : {e : Cable X // source N e=v ∨ target N e=v}) :
    let h:=vertexChart X digits (j,v)
    let names:=initialNames X (r:=r) group
    ∃ (p : (T).CellPorts h.1.1 h.1.2 h.2) («rec» : Stage.Live (T).degree (T).cap),
      Stage.signedPanel T (native X c) S ready names h (Stage.signed T (native X c) S ready h.1 h.2 p)=some «rec» ∧
      «rec».neighbor.val=seedPeer X v e.val ∧ «rec».wire.val=seedParallel X v e.val ∧
      (Stage.recover T h p).1=⟨j,e.val⟩ := by
  let u:=initial_units X G digits c q w hist z field hq hw hz eqn room retained root
  let home:=initial_home X G digits c q w hist z field hq hw hz eqn room retained root
  let h:=vertexChart X digits (j,v)
  let y:=incident X G digits c T u home j v e
  let p:=Stage.asPort T (native X c) h y
  let names:=initialNames X (r:=r) group
  let «rec»:=Stage.live T (native X c) S ready names h p
  have panel:=physical_panel X G digits c T u home names (initialNames_lt X digits group)
    (initial_near X G digits c q w hist z field hq hw hz eqn room retained root) S ready j v e
  refine ⟨p,«rec»,panel.1,panel.2.1,panel.2.2,?_⟩
  change (Stage.recover T h (Stage.asPort T (native X c) h y)).1=_
  rw [Stage.recover_port]
  exact congrArg Sigma.fst ((Stage.stream T (native X c)).symm_apply_apply
    ((unitEquiv X G c T u) (j,e.val)))
end Seed

end
end Hierarchy.DescentPackedSeed.Signed

end OAI
