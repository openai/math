import OAI.Hierarchy.DescentResetStemPortData
import OAI.Hierarchy.DescentResetStemDescriptorRAM
import OAI.Hierarchy.DescentResetStemObservedWord

namespace OAI
/-! # Detecting a physical stem at a receiver from its endpoint and neighbor words -/
namespace Hierarchy.DescentResetStemIncidence
open DescentResetStemDescriptorRAM DescentSortedRoster DescentPackedColony DescentFallbackRankRAM
open DescentSixParty.ClosedReset DescentResetFieldAssembler ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {K H pitch w stop U : ℕ}

def Ports.incident (p : Ports K) (j : Fin K) : Expr :=
  .branch .eq (p.src j) p.here (.lit 1) (.branch .eq (p.dst j) p.here (.lit 1) (.lit 0))

def Ports.inputs (p : Ports K) (side : Fin K→Bool) : Inputs K where
  roster := Fin.cases p.here p.near
  here := p.here
  src := p.src
  dst := p.dst
  live := p.incident
  selfAbsent := fun _=>unlessSeen p.here (.lit 1) (List.ofFn p.near)
  core := fun j=>if side j then .lit 1 else .branch .eq (p.oldHub j) (.lit 0) (.lit 1) (.lit 0)

def Scene.peers (s : Scene K H pitch) (v : Fin pitch) : Fin 4→Option (Fin pitch) :=
  Fin.cases (some v) (s.near v)

def Scene.neighbors (s : Scene K H pitch) (v : Fin pitch) : Finset ℕ :=
  (present s.near v).map Fin.valEmbedding

def hits (v : Fin pitch) (ab : Option (Fin pitch×Fin pitch)) : Bool :=
  ab.elim false (fun xy=>decide (xy.1.val=v.val ∨ xy.2.val=v.val))

def Scene.values (s : Scene K H pitch) (side : Fin K→Bool) : Values K H pitch where
  peer := s.peers
  here := s.here
  src := fun j r=>(s.ends j r).elim (s.here r) Prod.fst
  dst := fun j r=>(s.ends j r).elim (s.here r) Prod.snd
  live := fun j r=>hits (s.here r) (s.ends j r)
  selfAbsent := fun _ r=>decide ((s.here r).val∉s.neighbors (s.here r))
  core := fun j r=>side j || !(s.oldHub j r)

theorem Scene.self_mem (s : Scene K H pitch) (v : Fin pitch) :
    v.val∈s.neighbors v ↔ ∃i,s.near v i=some v := by
  constructor
  · intro mem
    obtain ⟨z,hz,e⟩:=Finset.mem_map.mp mem
    have same : z=v:=Fin.ext e
    subst z
    exact (Finset.mem_filter.mp hz).2
  · intro h
    exact Finset.mem_map.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩

theorem Scene.present_peers (s : Scene K H pitch) (v : Fin pitch) :
    present s.peers v=insert v (present s.near v) := by
  ext z
  simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,h⟩
    cases i using Fin.cases with
    | zero => exact Or.inl (Option.some.inj h).symm
    | succ t => exact Or.inr ⟨t,h⟩
  · rintro (rfl|⟨i,h⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨i.succ,h⟩

theorem Scene.ordinal (s : Scene K H pitch) (v z : Fin pitch) :
    before s.peers v z=Window.stemOrdinal v.val (s.neighbors v) z.val := by
  have mapped : (insert v (present s.near v)).map Fin.valEmbedding =
      insert v.val ((present s.near v).map Fin.valEmbedding) :=
    Finset.map_insert Fin.valEmbedding v (present s.near v)
  rw [before,s.present_peers,Window.stemOrdinal,Scene.neighbors,←mapped,
    Finset.filter_map,Finset.card_map]; rfl

/-- This includes an absent endpoint pair, loops, and nonincident pairs.
The native sorted roster counts each distinct present neighbor once. -/
theorem Scene.descriptor_eq (s : Scene K H pitch) (side : Fin K→Bool) (j : Fin K) (r : Fin H) :
    (s.values side).descriptor j r=Window.stemWord (s.here r).val (s.neighbors (s.here r))
      (side j) (s.oldHub j r) ((s.ends j r).map (fun x=>(x.1.val,x.2.val))) := by
  cases h:s.ends j r with
  | none => simp [Values.descriptor,Scene.values,hits,h,Window.stemWord]
  | some v =>
    by_cases hit:v.1.val=(s.here r).val ∨ v.2.val=(s.here r).val <;>
      simp [Values.descriptor,Scene.values,hits,h,Window.stemWord,hit,s.ordinal]

private theorem target_eq (id : Option (Fin pitch)) (v : Fin pitch) (room : pitch<2^w) :
    (target id:Word w)=(v.val:Word w) ↔ id=some v := by
  have bound : target id<2^w := by
    cases id with
    | none => exact room
    | some a => exact a.isLt.trans room
  rw [Fin.ext_iff,Fin.val_cast_of_lt bound,Fin.val_cast_of_lt (v.isLt.trans room)]
  cases id with
  | none => exact iff_of_false v.isLt.ne' (by simp)
  | some a => exact ⟨fun h=>congrArg some (Fin.ext h),fun h=>congrArg Fin.val (Option.some.inj h)⟩

theorem Ports.observed (p : Ports K) (s : Scene K H pitch) (side : Fin K→Bool) (m : Memory w)
    (room : pitch<2^w) (seen : Reads p s m) : Observed (p.inputs side) (s.values side) m := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro r i
    cases i using Fin.cases with
    | zero => exact seen.here r
    | succ i => exact seen.near r i
  · intro r
    change (p.here.eval m _).val=(s.here r).val
    rw [seen.here,Fin.val_cast_of_lt ((s.here r).isLt.trans room)]
  · intro j r
    have eq₁ : (p.src j).eval m (r.val:Word w)=p.here.eval m (r.val:Word w) ↔
        (s.ends j r).map Prod.fst=some (s.here r) := by
      rw [seen.src,seen.here,target_eq _ _ room]
    have eq₂ : (p.dst j).eval m (r.val:Word w)=p.here.eval m (r.val:Word w) ↔
        (s.ends j r).map Prod.snd=some (s.here r) := by
      rw [seen.dst,seen.here,target_eq _ _ room]
    change (p.incident j).eval m (r.val:Word w)=((hits (s.here r) (s.ends j r)).toNat:Word w)
    cases h:s.ends j r with
    | none => simp [Ports.incident,Expr.eval,Comparison.test,eq₁,eq₂,h,hits]
    | some ab =>
      by_cases e₁:ab.1=s.here r <;> by_cases e₂:ab.2=s.here r <;>
        simp [Ports.incident,Expr.eval,Comparison.test,eq₁,eq₂,h,hits,Fin.val_inj,e₁,e₂]
  · intro j r live
    change hits (s.here r) (s.ends j r)=true at live
    change ((p.src j).eval m _).val=((s.ends j r).elim (s.here r) Prod.fst).val
    cases h:s.ends j r with
    | none => simp [h,hits] at live
    | some xy =>
      rw [seen.src,h]
      exact Fin.val_cast_of_lt (xy.1.isLt.trans room)
  · intro j r live
    change hits (s.here r) (s.ends j r)=true at live
    change ((p.dst j).eval m _).val=((s.ends j r).elim (s.here r) Prod.snd).val
    cases h:s.ends j r with
    | none => simp [h,hits] at live
    | some xy =>
      rw [seen.dst,h]
      exact Fin.val_cast_of_lt (xy.2.isLt.trans room)
  · intro j r _
    change (unlessSeen p.here (.lit 1) (List.ofFn p.near)).eval m (r.val:Word w)=_
    rw [unlessSeen_eval]
    have has : (∃e∈List.ofFn p.near,e.eval m (r.val:Word w)=p.here.eval m (r.val:Word w)) ↔
        (s.here r).val∈s.neighbors (s.here r) := by
      rw [s.self_mem]
      constructor
      · rintro ⟨e,he,h⟩
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
        rw [seen.near,seen.here,target_eq _ _ room] at h
        exact ⟨i,h⟩
      · rintro ⟨i,h⟩
        refine ⟨p.near i,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
        rw [seen.near,seen.here,target_eq _ _ room]
        exact h
    by_cases mem:(s.here r).val∈s.neighbors (s.here r)
    · rw [ite_eq_left (has.mpr mem)]
      simp [Scene.values,mem]
    · rw [ite_eq_right (mt has.mp mem)]
      simp [Scene.values,mem,Expr.eval]
  · intro j r _
    have nz : (1:Word w)≠0 := by
      have one : 1<2^w := by have h:=(s.here r).isLt;omega
      intro same
      have eqn:=congrArg Fin.val same
      change 1 % (2^w) = 0 at eqn
      rw [Nat.mod_eq_of_lt one] at eqn
      omega
    cases hs:side j <;> cases h:s.oldHub j r <;>
      simp [Ports.inputs,Scene.values,Expr.eval,Comparison.test,seen.oldHub,h,hs,nz]

private theorem mask_fits (e : Expr) (es : List Expr) (efit : e.Fits w stop)
    (fits : ∀x∈es,x.Fits w stop) : (unlessSeen e (.lit 1) es).Fits w stop := by
  induction es with
  | nil => trivial
  | cons a as ih => exact ⟨fits a (.head _),efit,trivial,ih (fun b hb=>fits b (.tail _ hb))⟩

theorem Ports.fits (p : Ports K) (side : Fin K→Bool) (fit : p.All (Expr.Fits w stop)) :
    (p.inputs side).All (Expr.Fits w stop) := by
  refine ⟨?_,fit.here,fit.src,fit.dst,?_,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact fit.here
    | succ i => exact fit.near i
  · intro j
    exact ⟨fit.src j,fit.here,trivial,fit.dst j,fit.here,trivial,trivial⟩
  · intro j
    apply mask_fits _ _ fit.here
    intro e he
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    exact fit.near i
  · intro j
    change (if side j then Expr.lit 1 else .branch .eq (p.oldHub j) (.lit 0) (.lit 1) (.lit 0)).Fits w stop
    split
    · trivial
    · exact ⟨fit.hub j,trivial,trivial,trivial⟩

private theorem mask_work (e : Expr) (es : List Expr) (cost : e.work≤U)
    (costs : ∀x∈es,x.work≤U) : (unlessSeen e (.lit 1) es).work≤1+es.length*(2*U+2) := by
  induction es with
  | nil => simp [unlessSeen,Expr.work]
  | cons a as ih =>
    have bound:=costs a (.head _)
    have rest:=ih (fun b hb=>costs b (.tail _ hb))
    change a.work+e.work+1+(unlessSeen e (.lit 1) as).work+1≤_
    rw [List.length_cons,Nat.succ_mul]
    omega

theorem Ports.work (p : Ports K) (side : Fin K→Bool) (cost : p.All (fun e=>e.work≤U)) :
    (p.inputs side).All (fun e=>e.work≤6*U+7) := by
  have base : U≤6*U+7:=by omega
  refine ⟨?_,cost.here.trans base,(fun j=>(cost.src j).trans base),(fun j=>(cost.dst j).trans base),?_,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact cost.here.trans base
    | succ i => exact (cost.near i).trans base
  · intro j
    have h:=cost.here
    have a:=cost.src j
    have b:=cost.dst j
    change (p.src j).work+p.here.work+1+((p.dst j).work+p.here.work+1+1+1)+1≤_
    omega
  · intro j
    have h:=mask_work p.here (List.ofFn p.near) cost.here (fun e he=>by
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
      exact cost.near i)
    change (unlessSeen p.here (.lit 1) (List.ofFn p.near)).work≤_
    rw [List.length_ofFn] at h
    omega
  · intro j
    have h:=cost.hub j
    change (if side j then Expr.lit 1 else .branch .eq (p.oldHub j) (.lit 0) (.lit 1) (.lit 0)).work≤_
    split
    · change 1≤_
      omega
    · change (p.oldHub j).work+1+1+1+1≤_
      omega

/-- The compiled issuer reads only the physical endpoints, neighbors, hub, and actor identifier.
It publishes the exact raw stem word for each candidate, including blank rows. -/
theorem Ports.publish (p : Ports K) (s : Scene K H pitch) (side : Fin K→Bool) (b base out : ℕ) (m : Memory w)
    (seen : Reads p s m) (fit : p.All (Expr.Fits w base)) (small : pitch<2^w) (early : base+56≤out)
    (room : out+K*H<2^w) :
    let L:=p.inputs side
    let last:=output L b H base out m
    (code L b w H base out).Exec m last (ticks L H base out) ∧
      DescentResetStemHeaders.Raw out (fun j r=>raw b (Window.stemWord (s.here r).val
        (s.neighbors (s.here r)) (side j) (s.oldHub j r) ((s.ends j r).map (fun ab=>(ab.1.val,ab.2.val))))) last ∧
      (∀u,u<base ∨ base+56≤u→u<out ∨ out+K*H≤u→last u=m u) ∧ CheapCode (code L b w H base out) := by
  simpa only [s.descriptor_eq] using run (p.inputs side) b base out (s.values side) m
    (p.observed s side m small seen) (p.fits side fit) small early room

theorem Ports.clock_bound (p : Ports K) (side : Fin K→Bool) (U H base out : ℕ) (cost : p.All (fun e=>e.work≤U)) :
    ticks (p.inputs side) H base out≤(4+10*56)+(4+K*(4+H*(2*workLimit (6*U+7)+4))) :=
  ticks_le (p.inputs side) (6*U+7) H base out (p.work side cost)

theorem Ports.names_bound (p : Ports K) (side : Fin K→Bool) (b w U H base out : ℕ) (cost : p.All (fun e=>e.work≤U)) :
    DescentStaticWordColumn.names (code (p.inputs side) b w H base out)≤
      15*(56+1)+(15+K*(11+4*workLimit (6*U+7))) :=
  names_le (p.inputs side) b w (6*U+7) H base out (p.work side cost)


end
end Hierarchy.DescentResetStemIncidence

end OAI
