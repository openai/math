import OAI.Hierarchy.DescentRosterPaint
import OAI.Hierarchy.DescentPaddedPaint
import OAI.Hierarchy.DescentAffineOccupied
import OAI.Hierarchy.DescentStageMultiplier

namespace OAI
/-! # Identifying a measured stage in the dyadically padded physical searches -/

namespace Hierarchy.DescentColonies.DynamicSplit
open scoped Classical
noncomputable section
variable {L ℓ Δ : ℕ}

/-- A missing or ghost row contributes no entry to the compact host. -/
def compact (rs : Roster ℓ Δ) (h : L≤2^ℓ) (s : Fin L) : List (Fin L) :=
  (incoming rs (s.castLE h)).filterMap fun u=>
    if live : u.val<L then some ⟨u.val,live⟩ else none

private theorem recover (h : L≤2^ℓ) (xs : List (Fin (2^ℓ))) (real : ∀s∈xs,s.val<L) :
    ((xs.filterMap fun u=>if b:u.val<L then some (⟨u.val,b⟩ : Fin L) else none).map (Padded.front h))=xs := by
  induction xs with
  | nil=>rfl
  | cons u xs ih=>
    have good := real u List.mem_cons_self
    have rest := ih (fun v hv=>real v (List.mem_cons_of_mem u hv))
    simp only [List.filterMap_cons,dite_eq_left good,List.map_cons,rest]
    rfl

/-- Recover the ordered old roster from the stored rows. The proof uses only
which numbered host vertices are adjacent, so it permits any physical ordering. -/
theorem unpack_roster (rs : Roster ℓ Δ) (h : L≤2^ℓ) {V : Type} [Fintype V] [DecidableEq V]
    (e : V≃Fin L) (near : V→Finset V)
    (members : ∀i j,j∈incoming rs i ↔ ∃u v:V,i=(e u).castLE h ∧ j=(e v).castLE h ∧ u∈near v) :
    let raw := compact rs h
    let inc := fun u=>(raw (e u)).map e.symm
    incoming rs=Padded.neighbors h raw ∧
    (∀v z,v∈inc z ↔ z∈near v) ∧ (fun i=>(inc (e.symm i)).map e)=raw := by
  let raw := compact rs h
  have eqn : incoming rs=Padded.neighbors h raw := by
    funext i
    by_cases hit : i.val<L
    · let p : Fin L := ⟨i.val,hit⟩
      have back : p.castLE h=i := Fin.ext rfl
      have live (j : Fin (2^ℓ)) (hj : j∈incoming rs i) : j.val<L := by
        obtain ⟨_,v,_,rfl,_⟩ := (members i j).mp hj
        exact (e v).isLt
      simpa only [Padded.neighbors,dite_eq_left hit,raw,compact,back,p] using (recover h (incoming rs i) live).symm
    · rw [Padded.neighbors,dite_eq_right hit]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      obtain ⟨u,_,rfl,_,_⟩ := (members i j).mp hj
      exact hit (e u).isLt
  refine ⟨eqn,?_,?_⟩
  · intro v z
    let id := fun s : V=>(e s).castLE h
    have named : Function.Injective id := fun x y eqn=>e.injective (Fin.ext (congrArg (fun i : Fin (2^ℓ) => i.val) eqn))
    have index : id v∈incoming rs (id z) ↔ z∈near v := by
      constructor
      · intro mem
        obtain ⟨s,t,src,dst,linked⟩ := (members _ _).mp mem
        have hz : z=s := named src
        have hv : v=t := named dst
        simpa only [hz,hv] using linked
      · intro linked
        exact (members _ _).mpr ⟨z,v,rfl,rfl,linked⟩
    have group : e v∈raw (e z) ↔ z∈near v := by
      rw [eqn] at index
      change Padded.front h (e v) ∈ Padded.neighbors h raw (Padded.front h (e z)) ↔ _ at index
      simpa only [Padded.live_neighbors,List.mem_map,Function.Embedding.apply_eq_iff_eq,
        exists_eq_right] using index
    simpa [List.mem_map,Equiv.symm_apply_eq] using group
  · funext i
    simp [List.map_map,Function.comp_def]


end
end Hierarchy.DescentColonies.DynamicSplit

namespace Hierarchy.DescentSixParty.StageInput
open DescentColonies DescentGL DescentBinaryField DescentAffineColors DescentPacking StarKeys
open WinningSlabs ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d L ℓ Δ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {u ε : ℝ} (T : StageInput W G u ε)
local notation "full" => W.siteUnits T.hub T.records T.wire 256 T.hist
local notation "unit" => (T.wire*(T.z*G.b))
local notation "a" => DescentHostDegree.packExponent 20 T.Δ
local notation "D" => DescentHostDegree.gap T.Δ
local notation "cap" => (2^a*(unit*T.cap))
set_option quotPrecheck false in
local notation "pay" => fun v:W.graph.Site=>(W.core.filter fun edge=>W.graph.src edge=v).card

def loadsAt (e : T.V≃Fin L) (_ : Fin 1) (v : Fin L) :=
  blockMass W.graph T.pos T.block full (e.symm v)
def outgoingAt (e : T.V≃Fin L) (_ : Fin 1) (v : Fin L) :=
  blockMass W.graph T.pos T.block pay (e.symm v)

theorem score_is_canonical (e : T.V≃Fin L) (inc : T.V→List T.V)
    (listed : ∀v z,v∈inc z ↔ z∈T.near v) (μ : Nonzero T.k) :
    uniformColonyScore (fun s=>(inc (e.symm s)).map e) (T.loadsAt e) D cap (modulus T.fieldBits) μ=
      colonyCount (fun _ : Unit=>blockMass W.graph T.pos T.block full) (fun v z=>z∈T.near v)
        a (unit*T.cap) T.Δ (fun _=>T.small) (multiplier T.fieldBits μ) := by
  let load := blockMass W.graph T.pos T.block full
  let f := modulus T.fieldBits
  let q := multiplierLoad load f μ.val
  have rows : multiplierLoad (fun t=>load (e.symm t)) f μ.val=fun t=>q (e.symm t) := by
    funext t i
    rfl
  have re := Scan.leafScore_reindex e inc q D cap
  have cmp := scannedColonyCount_eq inc (fun _ : Unit=>load) _ listed a (unit*T.cap)
    T.Δ T.degreeMin (fun _=>T.small) (multiplier T.fieldBits μ)
  calc
    _ = Scan.leafScore (fun s=>(inc (e.symm s)).map e) (fun s=>q (e.symm s)) D cap := by
      simp only [uniformColonyScore,Fin.sum_univ_one]
      exact congrArg (fun weight => Scan.leafScore (fun s=>(inc (e.symm s)).map e) weight D cap) rows
    _ = _ := re.trans (by
      rw [show q=rearrangedLoad load (multiplier T.fieldBits μ) from
        multiplierLoad_eq load f μ.val (multiplier T.fieldBits μ) (multiplier_native T.fieldBits μ)]
      simpa [scannedColonyCount,DescentHostDegree.gap,DescentHostDegree.logDegree] using cmp)

theorem affine_is_canonical (e : T.V≃Fin L) (inc : T.V→List T.V)
    (listed : ∀v z,v∈inc z ↔ z∈T.near v) (μ : Nonzero T.k) (j : Candidate T.k) :
    let m := multiplier T.fieldBits μ
    let b := reindexedBlock W.graph T.block m
    let rows := Selected.winningRows (fun s=>(inc (e.symm s)).map e) (T.loadsAt e) D cap (modulus T.fieldBits) μ
    let amounts := Selected.winningAmounts (T.outgoingAt e) (modulus T.fieldBits) μ
    score (worldValue rows amounts) j=score
      (affineDirectory W.graph W.core T.pos b full T.near D a T.cap unit (small_reindexed W.graph T.pos T.block full T.small m)) j := by
  let m := multiplier T.fieldBits μ
  let b := reindexedBlock W.graph T.block m
  let good := small_reindexed W.graph T.pos T.block full T.small m
  let home := occupiedHome W.graph T.pos b full T.near D a (unit*T.cap) good
  have move (f : W.graph.Site→ℕ) :
      multiplierLoad (fun t=>blockMass W.graph T.pos T.block f (e.symm t)) (modulus T.fieldBits) μ.val =
        fun t=>blockMass W.graph T.pos b f (e.symm t) := by
    funext t i
    have renamed : multiplierLoad (fun t=>blockMass W.graph T.pos T.block f (e.symm t)) (modulus T.fieldBits) μ.val t i =
        multiplierLoad (blockMass W.graph T.pos T.block f) (modulus T.fieldBits) μ.val (e.symm t) i := by
      unfold multiplierLoad
      cases preimageWord (modulus T.fieldBits) μ.val i <;> rfl
    have load := (multiplierLoad_eq (blockMass W.graph T.pos T.block f) _ _ _
      (multiplier_native T.fieldBits μ)).trans (blockMass_reindexed W.graph T.pos T.block f m).symm
    exact renamed.trans (congrFun (congrFun load (e.symm t)) i)
  have source : pay=live (nativeTraffic W.graph W.core home) := (funext (outgoing_count W.graph W.core home)).symm
  have posD : 0<D := by
    have pow := Nat.le_pow_clog (by decide : 1<2) (2*T.Δ)
    have lower := T.degreeMin
    unfold DescentHostDegree.gap DescentHostDegree.logDegree
    by_contra! zero
    have bad : Nat.clog 2 (2*T.Δ)=0 := by omega
    rw [bad,pow_zero] at pow; omega
  let income := fun t => (inc (e.symm t)).map e
  have cols : worldValue (Selected.winningRows income (T.loadsAt e) D cap (modulus T.fieldBits) μ)
      (Selected.winningAmounts (T.outgoingAt e) (modulus T.fieldBits) μ) =
      worldValue (fun _ : Fin 1 => Scan.build income (fun t => blockMass W.graph T.pos b full (e.symm t)) D cap T.k)
        (fun _ t => blockMass W.graph T.pos b (live (nativeTraffic W.graph W.core home)) (e.symm t)) := by
    apply congrArg₂ (worldValue (G:=1) (H:=L) (k:=T.k))
    · funext g
      exact congrArg (fun f => Scan.build income f D cap T.k) (move full)
    · funext g
      exact (move pay).trans (congrArg (fun f : W.graph.Site→ℕ => fun t : Fin L =>
        blockMass W.graph T.pos b f (e.symm t)) source)
  exact (congrArg (fun values => score values j) cols).trans
    (native_score_eq_named W.graph W.core e T.pos b full T.near D a T.cap unit good inc listed posD j)

/-- The two minima selected by a public-capacity scan determine the particular
stage history, even though its actual host occupies only an initial segment. -/
theorem roster_scanned (he : 0≤ε) (e : T.V≃Fin L) (h : L≤2^ℓ) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v u:T.V,i=(e v).castLE h ∧ j=(e u).castLE h ∧ v∈T.near u)
    (μ : Nonzero T.k) (j : Candidate T.k)
    (seed :
      let Q := uniformColonyScore (DynamicSplit.incoming rs) (fun g=>Padded.table (T.loadsAt e g))
        D cap (modulus T.fieldBits)
      (scanMinimum Q (nonzeroWords T.k)).1=some (μ,Q μ))
    (paint :
      let rows := Selected.winningRows (DynamicSplit.incoming rs) (fun g=>Padded.table (T.loadsAt e g))
        D cap (modulus T.fieldBits) μ
      let A := worldValue rows (Selected.winningAmounts (fun g=>Padded.table (T.outgoingAt e g)) (modulus T.fieldBits) μ)
      (scanMinimum (scoreAt A) (List.range (2^(T.k+1)))).1=some (j.val,score A j)) :
    IsScannedAt W G T.pos T.block T.hub T.records T.wire T.hist T.z T.cap T.Δ T.near
      T.fieldBits T.small (T.result he) μ (linear j) (offset j) := by
  let raw := DynamicSplit.compact rs h
  let inc := fun v=>(raw (e v)).map e.symm
  obtain ⟨padded,listed,re⟩ := DynamicSplit.unpack_roster rs h e T.near members
  change DynamicSplit.incoming rs = Padded.neighbors h raw at padded
  change (fun i => (inc (e.symm i)).map e) = raw at re
  let cost := fun m:Nonzero T.k=>colonyCount (fun _ : Unit=>blockMass W.graph T.pos T.block full)
    (fun v z=>z∈T.near v) a (unit*T.cap) T.Δ (fun _=>T.small) (multiplier T.fieldBits m)
  have keys : uniformColonyScore raw (T.loadsAt e) D cap (modulus T.fieldBits)=cost := by
    funext ν
    rw [←re]
    exact T.score_is_canonical e inc listed ν
  obtain ⟨μ₀,α,β,old,first⟩ := T.result_scanned he
  have canonical : (scanMinimum cost (nonzeroWords T.k)).1 = some (μ₀,cost μ₀) := old.1
  have which := Padded.same_multiplier h raw (T.loadsAt e) D cap (modulus T.fieldBits) (nonzeroWords T.k)
  rw [←padded,seed,keys,canonical] at which
  have eqμ : μ=μ₀ := Option.some.inj which
  subst μ₀
  let m := multiplier T.fieldBits μ
  let orig := affineDirectory W.graph W.core T.pos (reindexedBlock W.graph T.block m) full T.near D a T.cap unit
    (small_reindexed W.graph T.pos T.block full T.small m)
  let actual := worldValue
    (Selected.winningRows (DynamicSplit.incoming rs) (fun g=>Padded.table (T.loadsAt e g)) D cap (modulus T.fieldBits) μ)
    (Selected.winningAmounts (fun g=>Padded.table (T.outgoingAt e g)) (modulus T.fieldBits) μ)
  have all (q : Candidate T.k) : score actual q = score orig q := by
    dsimp only [actual]
    rw [padded,Padded.slab_score,←re]
    exact T.affine_is_canonical e inc listed μ q
  have scores : scoreAt actual=scoreAt orig := by
    funext s;unfold scoreAt
    split <;> first | apply all | rfl
  have original : FirstPaint W.graph W.core T.pos (reindexedBlock W.graph T.block m) full T.near D a T.cap unit
      (small_reindexed W.graph T.pos T.block full T.small m) j := by
    change (scanMinimum (scoreAt orig) _).1=some (j.val,score orig j)
    simpa only [scores,all] using (show (scanMinimum (scoreAt actual) _).1=some (j.val,score actual j) from paint)
  have chosen := firstPaint_unique _ _ _ _ _ _ _ _ _ _ _ original first
  simpa only [chosen,linear_code,offset_code] using old

/-- Census carried out directly at the padded host addresses agrees with
extension by zero from every true old vertex. -/
theorem front_mass (e : T.V≃Fin L) (h : L≤2^ℓ) (f : W.graph.Site→ℕ)
    (v : Fin (2^ℓ)) (x : Block T.k) :
    blockMass W.graph (fun p=>(e (T.pos p)).castLE h) T.block f v x =
      Padded.table (fun t=>blockMass W.graph T.pos T.block f (e.symm t)) v x := by
  classical
  by_cases inside : v.val<L
  · let s : Fin L := ⟨v.val,inside⟩
    have old (p : W.graph.Site) : (e (T.pos p)).castLE h=v ↔ T.pos p=e.symm s := by
      constructor
      · intro eqn
        apply e.injective
        rw [e.apply_symm_apply]
        exact Fin.ext (congrArg (fun i : Fin (2^ℓ) => i.val) eqn)
      · intro eqn
        rw [eqn,e.apply_symm_apply]
        rfl
    simp only [Padded.table,dite_eq_left inside,blockMass,old,s]
  · have ghost (p : W.graph.Site) : (e (T.pos p)).castLE h≠v :=
      fun eqn=>inside (by rw [←eqn]; exact (e (T.pos p)).isLt)
    simp [Padded.table,inside,blockMass,ghost]

/-- The public-capacity solver starts with actual padded census values,
including all unused host positions. Its measured paint is attached to the
same history and the same incrementally issued multiplier word. -/
theorem roster_paint (he : 0≤ε) (e : T.V≃Fin L) (h : L≤2^ℓ) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v u:T.V,i=(e v).castLE h ∧ j=(e u).castLE h ∧ v∈T.near u)
    (adj base : ℕ) (wp raw : Fin 1→Fin (2^ℓ)→ℕ) (m : Memory w) (roster : DynamicSplit.Stored adj rs m)
    (oldAdj : adj+2^ℓ*Δ≤base) (old : ∀g v,wp g v+2^T.k≤base) (oldRaw : ∀g v,raw g v+2^T.k≤base)
    (room : RAM.paint T.k (Selected.endAt 1 (2^ℓ) T.k base)+2^T.k<2^w) (wide : 2^(ℓ+T.k)<2^w)
    (cf : cap<2^w) (total : W.core.card<2^w) (reserve : 2^T.k*(unit*T.cap)<2^w)
    (weights : ∀g v (x : Block T.k),m (wp g v+x.val)=
      (blockMass W.graph (fun p=>(e (T.pos p)).castLE h) T.block full v x:Word w))
    (amounts : ∀g v (x : Block T.k),m (raw g v+x.val)=
      (blockMass W.graph (fun p=>(e (T.pos p)).castLE h) T.block pay v x:Word w)) :
    let P := RosterPaint.program w ℓ Δ adj base D cap (modulus T.fieldBits) wp raw
    let z := Selected.endAt 1 (2^ℓ) T.k base
    ∃ out : Memory w,∃ μ : Nonzero T.k,∃ j : Candidate T.k,
      P.1.Exec m out P.2 ∧ IsScannedAt W G T.pos T.block T.hub T.records T.wire T.hist T.z T.cap T.Δ
        T.near T.fieldBits T.small (T.result he) μ (linear j) (offset j) ∧
      out (WinningColumns.winnerPtr 1 (2^ℓ) T.k base)=(MultiplierMinimumRAM.key μ:Word w) ∧
      out (RAM.chosen T.k z)=(j.val:Word w) ∧
      (∀x : Block T.k,out (RAM.paint T.k z+x.val)=((thick j x).toNat:Word w)) ∧
      (∀i<base,out i=m i) ∧
      ∀v (d : Fin T.k) (x : Block T.k),out (Materialized.dest base (((0 : Fin 1),v),some d)+x.val)=
        ((Scan.lookup (Selected.winningRows (DynamicSplit.incoming rs)
          (fun g=>Padded.table (T.loadsAt e g)) D cap (modulus T.fieldBits) μ 0) d.val v x).toNat:Word w) := by
  let pos := fun p:W.graph.Site=>(e (T.pos p)).castLE h
  let wt := fun g:Fin 1=>Padded.table (H:=2^ℓ) (T.loadsAt e g)
  let amt := fun g:Fin 1=>Padded.table (H:=2^ℓ) (T.outgoingAt e g)
  have capWt (g v x) : wt g v x≤unit*T.cap := by
    dsimp only [wt,Padded.table,loadsAt]
    split
    · exact T.small _ _
    · exact Nat.zero_le _
  have all : (∑g,∑v,∑x,amt g v x)=W.core.card := by
    rw [Fin.sum_univ_one]
    have read (v x) : amt 0 v x=blockMass W.graph pos T.block pay v x :=
      (T.front_mass e h pay v x).symm
    simp_rw [read]
    rw [total_blockMass]
    calc
      _ = ∑u : W.graph.Site, live (nativeTraffic W.graph W.core (fun _=>())) u :=
        Finset.sum_congr rfl fun u _ => (outgoing_count W.graph W.core (fun _=>()) u).symm
      _ = W.core.card := live_is_core W.graph W.core (fun _=>())
  obtain ⟨out,μ,j,run,picked,colors,seedWord,paintWord,bitsRead,keep,splitWords⟩ :=
    RosterPaint.execute ℓ Δ adj base D cap T.fieldBits wp raw rs m roster wt amt (unit*T.cap)
      oldAdj old oldRaw room wide cf (by simpa [pow_add] using wide) capWt reserve (all.trans_lt total)
      (fun g v x=>(weights g v x).trans (congrArg (fun x:ℕ=>(x:Word w)) (T.front_mass e h full v x)))
      (fun g v x=>(amounts g v x).trans (congrArg (fun x:ℕ=>(x:Word w)) (T.front_mass e h pay v x)))
  exact ⟨out,μ,j,run,T.roster_scanned he e h rs members μ j picked colors,seedWord,paintWord,bitsRead,keep,splitWords 0⟩

end
end Hierarchy.DescentSixParty.StageInput

end OAI
