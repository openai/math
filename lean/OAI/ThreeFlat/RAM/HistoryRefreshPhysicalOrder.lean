import OAI.ThreeFlat.RAM.HistoryRefreshRoot

namespace OAI
/-! # Physical ordering and placement of refresh party pairs -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

open private pair_cells from OAI.ThreeFlat.RAM.HistoryRefreshRoot

section Arena
open HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
variable (u : ℕ) (arch : HistoryStageBody.Physical.Archive) (family : Family)
local notation "A" => layout u arch family
local notation "W₀" => 16*u^10
variable (node : ℕ) (winner : Fin family.parties)

/-- Non-overlap of any two distinct full physical local pages, independent of the selected node. -/
theorem local_apart {V M P base n : ℕ} {x y : Local} (positive : 0<V)
    (capacity : (M+2)*(P+2)*8*32≤V) (xok : x.Valid M P) (yok : y.Valid M P) (ne : x≠y) :
    atWord base V M P n x 0+V≤atWord base V M P n y 0 ∨
    atWord base V M P n y 0+V≤atWord base V M P n x 0 := by
  have diff : sector M P x≠sector M P y := by
    intro h
    have e:atWord base V M P n x 0=atWord base V M P n y 0 := by simp [atWord,h]
    exact ne ((HistoryScratch.separated capacity xok yok positive positive e).2.1)
  have step (i j : ℕ) (lt : i<j) : base+(n*V+i)*V+V≤base+(n*V+j)*V := by
    have h':n*V+i+1≤n*V+j := by omega
    have z:=Nat.mul_le_mul_right V h'
    rw [Nat.add_one_mul] at z
    omega
  obtain h|h:=lt_or_gt_of_ne diff
  · exact Or.inl (by simpa only [atWord,Nat.add_zero] using step _ _ h)
  · exact Or.inr (by simpa only [atWord,Nat.add_zero] using step _ _ h)

local notation "V" => volume u
local notation "F₀" => fun x : Local=>atWord (base u 12) V family.motifs family.parties node x 0

/-- Every complete private page fits in S12 at the physical word size. -/
theorem local_window (age : 16≤u) (idRoom : node<V^2)
    (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (x : Local) (ok : x.Valid family.motifs family.parties) :
    base u 12≤F₀ x ∧ F₀ x+V≤base u 12+Diagonal.TickWorkspace.stride u ∧ F₀ x+V<2^W₀ := by
  have positive : 0<V := Nat.two_pow_pos _
  have last : V-1<V := by omega
  have r:=HistoryScratch.fits (base:=base u 12) idRoom capacity ok last
  have div : atWord (base u 12) V family.motifs family.parties node x (V-1)=F₀ x+(V-1) := by
    simp [atWord]
  rw [div] at r
  change F₀ x+(V-1)<base u 12+Diagonal.TickWorkspace.stride u at r
  have wide : 12<Diagonal.TickWorkspace.stride u := by
    have g : 16≤V := age.trans ((Nat.le_self_pow (by decide : 10≠0) u).trans (Nat.lt_two_pow_self.le))
    have p : V≤V^4 := Nat.le_self_pow (by decide) V
    change 12<V^4
    omega
  have w:=word_space (i:=12) (by omega : 1≤u) wide
  refine ⟨?_,by omega,by omega⟩
  change base u 12 ≤ base u 12+(node*V+sector family.motifs family.parties x)*V+0
  exact Nat.le_add_right _ _

omit [CommRing F] in
/-- All nonempty-source, map and fresh row extents used by the refresh singleton join
follow from S12 sector separation and the real S14 control location. -/
theorem physical_root_space (L : Tree F a) (R : Tree F b) (id : ((Fin 3→Bool)→F)→ℕ)
    (mem : Memory W₀) (age : 16≤u) (idRoom : node<V^2) (positiveMotifs : 0<family.motifs)
    (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (pins : a+b≤V) (rows : 4*(pair L R).compile.cells≤V)
    (gateFit : ∀ i j,HistoryCompiledRows.metadata id (pair L R).compile i j<2^W₀) :
    RootSpace A node winner L R (p:=p) id mem := by
  let source := fun k:ℕ=>(⟨2,winner.val+2,2,k⟩:Local)
  let target := (⟨2,0,3,0⟩:Local)
  have pos : 0<V:=Nat.two_pow_pos _
  have valid (k : ℕ) (hk : k<32) : (source k).Valid family.motifs family.parties := by
    simp only [Local.Valid,source]
    exact ⟨by omega,by have := winner.isLt;omega,by decide,hk⟩
  have vt : target.Valid family.motifs family.parties := by
    change 2 < family.motifs+2 ∧ 0 < family.parties+2 ∧ 3 < 8 ∧ 0 < 32
    exact ⟨by omega, by omega, by decide, by decide⟩
  have src (k : ℕ) (hk : k<32) := local_window u family node age idRoom capacity (source k) (valid k hk)
  have dst:=local_window u family node age idRoom capacity target vt
  have apart:=local_apart (base:=base u 12) (n:=node) pos capacity (valid 3 (by decide)) vt
    (by intro eqn;have z:=congrArg Local.party eqn;change winner.val+2=0 at z;omega)
  have before₁:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have roomSeed : base u 14+V+7<2^W₀ := by
    have bound : 16≤V:=age.trans ((Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le)
    have big : V+7<V^4 := calc
      V+7<2*V := by omega
      _≤V*V:=Nat.mul_le_mul_right _ (by omega)
      _=V^2:=(pow_two V).symm
      _≤V^4:=Nat.pow_le_pow_right pos (by decide)
    have width : 14<Diagonal.TickWorkspace.stride u := by change 14<V^4;omega
    have word:=word_space (i:=14) (by omega : 1≤u) width
    change base u 14+V^4<2^W₀ at word
    omega
  have ctrl : ((base u 14+V+7:ℕ):Word W₀).val=base u 14+V+7 :=Fin.val_cast_of_lt roomSeed
  have s0:=src 0 (by decide)
  have s2:=src 2 (by decide)
  have s3:=src 3 (by decide)
  change RootSpace A node winner L R (p:=p) id mem
  constructor
  · have stridePos : 0<Diagonal.TickWorkspace.stride u := Nat.pow_pos pos
    have seedBase : 2≤base u 14 := by change 2≤(14+1)*Diagonal.TickWorkspace.stride u;omega
    omega
  · change F₀ (source 3)+(a+b)≤2^W₀;omega
  · change F₀ (source 2)+(a+b)≤2^W₀;omega
  · change F₀ (source 2)<2^W₀;omega
  · change F₀ (source 3)+(a+b)≤F₀ target ∨ F₀ target+4*(pair L R).compile.cells≤F₀ (source 3)
    change F₀ (source 3)+V≤F₀ target ∨ F₀ target+V≤F₀ (source 3) at apart
    rcases apart with l|r <;> omega
  · change _<F₀ (source 3) ∨ F₀ (source 3)+(a+b)≤((base u 14+V+7:ℕ):Word W₀).val
    rw [ctrl];omega
  · change _<F₀ target ∨ F₀ target+4*(pair L R).compile.cells≤((base u 14+V+7:ℕ):Word W₀).val
    rw [ctrl];omega
  · change F₀ (source 0)+4*(pair L R).compile.cells≤2^W₀;omega
  · exact gateFit
  · exact rows

/-- Within any refresh node, these are the six consecutive relevant sectors, in physical
order: output stream and root, then the elected stream, root, source map, and copied map. -/
theorem window_order :
    let target:=resultBank (withMotif A 0) node true
    let src:=HistoryPartyPair.atPair (rawArm A winner.val).party node
    target 0+V≤target 1 ∧ target 1+V≤ src 0 ∧ src 0+V≤ src 1 ∧ src 1+V≤ src 2 ∧ src 2+V≤ src 3 := by
  let f:=F₀
  let t:=fun k:ℕ=>(⟨2,0,3,k⟩:Local)
  let s:=fun k:ℕ=>(⟨2,winner.val+2,2,k⟩:Local)
  have step (x y : Local) (lt : sector family.motifs family.parties x<sector family.motifs family.parties y) :
      f x+V≤f y := by
    let ix:=node*V+sector family.motifs family.parties x
    let iy:=node*V+sector family.motifs family.parties y
    have l:ix+1≤ iy:=by dsimp [ix,iy]; omega
    have eq:=Nat.mul_le_mul_right V l
    rw [Nat.add_one_mul] at eq
    change base u 12+ix*V+0+V≤base u 12+iy*V+0
    omega
  change f (t 0)+V≤f (t 1) ∧ f (t 1)+V≤f (s 0) ∧ f (s 0)+V≤f (s 1) ∧ f (s 1)+V≤f (s 2) ∧ f (s 2)+V≤f (s 3)
  exact ⟨step _ _ (by simp [sector,t]),step _ _ (by simp [sector,t,s]; omega),
    step _ _ (by simp [sector,s]),step _ _ (by simp [sector,s]),step _ _ (by simp [sector,s])⟩

end Arena

section RootOrder
variable (A : HistoryGatherBody.Layout) (node : ℕ) (winner : Fin A.party.parties)
  (L : Tree F a) (R : Tree F b) (wire : Fin (a+b)→BitSource 0 p) (id : ((Fin 3→Bool)→F)→ℕ) (mem : Memory W)
local notation "C" => withMotif A 0
local notation "src" => HistoryPartyPair.atPair (rawArm A winner.val).party node
local notation "dst" => resultBank C node true
local notation "H" => groupHub C mem true node p 0 1
local notation "B" => groupBuild C true H mem
local notation "V" => A.party.V
local notation "q" => fun _ : Fin 1=>rootHeader A node winner (a+b) p
local notation "N" => fun _ : Fin 1=>(pair L R).compile
local notation "mp" => fun _ : Fin 1=>wire
local notation "ops" => Tape.tape (W:=W) N mp id q

/-- The scalar layout of the physical S12, S14, S15 and S16 bank groups. -/
structure RootOrder : Prop where
  lane₀ : dst 0+V≤dst 1
  lane₁ : dst 1+V≤ src 0
  lane₂ : src 0+V≤ src 1
  lane₃ : src 1+V≤ src 2
  lane₄ : src 2+V≤ src 3
  front : src 3+V≤A.party.seed
  header : A.party.seed+64+7+7*A.party.parties≤A.party.commands
  commands : A.party.commands+14≤A.party.arguments
  wide : A.party.arguments+7<2^W
  minWidth : 16≤V
  pins : a+b≤V
  gates : 4*(pair L R).compile.cells≤V
  bits : L.bits+R.bits<2^W

set_option maxHeartbeats 1500000 in
omit [CommRing F] in
theorem ordered_charts (order : RootOrder A node winner L R (W:=W)) :
    RootBanksRoom A node winner L R (p:=p) mem ∧
    RootStay A node winner L R wire id mem ∧ RootSourceRoom A node winner L R wire id mem := by
  let x₀:=dst 0
  let x₁:=dst 1
  let y₀:=src 0
  let y₁:=src 1
  let y₂:=src 2
  let y₃:=src 3
  let g:=4*(pair L R).compile.cells
  let r:=a+b
  let c:=A.party.commands
  let arg:=A.party.arguments
  let s:=A.party.seed
  let u:=s+64
  let link:=u+7
  let mapArg:=u+7+4*A.party.parties
  obtain ⟨l₀,l₁,l₂,l₃,l₄,front,header,commandRoom,wide,positive,pins,gates,bits⟩:=order
  change x₀+V≤x₁ at l₀
  change x₁+V≤y₀ at l₁
  change y₀+V≤y₁ at l₂
  change y₁+V≤y₂ at l₃
  change y₂+V≤y₃ at l₄
  change y₃+V≤ s at front
  change u+7+7*A.party.parties≤c at header
  change c+14≤arg at commandRoom
  change arg+7<2^W at wide
  change r≤V at pins
  change g≤V at gates
  have np:=winner.isLt
  have linkEq:link=u+7:=rfl
  have mapEq:mapArg=u+7+4*A.party.parties:=rfl
  have uEq:u=s+64:=rfl
  have control : (B).control.val=s+7:=Fin.val_cast_of_lt (by change s+7<2^W;omega)
  let live (x:ℕ):= (y₀≤x ∧ x<y₀+g) ∨ (y₁≤x ∧ x<y₁+4) ∨ (y₂≤x ∧ x<y₂+r)
  let region (x:ℕ):= (u≤x ∧ x<u+7) ∨ (link≤x ∧ x<link+4) ∨ (mapArg≤x ∧ x< mapArg+3) ∨ live x
  have win (x : ℕ) : winnerAddress A node winner L R x↔live x:=Iff.rfl
  have reg (x : ℕ) : rootAddress A node winner L R (p:=p) mem x↔region x:=Iff.rfl
  have jobRange (j) (inTape : j∈ops) : (j.start=y₃ ∧ j.finish=y₃+r) ∨ (j.start=x₀ ∧ j.finish=x₀+g) := by
    have singleton : List.finRange 1=[0]:=by decide
    simp only [Tape.tape,singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil,Tape.jobs,
      List.mem_cons,List.not_mem_nil,or_false] at inTape
    rcases inTape with rfl|rfl
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  have safe (x : ℕ) (h : x< s+7 ∨ s+7<x) (map : x<y₃ ∨ y₃+r≤x) (row : x<x₀ ∨ x₀+g≤x) :
      (B).protectedAt N q x := by
    refine ⟨by rw [control];omega,fun i=>⟨map,row⟩⟩
  have encodedRows : (pair L R).compile.cells=L.rows+R.rows:=pair_cells L R
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro x h
      have := (reg x).1 h
      change _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ at this
      rcases this with z|z|z|z|z|z <;>
        constructor <;> first | (change x< s ∨ s+9≤x;omega) | (change x<c ∨ c+14≤x;omega) | (change x<arg ∨ arg+7≤x;omega)
    · intro x h
      have z:=(win x).1 h
      rw [HistoryMotifJoin.rows_len]
      change x<u ∨ u+(7+7*A.party.parties)≤x
      rcases z with z|z|z <;> omega
    · intro j
      fin_cases j <;> first | (change y₁<2^W;omega) | (change y₃<2^W;omega) | (change 10<2^W;omega) | (change mapArg<2^W;omega)
    · intro j
      fin_cases j <;> first | (change y₀<2^W;omega) | (change r<2^W;omega) | (change L.rows+R.rows<2^W;dsimp [g] at gates;omega) | exact bits
    · change mapArg+4<2^W;omega
    · intro side j
      exact safe (c+(7*side.toNat+j.val)) (.inr (by omega)) (.inr (by omega))
        (.inr (by omega))
    · intro j
      exact safe (arg+j.val) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))
    · intro j
      exact safe (mapArg+j.val) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))
    · intro i j
      have hi:=i.isLt
      have hj:=j.isLt
      have off:4*i.val+j.val<g:=by dsimp [g];omega
      exact safe (y₀+(4*i.val+j.val)) (.inl (by omega)) (.inl (by omega)) (.inr (by omega))
    · intro j
      have hj:j.val<r:=j.isLt
      exact safe (y₂+j.val) (.inl (by omega)) (.inl (by omega)) (.inr (by omega))
  · have stay (x : ℕ) (reg : (u≤x ∧ x<u+7) ∨ x=link ∨ (y₁≤x ∧ x<y₁+4)) :
        x≠(B).control.val ∧ ∀ j∈ops,x<j.start ∨ j.finish≤x := by
      rw [control]
      refine ⟨by rcases reg with z|z|z <;> omega,?_⟩
      intro j hj
      rcases jobRange j hj with z|z <;> rcases reg with h|h|h <;> omega
    refine ⟨fun j=>stay _ (.inl (by change u≤u+j.val ∧ u+j.val<u+7;have:=j.isLt;omega)),
      fun j=>stay _ (.inr (.inr (by change y₁≤y₁+j.val ∧ y₁+j.val<y₁+4;have:=j.isLt;omega))),
      stay _ (.inr (.inl rfl))⟩
  · constructor
    · omega
    · omega
    · change s+9<2^W;omega
    · change u+7<2^W;omega
    · change s+9≤c ∧ c+14≤arg;omega
    · change c+14<2^W;omega
    · exact wide
    · change link+4≤2^W;omega
    · change y₁+3<2^W;omega
    · change x₁+4<2^W;omega
    · intro x hx
      have z:=(reg x).1 hx
      change _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ at z
      change x<x₁ ∨ x₁+4≤x
      rcases z with h|h|h|h|h|h <;> omega
    · constructor <;> intro j hj <;> rcases jobRange j hj with z|z <;> first | (change j.finish≤ s ∨ s+9≤j.start;omega) | (change j.finish≤c ∨ c+14≤j.start;omega)
    · intro j hj
      rcases jobRange j hj with z|z <;> omega

end RootOrder

section PhysicalOrder
open HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
variable (u : ℕ) (arch : HistoryStageBody.Physical.Archive) (f : Family) (node : ℕ) (winner : Fin f.parties)
local notation "A" => layout u arch f
local notation "V" => volume u
local notation "W₀" => 16*u^10

omit [CommRing F] in
/-- The real S12/S14/S15/S16 placement establishes the entire scalar chart of a refresh root.
Only the size of the elected compiled tree and the template dimensions enter the bound. -/
theorem physical_root_order (L : Tree F a) (R : Tree F b)
    (age : 16≤u) (count : node<V^2) (posM : 0<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (pins : a+b≤V) (gates : 4*(pair L R).compile.cells≤V) (bits : L.bits+R.bits<2^W₀) :
    RootOrder A node winner L R (W:=W₀) := by
  have pages:=window_order u arch f node winner
  obtain ⟨p₀,p₁,p₂,p₃,p₄⟩:=pages
  let sx:Local:=⟨2,winner.val+2,2,3⟩
  have good : sx.Valid f.motifs f.parties := by
    change 2<f.motifs+2 ∧ winner.val+2<f.parties+2 ∧ 2<8 ∧ 3<32
    exact ⟨by omega,Nat.add_lt_add_right winner.isLt 2,by decide,by decide⟩
  have place:=local_window u f node age count capacity sx good
  have fits₁:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<14)
  have fits₂:=Diagonal.TickWorkspace.apart (u:=u) (by decide:14<15)
  have fits₃:=Diagonal.TickWorkspace.apart (u:=u) (by decide:15<16)
  have orderP : f.parties≤V:=by
    have h:f.parties+2≤(f.motifs+2)*(f.parties+2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have exp : 10≤u^10 := (show 10≤u by omega).trans (Nat.le_self_pow (by decide) _)
  have big : 1024≤V:=by exact Nat.pow_le_pow_right (by decide : 0<2) exp
  have power : 10*V≤V^4:=calc
    _≤V*V := Nat.mul_le_mul_right _ (by omega)
    _=V^2 := (pow_two V).symm
    _≤V^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have total : V+64+7+7*f.parties≤Diagonal.TickWorkspace.stride u := by change _≤V^4;omega
  have w:=word_space (i:=16) (by omega : 1≤u) (by change 16<V^4;omega)
  refine ⟨p₀,p₁,p₂,p₃,p₄,?_,?_,?_,?_,big.trans' (by decide),pins,gates,bits⟩
  · change atWord (base u 12) V f.motifs f.parties node sx 0+V≤base u 14+V
    exact place.2.1.trans (fits₁.trans (Nat.le_add_right _ _))
  · change (base u 14+V)+64+7+7*f.parties≤base u 15
    omega
  · change base u 15+14≤base u 16
    have : 14≤Diagonal.TickWorkspace.stride u := by change 14≤V^4;omega
    omega
  · change base u 16+7<2^W₀
    have : 7≤Diagonal.TickWorkspace.stride u := by change 7≤V^4;omega
    omega

/-- A word of an elected input sector is disjoint from every four-word record of
another physical sector of the same chart. -/
private theorem local_away (_age : 16≤u) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (x y : Local) (validX : x.Valid f.motifs f.parties) (validY : y.Valid f.motifs f.parties) (ne : x≠y)
    (k z : ℕ) (low : atWord (base u 12) V f.motifs f.parties node x 0≤k)
    (high : k<atWord (base u 12) V f.motifs f.parties node x 0+V) (len : z≤V) :
    k<atWord (base u 12) V f.motifs f.parties node y 0 ∨
    atWord (base u 12) V f.motifs f.parties node y 0+z≤k := by
  have h:=local_apart («V»:=V) (base:=base u 12) (n:=node) (Nat.two_pow_pos _) capacity validX validY ne
  rcases h with e|e
  · exact Or.inl (high.trans_le e)
  · exact Or.inr ((Nat.add_le_add_left len _).trans (e.trans low))

omit [CommRing F] in
/-- A vacant party can never overwrite the previously emitted pair stream, four-word
header or typed gather map of the elected party, including at either end of the roster. -/
theorem physical_vacant_away (j : Fin f.parties) (other : j≠winner) (id : ((Fin 3→Bool)→F)→ℕ)
    (mem : Memory W₀) (room : VacantRoom (rawArm A j.val) node id mem)
    (L : Tree F a) (R : Tree F b) (age : 16≤u) (posM : 0<f.motifs) (nodeRoom : node<V^2)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (gates : 4*(pair L R).compile.cells≤V) (pins : a+b≤V)
    (k : ℕ) (live : winnerAddress A node winner L R k) : VacantAway (rawArm A j.val) node id mem k := by
  let J:=rawArm A j.val
  let X:=vacantChecks J.party mem
  let Y:=vacantPayload J.party mem
  let P:=HistoryPartyPairExec.build J.party node 0 0 (Y.published [])
  let loc:=fun (p : Fin f.parties) (family bank : ℕ)=>(⟨2,p.val+2,family,bank⟩:Local)
  let page:=fun (x : Local)=>atWord (base u 12) V f.motifs f.parties node x 0
  have ok (p : Fin f.parties) (t z : ℕ) (vt:t<8) (vz:z<32): (loc p t z).Valid f.motifs f.parties := by
    change 2<f.motifs+2 ∧ p.val+2<f.parties+2 ∧ t<8 ∧ z<32
    exact ⟨by omega,Nat.add_lt_add_right p.isLt 2,vt,vz⟩
  have v16 : 16≤V:=age.trans ((Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le)
  have source : ∃ x:Fin 3,page (loc winner 2 x.val)≤k ∧ k<page (loc winner 2 x.val)+V := by
    change (_≤k ∧ k<_+4*(pair L R).compile.cells) ∨ (_≤k ∧ k<_+4) ∨ (_≤k ∧ k<_+(a+b)) at live
    rcases live with term|term|term
    · exact ⟨0,term.1,term.2.trans_le (Nat.add_le_add_left gates _)⟩
    · exact ⟨1,term.1,term.2.trans_le (Nat.add_le_add_left (by omega : 4≤V) _)⟩
    · exact ⟨2,term.1,term.2.trans_le (Nat.add_le_add_left pins _)⟩
  obtain ⟨n,low,high⟩:=source
  have valid:=ok winner 2 n.val (by decide) (by have:=n.isLt;omega)
  have win:=local_window u f node age nodeRoom capacity (loc winner 2 n.val) valid
  have below : k<base u 12+Diagonal.TickWorkspace.stride u:=high.trans_le win.2.1
  have away (t:ℕ) (ht:t<8) : k<page (loc j t 1) ∨ page (loc j t 1)+4≤k := by
    apply local_away u f node age capacity _ _ valid (ok j t 1 ht (by decide)) _ _ _ low high (by omega)
    intro e
    have v:=congrArg Local.party e
    change winner.val+2=j.val+2 at v
    exact other (Fin.ext (by omega))
  have b14:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<14)
  have b15:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<15)
  have b16:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<16)
  have b17:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<17)
  have wSeed:base u 14+V+37<2^W₀:=room.checks.seedRoom
  have cursor : ((base u 14+V+33:ℕ):Word W₀).val=base u 14+V+33:=Fin.val_cast_of_lt (by omega)
  have c : ((base u 14+V+7:ℕ):Word W₀).val=base u 14+V+7:=Fin.val_cast_of_lt (by omega)
  have xRoot : X.target=page (loc j 1 1) :=
    congrArg (fun idx => dest J.party true idx 1) room.before
  have yRoot : Y.target=page (loc j 0 1) :=
    congrArg (fun idx => dest J.party false idx 1) room.between
  have pRoot : P.outputBase=page (loc j 2 1):=vacant_output_base J node id mem room
  have setup (Z : HistoryPartyBatchExec.Build W₀) (same : Z.layout=J.party) (range : k<Z.target ∨ Z.target+4≤k) :
      BatchAway Z [] k := by
    constructor
    · rw [HistoryPartyBatchExec.Build.ctrl,same]
      change k≠((base u 14+V+33:ℕ):Word W₀).val;rw [cursor];omega
    · rw [same];left;change k<base u 14+V;omega
    · rw [same];left;change k<base u 14+2*V;omega
    · rw [same];left;exact lt_of_lt_of_le below b15
    · rw [same];left;exact lt_of_lt_of_le below b16
    · simp
    · exact range
  refine ⟨Or.inl (lt_of_lt_of_le below b17),setup X rfl (by rw [xRoot]; exact away 1 (by decide)),
    setup Y rfl (by rw [yRoot]; exact away 0 (by decide)),?_,?_,?_⟩
  · constructor
    · left;change k<base u 14+V;omega
    · left;exact below.trans_le b15
    · left;exact below.trans_le b16
    · change k≠((base u 14+V+7:ℕ):Word W₀).val;rw [c];omega
    · intro job hj
      have z:=empty_pair_jobs J node id job hj
      change k<job.start ∨ job.start+job.count≤k
      omega
  · left;change k<(base u 14+V)+64;omega
  · change k<P.outputBase ∨ P.outputBase+4≤k
    rw [pRoot]
    exact away 2 (by decide)

omit [CommRing F] in
/-- The S17 port materializer and the elected S12 map leave the occupied pair's rows and
four-word summary resident, regardless of the lengths of the individual source scans. -/
theorem physical_gather_away (L : Tree F a) (R : Tree F b) (plan : HistoryGatherExecution.Plan W₀)
    (age : 16≤u) (count : node<V^2) (posM : 0<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (gates : 4*(pair L R).compile.cells≤V)
    (mapBase : plan.gatherBase=HistoryPartyPair.atPair (rawArm A winner.val).party node 2) :
    ∀ k,let src:=HistoryPartyPair.atPair (rawArm A winner.val).party node
    (src 0≤k ∧ k< src 0+4*(pair L R).compile.cells) ∨ (src 1≤k ∧ k< src 1+4) →
    let J:=rawArm A winner.val
    (k<J.temp ∨ J.temp+(HistoryGatherBody.fields (W:=W₀) J).length≤k) ∧
    (∀ q j,j<HistoryGatherExecution.cap J q→k<HistoryGatherBody.srcBase J q j ∨
      HistoryGatherBody.srcBase J q j+plan.width q j≤k) ∧ (k<plan.gatherBase ∨ plan.gatherBase+plan.gatherCount≤k) := by
  intro k src range J
  have v16 : 16≤V:=age.trans ((Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le)
  have ⟨_,_,ord₀,ord₁,_⟩:=window_order u arch f node winner
  change src 0+V≤ src 1 at ord₀
  change src 1+V≤ src 2 at ord₁
  have lower:k< src 2:=by
    change (src 0≤k ∧ k< src 0+4*(pair L R).compile.cells) ∨ (src 1≤k ∧ k< src 1+4) at range
    rcases range with h|h <;> omega
  have winPage : (⟨2,winner.val+2,2,2⟩ : Local).Valid f.motifs f.parties := by
    change 2<f.motifs+2 ∧ winner.val+2<f.parties+2 ∧ 2<8 ∧ 2<32
    exact ⟨by omega,Nat.add_lt_add_right winner.isLt 2,by decide,by decide⟩
  have window:=local_window u f node age count capacity _ winPage
  have place:src 2+V≤base u 12+Diagonal.TickWorkspace.stride u:=window.2.1
  have high:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<17)
  have beforeTemp : k < base u 17 :=
    lower.trans_le ((Nat.le_add_right (src 2) V).trans (place.trans high))
  refine ⟨Or.inl beforeTemp, ?_, Or.inl (by rw [mapBase]; exact lower)⟩
  intro q j _
  left
  change k < base u 17 + _
  exact beforeTemp.trans_le (Nat.le_add_right _ _)

/-- Instantiate the empty batch's complete seven-stage source in the physical layout.
The only immutable reads before the zero sentinel are the selected node and its
single incident. The archive contributes its two base addresses and its two strides. -/
theorem physical_vacant_source_at (g : ℕ) (j : Fin f.parties) (ck : Bool) (mem : Memory W₀)
    (age : 16≤u) (count : node<V^2) (motifs : g<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (cursor : numeric mem (rawParty A g j.val).party.cursor-1=node)
    (flag : ¬occupied (rawParty A g j.val).party (numeric mem))
    (probes : ∀ x,HistoryPartyBootExec.SeedRead (rawParty A g j.val).party ck (numeric mem) x→
      (x<base u 14+V ∨ base u 14+V+37≤x) ∧ x<2^W₀)
    (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts) :
    (⟨(rawParty A g j.val).party,ck,emptyKind,mem⟩:HistoryPartyBatchExec.Build W₀).Source [] := by
  let J:=(rawParty A g j.val).party
  let loc:=fun k:ℕ=>(⟨g+2,j.val+2,ck.toNat,k⟩:Local)
  let page:=fun k:ℕ=>atWord (base u 12) V f.motifs f.parties node (loc k) 0
  have pageFit (k:ℕ) (hk:k<32) : base u 12≤page k ∧ page k+V≤base u 12+Diagonal.TickWorkspace.stride u ∧ page k+V<2^W₀ := by
    apply local_window u f node age count capacity (loc k)
    change g+2<f.motifs+2 ∧ j.val+2<f.parties+2 ∧ ck.toNat<8 ∧ k<32
    exact ⟨Nat.add_lt_add_right motifs 2,Nat.add_lt_add_right j.isLt 2,by cases ck <;> decide,hk⟩
  have ptr (k : ℕ) : dest J ck (numeric mem J.cursor-1) k=page k:=by rw [cursor];rfl
  have v₁ : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have big : 10*V≤V^4:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have s:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<15)
  have cmd:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 15<16)
  have earlier:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have after_:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 16<18)
  have high:=word_space (i:=18) (by omega : 1≤u) (by change 18<V^4;omega)
  change base u 14+V^4≤base u 15 at s
  change base u 15+V^4≤base u 16 at cmd
  change base u 16+V^4≤base u 18 at after_
  change base u 18+V^4<2^W₀ at high
  have seed : J.seed+37<2^W₀:=by change base u 14+V+37<_;omega
  apply vacant_source J ck mem flag seed
  · change base u 14+2*V+26<_;omega
  · change base u 14+V+37≤base u 14+2*V;omega
  · change base u 14+2*V+26≤base u 15;omega
  · change base u 15≤base u 16;omega
  · change base u 16<_;omega
  · omega
  · change g<2^W₀;have h:=Nat.le_mul_of_pos_right (f.motifs+2) (by omega : 0<f.parties+2);omega
  · exact probes
  · intro _
    exact (Nat.pow_le_pow_right (by decide : 0<2) j.isLt.le).trans_lt mask
  · intro i
    have root := (pageFit 0 (by decide)).2.2
    have account:dest J ck (numeric mem J.cursor-1) 0<2^W₀:=by rw [ptr];omega
    change (registers J ck (numeric mem)).words i<_
    simp only [registers]
    fin_cases i <;> first
      | exact account | exact lutStride | exact pages | exact pageStride
      | (change base u 16<_;omega)
      | (change base u 18+5*V<_;omega)
      | (change (if occupied J (numeric mem) then incident J (numeric mem) else J.seed+15)<_
         rw [ite_eq_right (show ¬occupied J (numeric mem) from flag)]
         change base u 14+V+15<_
         omega)
      | (change (if occupied J (numeric mem) then shape J (numeric mem) else J.seed+21)<_
         rw [ite_eq_right (show ¬occupied J (numeric mem) from flag)]
         change base u 14+V+21<_
         omega)
      | (change base u 14+V+1<_;omega)
      | (change arch.lut<_;omega)
      | (change arch.counts<_;omega)
  · exact lookup
  · exact counts
  · exact lutAway
  · exact countsAway
  · change dest J ck (numeric mem J.cursor-1) 1+4<2^W₀
    rw [ptr];have h:=(pageFit 1 (by decide)).2.2;omega
  · left
    change dest J ck (numeric mem J.cursor-1) 1+4≤base u 14+V
    rw [ptr];have h:=(pageFit 1 (by decide)).2.1;omega

theorem physical_vacant_source (j : Fin f.parties) (ck : Bool) (mem : Memory W₀)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (cursor : numeric mem (rawArm A j.val).party.cursor-1=node)
    (flag : ¬occupied (rawArm A j.val).party (numeric mem))
    (probes : ∀ x,HistoryPartyBootExec.SeedRead (rawArm A j.val).party ck (numeric mem) x→
      (x<base u 14+V ∨ base u 14+V+37≤x) ∧ x<2^W₀)
    (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts) :
    (⟨(rawArm A j.val).party,ck,emptyKind,mem⟩:HistoryPartyBatchExec.Build W₀).Source [] :=
  physical_vacant_source_at u arch f node 0 j ck mem age count motifs capacity cursor flag probes mask lookup lutStride pages pageStride counts lutAway countsAway

section PairPlacement
open HistoryPartyPairExec
variable (g : ℕ) (j : Fin f.parties) (L : Tree F a) (R : Tree F b)
  (id : ((Fin 3→Bool)→F)→ℕ) (mem : Memory (16*u^10))
local notation "J" => (rawParty A g j.val).party
local notation "N" => pairNetwork L R
local notation "Q" => HistoryPartyPairExec.copyHeader J node L R
local notation "P" => HistoryPartyPairExec.build J node a b mem
local notation "ops" => HistoryPartyPairExec.steps (w:=W₀) J node L R id
local notation "root" => HistoryPartyPair.atPair J node

omit [CommRing F] in
private theorem pair_job (x : HistoryReadyTape.Job W₀) (valid:x∈ops) :
    ∃ i:Fin 2,(x.start=(Q i).pins ∧ x.finish=(Q i).pins+pairArity L R i) ∨
      (x.start=(Q i).dest ∧ x.finish=(Q i).dest+4*(N i).cells) := by
  obtain ⟨i,_,hin⟩:=List.mem_flatMap.mp valid
  refine ⟨i,?_⟩
  rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using hin :
    x=⟨(Q i).pins,pairArity L R i,_⟩ ∨ x=⟨(Q i).dest,4*(N i).cells,_⟩) with rfl|rfl
  · exact .inl ⟨rfl,rfl⟩
  · exact .inr ⟨rfl,rfl⟩

omit [CommRing F] in
private theorem pair_place (i : Fin 2) :
    (Q i).pins≥(J).maps ∧ (Q i).pins+pairArity L R i≤(J).maps+(a+b) ∧
    root 0≤(Q i).dest ∧ (Q i).dest+4*(N i).cells≤root 0+4*(L.rows+R.rows) ∧
    (Q i).source=dest J (decide (i=0)) node 0+4*(N i).cells ∧
    (N i).cells≤L.rows+R.rows := by
  have leftRows : (N (0:Fin 2)).cells=L.rows := by
    change L.compile.cells=L.rows
    exact compiled_rows L
  have rightRows : (N (1:Fin 2)).cells=R.rows := by
    change R.compile.cells=R.rows
    exact compiled_rows R
  have h0 : before (fun k=>(N k).cells) (0:Fin 2)=0 := by simp [before]
  have h1 : before (fun k=>(N k).cells) (1:Fin 2)=L.rows := by
    simpa [before,Fin.sum_univ_one] using leftRows
  have first (k : Fin 2) : root 0≤(Q k).dest := Nat.le_add_right _ _
  fin_cases i
  · refine ⟨le_rfl,?_,first 0,?_,rfl,?_⟩
    · change (J).maps+a≤(J).maps+(a+b)
      omega
    · change root 0+4*before (fun k=>(N k).cells) 0+4*(N 0).cells≤_
      rw [h0,leftRows]
      omega
    · exact leftRows.le.trans (Nat.le_add_right _ _)
  · refine ⟨?_,?_,first 1,?_,rfl,?_⟩
    · change (J).maps≤(J).maps+a
      exact Nat.le_add_right _ _
    · change ((J).maps+a)+b≤(J).maps+(a+b)
      omega
    · change root 0+4*before (fun k=>(N k).cells) 1+4*(N 1).cells≤_
      rw [h1,rightRows]
      omega
    · exact rightRows.le.trans (Nat.le_add_left _ _)

omit [CommRing F] in
/-- Physical source and header certificate of the two-child pair, valid for both the
elected batch and the vacant pair. Row jobs lie in S12 and map jobs lie in S18. -/
theorem physical_pair_source_at (age : 16≤u) (count : node<V^2) (motifs : g<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (pins : a+b≤V) (rows : 4*(L.rows+R.rows)≤V)
    (cursor : numeric mem (J).cursor-1=node) :
    BootRoom J mem node ∧ PairSourceRoom J node L R id (W:=W₀) := by
  let loc:=fun (family bank:ℕ)=>(⟨g+2,j.val+2,family,bank⟩:Local)
  let page:=fun (k n:ℕ)=>atWord (base u 12) V f.motifs f.parties node (loc k n) 0
  have ok (k n:ℕ) (ks:k<8) (ns:n<32) : (loc k n).Valid f.motifs f.parties := by
    change g+2<f.motifs+2 ∧ j.val+2<f.parties+2 ∧ k<8 ∧ n<32
    exact ⟨by omega,by have:=j.isLt;omega,ks,ns⟩
  have room (k n:ℕ) (ks:k<8) (ns:n<32) := local_window u f node age count capacity _ (ok k n ks ns)
  have v₁ : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have big : 10*V≤V^4:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have s12:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have s14:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<15)
  have s15:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 15<16)
  have s16:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 16<18)
  have words:=word_space (i:=18) (by omega : 1≤u) (by change 18<V^4;omega)
  change base u 14+V^4≤base u 15 at s14
  change base u 15+V^4≤base u 16 at s15
  change base u 16+V^4≤base u 18 at s16
  change base u 18+V^4<2^W₀ at words
  have zone (k n:ℕ) (ks:k<8) (ns:n<32) : page k n+V≤base u 14:=(room k n ks ns).2.1.trans s12
  have hl : (link J node a 0).node=page 1 1:=rfl
  have hr : (link J node a 1).node=page 0 1:=rfl
  have childBelow (i:Fin 2) : (link J node a i).node+V≤base u 14:=by
    fin_cases i <;> first | exact zone 1 1 (by decide) (by decide) | exact zone 0 1 (by decide) (by decide)
  have separate (i:Fin 2) : (link J node a i).node+V≤root 1 ∨ root 1+V≤(link J node a i).node:=by
    fin_cases i
    · exact local_apart (base:=base u 12) (n:=node) (Nat.two_pow_pos _) capacity
        (ok 1 1 (by decide) (by decide)) (ok 2 1 (by decide) (by decide)) (fun e=>by
          have h:=congrArg Local.family e;change (1:ℕ)=2 at h;omega)
    · exact local_apart (base:=base u 12) (n:=node) (Nat.two_pow_pos _) capacity
        (ok 0 1 (by decide) (by decide)) (ok 2 1 (by decide) (by decide)) (fun e=>by
          have h:=congrArg Local.family e;change (0:ℕ)=2 at h;omega)
  have y : root 1+V≤base u 14:=zone 2 1 (by decide) (by decide)
  have z : root 0+V≤base u 14:=zone 2 0 (by decide) (by decide)
  have hL : dest J true node 1+V≤base u 14:=childBelow 0
  have hR : dest J false node 1+V≤base u 14:=childBelow 1
  have seed : (J).seed=base u 14+V:=rfl
  have hup : HistoryPartyPair.hub J=base u 14+V+64:=rfl
  have maps : (J).maps=base u 18+5*V:=rfl
  have job (x : HistoryReadyTape.Job W₀) (v:x∈ops) :
      (base u 18+5*V≤x.start ∧ x.finish≤base u 18+6*V) ∨ x.finish≤base u 14:=by
    obtain ⟨i,tr|tr⟩:=pair_job u arch f node g j L R id x v <;> have place:=pair_place u arch f node g j L R i
    · left;rw [tr.1,tr.2];rcases place with ⟨lo,hi,_⟩;rw [maps] at lo hi;omega
    · right;rw [tr.2];have:=place.2.2.2.1;omega
  refine ⟨⟨by change base u 18<_;omega,cursor,by rw [hup];omega,by omega,by omega,
    .inr (by change _≤base u 18;rw [hup];omega),.inl (by rw [hup];omega),.inl (by rw [hup];omega)⟩,?_⟩
  refine ⟨by rw [seed];omega,?_,?_,?_,?_,by omega,?_,?_,⟨?_,?_⟩,?_⟩
  · change base u 14+V+9≤base u 15 ∧ base u 15+28≤base u 16;omega
  · change base u 15+28<_;omega
  · change base u 16+14<_;omega
  · intro i;have:=childBelow i;omega
  · right;rw [hup];omega
  · intro i;have:=separate i;omega
  · intro x hx;have h:=job x hx;rw [seed];omega
  · intro x hx;have h:=job x hx;change _≤base u 15 ∨ base u 15+28≤_;omega
  · intro x hx;have h:=job x hx;omega

omit [CommRing F] in
/-- S12 source rows begin after each child's leaf staging buffer. The two separate
batch families, the pair family and the S18 affine pin maps give the full frame. -/
theorem physical_pair_room_at (age : 16≤u) (count : node<V^2) (motifs : g<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (pins : a+b≤V)
    (rows : 8*(L.rows+R.rows)≤V) (bits : L.bits+R.bits<2^W₀)
    («meta» : ∀ i k t,HistoryCompiledRows.metadata id (N i) k t<2^W₀)
    (cursor : numeric mem (J).cursor-1=node) : PairRoom J node L R id mem := by
  let loc:=fun (family bank:ℕ)=>(⟨g+2,j.val+2,family,bank⟩:Local)
  let page:=fun k b=>atWord (base u 12) V f.motifs f.parties node (loc k b) 0
  let fam:=fun i:Fin 2=>(decide (i=0)).toNat
  have fok (i:Fin 2) : fam i<2:=by fin_cases i <;> decide
  have ok (k n:ℕ) (ks:k<8) (ns:n<32) : (loc k n).Valid f.motifs f.parties := by
    change g+2<f.motifs+2 ∧ j.val+2<f.parties+2 ∧ k<8 ∧ n<32
    exact ⟨by omega,by have:=j.isLt;omega,ks,ns⟩
  have boot:=physical_pair_source_at u arch f node g j L R id mem age count motifs capacity pins (by omega) cursor
  have v₁ : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have grow : 10*V≤V^4:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have p12:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have p14:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<15)
  have p15:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 15<16)
  have p16:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 16<18)
  have words:=word_space (i:=18) (by omega : 1≤u) (by change 18<V^4;omega)
  change base u 14+V^4≤base u 15 at p14
  change base u 15+V^4≤base u 16 at p15
  change base u 16+V^4≤base u 18 at p16
  change base u 18+V^4<2^W₀ at words
  have below (k n:ℕ) (ks:k<8) (ns:n<32) : page k n+V≤base u 14 :=
    (local_window u f node age count capacity _ (ok k n ks ns)).2.1.trans p12
  have pair0 : root 0+V≤base u 14:=below 2 0 (by decide) (by decide)
  have pair1 : root 1+V≤base u 14:=below 2 1 (by decide) (by decide)
  have c0 : dest J true node 0+V≤base u 14:=below 1 0 (by decide) (by decide)
  have c1 : dest J true node 1+V≤base u 14:=below 1 1 (by decide) (by decide)
  have p0 : dest J false node 0+V≤base u 14:=below 0 0 (by decide) (by decide)
  have p1 : dest J false node 1+V≤base u 14:=below 0 1 (by decide) (by decide)
  have source0 (i:Fin 2) : (Q i).source=page (fam i) 0+4*(N i).cells:=rfl
  have child1 (i:Fin 2) : (link J node a i).node=page (fam i) 1:=by fin_cases i <;> rfl
  have both (i:Fin 2) (bank:ℕ) (bk:bank<32) : page (fam i) bank+V≤root 0 ∨ root 0+V≤page (fam i) bank:=
    local_apart (base:=base u 12) (n:=node) (Nat.two_pow_pos _) capacity
      (ok (fam i) bank ((fok i).trans (by decide)) bk) (ok 2 0 (by decide) (by decide))
      (fun e=>by have k:=congrArg Local.family e;change fam i=2 at k;have:=fok i;omega)
  have sm (i:Fin 2) : (N i).cells≤L.rows+R.rows:=(pair_place u arch f node g j L R i).2.2.2.2.2
  have src (i:Fin 2) : (Q i).source+4*(N i).cells≤base u 14:=by
    rw [source0];have:=below (fam i) 0 ((fok i).trans (by decide)) (by decide);have:=sm i;omega
  have nodeIn (i:Fin 2) : (link J node a i).node+4≤base u 14:=by
    rw [child1];have:=below (fam i) 1 ((fok i).trans (by decide)) (by decide);omega
  have hseed : (J).seed=base u 14+V:=rfl
  have hub : HistoryPartyPair.hub J=base u 14+V+64:=rfl
  have maps : (J).maps=base u 18+5*V:=rfl
  have cword : (P).control.val=base u 14+V+7 := by
    apply Fin.val_cast_of_lt (a := base u 14+V+7)
    omega
  have pin (i:Fin 2) : base u 18+5*V≤(Q i).pins ∧ (Q i).pins+pairArity L R i≤base u 18+6*V:=by
    have h:=pair_place u arch f node g j L R i
    rcases h with ⟨start,finish,_⟩;rw [maps] at start finish;omega
  have disk (i:Fin 2) : root 0≤(Q i).dest ∧ (Q i).dest+4*(N i).cells≤root 0+V:=by
    have h:=pair_place u arch f node g j L R i;rcases h with ⟨_,_,start,finish,_⟩;omega
  have old (i:Fin 2) : (Q i).oldPins≤a+b:=by fin_cases i <;> first | (change a≤_;omega) | (change b≤_;omega)
  have operand (i:Fin 2) (t:Fin 5) : base u 14+V+64≤(HistoryPartyPairExec.rows J a b i).arg+t.val ∧
      (HistoryPartyPairExec.rows J a b i).arg+t.val<base u 14+V+89:=by
    have ht:=t.isLt
    fin_cases i <;> first
      | (change _≤HistoryPartyPair.hub J+15+t.val ∧ HistoryPartyPair.hub J+15+t.val<_;rw [hub];omega)
      | (change _≤HistoryPartyPair.hub J+20+t.val ∧ HistoryPartyPair.hub J+20+t.val<_;rw [hub];omega)
  have outside (x:ℕ) (lo : x<base u 14 ∨ (base u 14+V+64≤x ∧ x<base u 14+V+89)) :
      Outside J x:=by
    exact ⟨by rw [hseed];omega,by change x<base u 15 ∨ base u 15+28≤x;omega,
      by change x<base u 16 ∨ base u 16+14≤x;omega⟩
  have safe (x:ℕ) (ctrl : x≠base u 14+V+7) (map : x<base u 18+5*V ∨ base u 18+6*V≤x)
      (stream : x<root 0 ∨ root 0+V≤x) : (P).protectedAt N Q x:=by
    refine ⟨by simpa only [cword] using ctrl,fun i=>?_⟩
    have h:=pin i;have d:=disk i;omega
  have writes (x:ℕ) (protectedAt : (P).protectedAt N Q x) :
      ∀ r∈ops,x<r.start ∨ r.finish≤x:=by
    intro r hr
    obtain ⟨i,h|h⟩:=pair_job u arch f node g j L R id r hr <;>
      have part:=protectedAt.2 i <;> rw [h.1,h.2] <;> tauto
  have keep (x:ℕ) (off : Outside J x) (safe_ : (P).protectedAt N Q x) : Retained J node L R id mem x :=
    ⟨off.seed,off.commands,off.arguments,safe_.1,writes x safe_⟩
  have lowSafe (x:ℕ) (low:x<base u 14) (disk:x<root 0 ∨ root 0+V≤x) : (P).protectedAt N Q x:=
    safe x (by omega) (.inl (by omega)) disk
  have wordSafe (x:ℕ) (lo:base u 14+V+64≤x) (hi:x<base u 16+15) : (P).protectedAt N Q x:=
    safe x (by omega) (.inl (by omega)) (.inr (by omega))
  have sourceSafe (i:Fin 2) (k:Fin (N i).cells) (t:Fin 4) :
      (P).protectedAt N Q ((Q i).source+(4*k.val+t.val)):=by
    have ksmall:=k.isLt;have tsmall:=t.isLt
    apply lowSafe _ (by have:=src i;omega)
    have eq:=source0 i;have := both i 0 (by decide);have:=sm i;omega
  have fixed (i:Fin 2) (t:Fin 4) : (P).protectedAt N Q ((link J node a i).node+t.val):=by
    have k:=t.isLt;have loc:=child1 i
    apply lowSafe _ (by have:=nodeIn i;omega)
    have sep:=both i 1 (by decide);omega
  have space : Space J node L R id mem:=by
    refine ⟨fun i=>by have:=pin i;omega,fun i k=>.inr (by have:=pin k;have:=disk i;omega),?_,?_,
      fun i=>by have:=src i;omega,fun i=>by have:=old i;omega,«meta»,by change _≤V;omega⟩
    · intro i;left;rw [cword];have:=pin i;omega
    · intro i;right;rw [cword];have:=disk i;omega
  have frozen : Frozen J node L R mem:=by
    refine ⟨?_,fun i t=>wordSafe _ (operand i t).1 (by have:=(operand i t).2;omega),?_,sourceSafe⟩
    · intro i side t
      have hi:=i.isLt;have ht:=t.isLt
      change (P).protectedAt N Q (base u 15+(14*i.val+7*side.toNat+t.val))
      cases side <;> apply wordSafe <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
    · intro i t;have hi:=i.isLt;have ht:=t.isLt
      change (P).protectedAt N Q (base u 16+(7*i.val+t.val));apply wordSafe <;> omega
  have cap (t:Fin 25) : fields J node a b t<2^W₀:=by
    fin_cases t <;> first
      | (change root 0<_;omega) | (change a+b<_;omega) | (change 0<_;omega) | (change 2<_;omega)
      | (change HistoryPartyPair.hub J+7<_;rw [hub];omega) | (change base u 16<_;omega) | (change root 1<_;omega)
      | (change dest J true node 1<_;omega) | (change dest J false node 1<_;omega)
      | (change (J).maps<_;rw [maps];omega) | (change (J).maps+a<_;rw [maps];omega)
      | (change HistoryPartyPair.hub J+15<_;rw [hub];omega) | (change HistoryPartyPair.hub J+20<_;rw [hub];omega)
      | (change 8<_;omega) | (change a<_;omega) | (change b<_;omega) | (change 2+a<_;omega)
  refine ⟨cursor,boot.1,boot.2,space,frozen,cap,boot.1.width,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i t;left;have:=nodeIn i;have:=t.isLt;rw [hub];omega
  · right;change (J).seed+9≤HistoryPartyPair.hub J+7;rw [hseed,hub];omega
  · intro i;left;rw [hseed];have:=nodeIn i;omega
  · left;change HistoryPartyPair.hub J+7+8≤base u 15;rw [hub];omega
  · intro i;left;change _≤base u 15;have:=nodeIn i;omega
  · intro i t;exact outside _ (.inr (operand i t))
  · intro i k t
    have lo : (Q i).source+(4*k.val+t.val)<base u 14:=by have:=src i;have:=k.isLt;have:=t.isLt;omega
    exact ⟨outside _ (.inl lo),.inl (by rw [hub];omega)⟩
  · intro t
    have ht:=t.isLt
    have lo:base u 14+V+64≤HistoryPartyPair.hub J+t.val:=by rw [hub];omega
    have hi:HistoryPartyPair.hub J+t.val<base u 14+V+89:=by rw [hub];omega
    exact keep _ (outside _ (.inr ⟨lo,hi⟩)) (wordSafe _ lo (by omega))
  · intro i t
    have lo : (link J node a i).node+t.val<base u 14:=by have:=nodeIn i;have:=t.isLt;omega
    exact keep _ (outside _ (.inl lo)) (fixed i t)
  · intro t;fin_cases t <;> first
      | (change dest J true node 0+4*L.rows<_;omega) | (change a<_;omega) | (change L.rows<_;omega) | (change L.bits<_;omega)
  · intro t;fin_cases t <;> first
      | (change dest J false node 0+4*R.rows<_;omega) | (change b<_;omega) | (change R.rows<_;omega) | (change R.bits<_;omega)

end PairPlacement

section PairZeroPlacement
open HistoryPartyPairExec
variable (j : Fin f.parties) (L : Tree F a) (R : Tree F b)
  (id : ((Fin 3→Bool)→F)→ℕ) (mem : Memory (16*u^10))
local notation "J" => (rawArm A j.val).party
local notation "N" => pairNetwork L R
local notation "Q" => HistoryPartyPairExec.copyHeader J node L R
local notation "P" => HistoryPartyPairExec.build J node a b mem
local notation "ops" => HistoryPartyPairExec.steps (w:=W₀) J node L R id
local notation "root" => HistoryPartyPair.atPair J node

omit [CommRing F] in
theorem physical_pair_source (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (pins : a+b≤V) (rows : 4*(L.rows+R.rows)≤V)
    (cursor : numeric mem (J).cursor-1=node) :
    BootRoom J mem node ∧ PairSourceRoom J node L R id (W:=W₀) :=
  physical_pair_source_at u arch f node 0 j L R id mem age count motifs capacity pins rows cursor

omit [CommRing F] in
theorem physical_pair_room (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (pins : a+b≤V)
    (rows : 8*(L.rows+R.rows)≤V) (bits : L.bits+R.bits<2^W₀)
    («meta» : ∀ i k t,HistoryCompiledRows.metadata id (N i) k t<2^W₀)
    (cursor : numeric mem (J).cursor-1=node) : PairRoom J node L R id mem :=
  physical_pair_room_at u arch f node 0 j L R id mem age count motifs capacity pins rows bits «meta» cursor

end PairZeroPlacement

end PhysicalOrder


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
