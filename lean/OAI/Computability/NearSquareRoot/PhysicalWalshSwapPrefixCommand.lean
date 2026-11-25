import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefix
import OAI.Computability.NearSquareRoot.PhysicalWalshParamLiterals

/-! # Effective prefix extension and truncation for a Walsh lane

A shared program reads the radix and fanout beside the node descriptor,
computes the exact two row counts in binary, and materializes the required
tallies. Specialization to a candidate writes just its two literals.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SwapPrefixCmd

open IntegerMultiplication Code Space Strip Carry Staff PhysicalWalsh
open CommonRegisters GeneratorSyntax SwapPrefix

private structure World where
  A : ℕ
  W : ℕ
  s : Shape

private def params (z : World) := (tally z.A,tally z.W)
private def desc (z : World) := Header.wire z.A z.s
private def compactHeader (z : World) := (params z,desc z)
private def regime : Regime World := ⟨size ∘ compactHeader,send ∘ compactHeader,Dom.base _⟩
private def marks (z : World) := cuts z.A z.W z.s
private def counts (z : World) := (desc z, marks z)

private theorem counts_mint : Mint regime counts := by
  have input : regime.Has compactHeader := regime.self
  have hd : regime.Has desc := input.ez Easy.snd
  have batch : Realizes regime World.W := input.ez (Easy.fst.compose Easy.snd)
  have active : Realizes regime (fun z => grow z.A z.s.level) :=
    hd.ez (Easy.fst.compose (Easy.snd.compose Easy.fst))
  have pref : Figure regime (fun z => z.s.pref) :=
    ⟨_,hd.ez (Easy.snd.compose Easy.fst),fun z => Header.binary_value z.s.pref⟩
  have suff : Figure regime (fun z => z.s.suff) :=
    ⟨_,hd.ez (Easy.snd.compose Easy.snd),fun z => Header.binary_value z.s.suff⟩
  have groups := (Figure.natural 1).maximum (pref.quotients (Figure.of_spoken batch))
  have row := ((Figure.natural 2).repeated active).multiplied suff
  have raw := groups.multiplied row
  have padded := ((Figure.natural 2).repeated groups.short_log).multiplied row
  exact (Mint.of_has hd).pair ((Mint.tally (padded.subtracted raw)).pair (Mint.tally raw))

private structure Frame extends World where
  x : Data s

private def N (f : Frame) := length f.A f.W f.s
private def M (f : Frame) := paddedSize f.A f.W f.s
private def row (n : Frame → ℕ) (f : Frame) := stream (n f) f.x
private def extended (f : Frame) := stream (M f) (extend f.A f.W f.s f.x)
private def start (n : Frame → ℕ) (f : Frame) := (desc f.toWorld,row n f)
private def budget (d : ℕ) (f : Frame) :=
  (regime.scale f.toWorld+1)^d + regime.scale f.toWorld + allowance f.A 1 f.s

private theorem baseline (d : ℕ) (f : Frame) : allowance f.A 1 f.s ≤ budget d f := Nat.le_add_left ..
private theorem metadata (d : ℕ) (f : Frame) : size (compactHeader f.toWorld) ≤ budget d f :=
  (Nat.le_add_left ..).trans (Nat.le_add_right ..)
private theorem wireSize (d : ℕ) (f : Frame) : size (desc f.toWorld) ≤ budget d f := by
  have h := metadata d f
  change size (params f.toWorld)+size (desc f.toWorld)+1 ≤ _ at h
  omega

private theorem capacity' (d : ℕ) (f : Frame) : (N f+1)*(f.s.w+1) ≤ budget d f :=
  (capacity f.A f.W f.s 1).trans (baseline d f)

private theorem n_le (d : ℕ) (f : Frame) : N f ≤ budget d f :=
  (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (capacity' d f))

private theorem rowSize (d : ℕ) (f : Frame) (n : ℕ) (hn : n ≤ M f) (x : Data f.s) :
    size (stream n x) ≤ 16*budget d f+1 :=
  (stream_cost f.A f.W 1 f.s n x hn).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (baseline d f)) _)

private theorem countSize (d : ℕ) (f : Frame) : size (counts f.toWorld) ≤ 7*budget d f+4 := by
  have hd := wireSize d f
  have hn := n_le d f
  have hm : M f ≤ 2*N f := paddedSize_le f.A f.W f.s
  change size (desc f.toWorld)+(size (tally (M f-N f),tally (N f)))+1 ≤ _
  change size (desc f.toWorld)+(size (tally (M f-N f))+size (tally (N f))+1)+1 ≤ _
  simp only [size_tally,tally_length]; omega

private abbrev Row := List Dusk.Pair
private abbrev T := Tally × Tally
private abbrev H := Header.Wire

private def associate (v : T × H × Row) := ((v.1,v.2.1),v.2.2)
private def separate (v : (H × T) × Row) := (v.1.1,(v.1.2,v.2))
private def keep (v : H × Tally × Row) := (v.1,v.2.2)
private def cut (v : H × T × Row) := v.2.2.take v.2.1.2.length

private theorem counted : ∃ d, ∀ (n : Frame → ℕ) (_hn : ∀ f, n f ≤ M f),
    BoundedTask (budget d) (budget d) (fun f => .fork (send (params f.toWorld)) (send (start n f)))
      (fun f => send (desc f.toWorld,(marks f.toWorld,row n f))) := by
  obtain ⟨d,C,mint⟩ := counts_mint.bounded
  refine ⟨d,fun n hn => ?_⟩
  let a (f : Frame) := (params f.toWorld,start n f)
  have first := PhysicalWalshGrid.easyWithin (budget d) (show Easy associate by unfold associate; fun_prop) a 22
    (fun f => by
      have md := metadata d f
      have rs := rowSize d f (n f) (hn f) f.x
      change size (params f.toWorld)+size (desc f.toWorld)+1 ≤ _ at md
      change size (params f.toWorld)+(size (desc f.toWorld)+size (stream (n f) f.x)+1)+1 ≤ _
      omega)
  have core := (mint.on Frame.toWorld).left (fun f => send (row n f))
  have middle : BoundedTask (budget d) (budget d)
      (fun f => send (compactHeader f.toWorld,row n f)) (fun f => send (counts f.toWorld,row n f)) := by
    apply core.bound (C+12) (C+30) <;> intro f
    all_goals
      have cs := countSize d f
      have rs := rowSize d f (n f) (hn f) f.x
      have compact : C*(regime.scale f.toWorld+1)^d ≤ C*budget d f :=
        Nat.mul_le_mul_left _ ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
    · change C*(regime.scale f.toWorld+1)^d+_+1 ≤ _
      rw [Nat.add_mul,Nat.mul_succ]; omega
    · change C*(regime.scale f.toWorld+1)^d+size (counts f.toWorld)+size (stream (n f) f.x)+1 ≤ _
      rw [Nat.add_mul,Nat.mul_succ]; omega
  have last := PhysicalWalshGrid.easyWithin (budget d) (show Easy separate by unfold separate; fun_prop)
    (fun f => (counts f.toWorld,row n f)) 30 (fun f => by
      have cs := countSize d f
      have rs := rowSize d f (n f) (hn f) f.x
      change size (counts f.toWorld)+size (stream (n f) f.x)+1 ≤ _; omega)
  exact FixedCandidate.sequence (FixedCandidate.sequence first middle) last

private theorem padBody (d : ℕ) : BoundedTask (budget d) (budget d)
    (fun f => send (desc f.toWorld,(marks f.toWorld,row N f)))
    (fun f => send (desc f.toWorld,extended f)) := by
  let xs (f : Frame) := (List.range (N f)).map f.x
  have ne (f : Frame) : xs f ≠ [] := by
    intro h
    have bad := congrArg List.length h
    simp only [xs,List.length_nil,List.length_map,List.length_range] at bad
    exact (length_pos f.A f.W f.s).ne' bad
  have append := Padding.appendZeros (fun f : Frame => f.s.w) (fun f => M f-N f) xs ne
  simp only [xs,List.length_map,List.length_range,List.map_map] at append
  have eqn (f : Frame) : Padding.padded (M f-N f) ((List.range (N f)).map f.x) = extended f :=
    pad_eq f.A f.W f.s f.x
  simp only [eqn] at append
  have head : BoundedTask (budget d) (budget d)
      (fun f => send (desc f.toWorld,(marks f.toWorld,row N f)))
      (fun f => send (desc f.toWorld,tally (N f),extended f)) := by
    apply (append.right (fun f => send (desc f.toWorld))).bound 5 5 <;> intro f
    all_goals
      have wire := wireSize d f
      have cap := capacity' d f
      have nm : N f ≤ M f := length_le f.A f.W f.s
      have twice : M f ≤ 2*N f := paddedSize_le f.A f.W f.s
      have cost := Nat.mul_le_mul_right (f.s.w+1) (show N f+(M f-N f)+1 ≤ 2*(N f+1) by omega)
      rw [Nat.mul_assoc] at cost
    · change size (desc f.toWorld)+(N f+(M f-N f)+1)*(f.s.w+1)+1 ≤ _; omega
    · change (N f+(M f-N f)+1)*(f.s.w+1)+size (desc f.toWorld)+1 ≤ _; omega
  have last := PhysicalWalshGrid.easyWithin (budget d) (show Easy keep by unfold keep; fun_prop)
    (fun f => (desc f.toWorld,tally (N f),extended f)) 23 (fun f => by
      have wire := wireSize d f
      have n := n_le d f
      have rs := rowSize d f (M f) le_rfl (extend f.A f.W f.s f.x)
      change size (desc f.toWorld)+(size (tally (N f))+size (stream (M f) (extend f.A f.W f.s f.x))+1)+1 ≤ _
      simp only [size_tally,tally_length]; omega)
  exact FixedCandidate.sequence head last

private theorem cropBody (d : ℕ) : BoundedTask (budget d) (budget d)
    (fun f => send (desc f.toWorld,(marks f.toWorld,row M f)))
    (fun f => send (row N f)) := by
  have easy : Easy cut := (easy_cut ((Easy.snd.compose (Easy.fst.compose Easy.snd)).pair
    (Easy.snd.compose Easy.snd))).compose Easy.fst
  have op := PhysicalWalshGrid.easyWithin (budget d) easy
    (fun f => (desc f.toWorld,(marks f.toWorld,row M f))) 30 (fun f => by
      have c := countSize d f
      have h := rowSize d f (M f) le_rfl f.x
      change size (desc f.toWorld)+size (marks f.toWorld)+1 ≤ _ at c
      change size (desc f.toWorld)+(size (marks f.toWorld)+size (stream (M f) f.x)+1)+1 ≤ _
      omega)
  have eqn (f : Frame) : cut (desc f.toWorld,marks f.toWorld,row M f) = row N f := by
    change ((List.range (M f)).map (Dusk.mark ∘ f.x)).take (tally (N f)).length = _
    rw [tally_length,← List.map_take,List.take_range,Nat.min_eq_left (show N f ≤ M f from length_le f.A f.W f.s)]
    rfl
  simpa only [eqn] using op

private noncomputable def d₀ := counted.choose
private def source (pad : Bool) (f : Frame) := send (start (if pad then N else M) f)
private def dest (pad : Bool) (f : Frame) := if pad then send (desc f.toWorld,extended f) else send (row N f)
private theorem interpreter (pad : Bool) : BoundedTask (budget d₀) (budget d₀)
    (fun f => .fork (send (params f.toWorld)) (source pad f)) (dest pad) := by
  cases pad
  · exact FixedCandidate.sequence (counted.choose_spec M (fun _ => le_rfl)) (cropBody d₀)
  · exact FixedCandidate.sequence (counted.choose_spec N (fun f => length_le f.A f.W f.s)) (padBody d₀)

private noncomputable def command (pad : Bool) (p : ℕ × ℕ) := ParamLiterals.command p.1 p.2 (interpreter pad).choose
noncomputable def pre := command true
noncomputable def post := command false
noncomputable def degree := d₀+1

theorem effective_pre : Effective ltr pre := ParamLiterals.effective _
theorem effective_post : Effective ltr post := ParamLiterals.effective _

theorem within : ∃ R, 0 < R ∧ ∀ p, Within R (pre p) ∧ Within R (post p) := by
  obtain ⟨R,hr,hp,hc⟩ := ((Filter.eventually_gt_atTop (0:ℕ)).and ((RegisterSelect.within_eventually
    (interpreter true).choose).and (RegisterSelect.within_eventually (interpreter false).choose))).exists
  exact ⟨R,hr,fun _ => ⟨ParamLiterals.within hr hp _ _,ParamLiterals.within hr hc _ _⟩⟩

private theorem specialize {I : Type} (pad : Bool) (A W : ℕ) (s : I → Shape) (x : (i:I) → Data (s i)) :
    let f i : Frame := ⟨⟨A,W,s i⟩,x i⟩
    ClosedRuns (command pad (A,W)) (allowance A degree ∘ s) (allowance A degree ∘ s)
      (source pad ∘ f) (dest pad ∘ f) := by
  intro f
  let b i := budget d₀ (f i)
  let t i := b i + (source pad (f i)).count
  have run : EffectiveBoundedTask.Runs (interpreter pad).choose b b
      (fun i => .fork (ParamLiterals.literal A W) (source pad (f i))) (dest pad ∘ f) :=
    EffectiveBoundedTask.Runs.on (interpreter pad).choose_spec f
  have monotone : ∀ i, b i ≤ t i := fun _ => Nat.le_add_right ..
  have emitted := ParamLiterals.runs A W (run.mono monotone monotone) (fun i => Nat.le_add_left ..)
  let P := size (tally A,tally W)+2
  let K := P^d₀+P+2
  have step (i : I) : t i+1 ≤ (25*K+30)*(allowance A degree (s i)+1) := by
    let H := Header.scale A (s i)+1
    let B := allowance A degree (s i)
    have metaSize : regime.scale (f i).toWorld+1 ≤ P*H := by
      change size (tally A,tally W)+Header.scale A (s i)+1+1 ≤ (size (tally A,tally W)+2)*(Header.scale A (s i)+1)
      rw [Nat.mul_succ,Nat.add_mul]; omega
    have grow : H^d₀ ≤ H^degree := Nat.pow_le_pow_right (by dsimp [H]; omega) (Nat.le_succ _)
    have power : H^degree ≤ B := Nat.le_add_left ..
    have hbase : H ≤ B := (show H ≤ H^degree by simpa using
      (Nat.pow_le_pow_right (n:=H) (by dsimp [H]; omega) (show 1 ≤ degree by unfold degree; omega))).trans power
    have compact : (regime.scale (f i).toWorld+1)^d₀ ≤ P^d₀*B := by
      exact (Nat.pow_le_pow_left metaSize _).trans ((mul_pow ..).le.trans (Nat.mul_le_mul_left _ (grow.trans power)))
    have base : allowance A 1 (s i) ≤ B := allowance_mono (show 1 ≤ degree by unfold degree; omega) _
    have coeff : regime.scale (f i).toWorld+1 ≤ P*B := metaSize.trans (Nat.mul_le_mul_left _ hbase)
    have initialCost : b i ≤ K*B := by
      change (regime.scale (f i).toWorld+1)^d₀+regime.scale (f i).toWorld+allowance A 1 (s i) ≤ (P^d₀+P+2)*B
      rw [Nat.add_mul,Nat.add_mul]; omega
    have payload : (source pad (f i)).count ≤ 18*b i+2 := by
      let q := if pad then N else M
      have fit : q (f i) ≤ M (f i) := by cases pad <;> simp [q,length_le,N,M]
      have rs := rowSize d₀ (f i) (q (f i)) fit (f i).x
      have h := wireSize d₀ (f i)
      change size (desc (f i).toWorld)+size (stream (q (f i)) (f i).x)+1 ≤ 18*budget d₀ (f i)+2
      omega
    change b i+(source pad (f i)).count+1 ≤ (25*K+30)*(B+1)
    rw [Nat.add_mul,Nat.mul_assoc, Nat.mul_succ K]; omega
  exact emitted.bound _ _ step step

theorem pre_runs {I : Type} (A W : ℕ) (s : I → Shape) (x : (i:I) → Data (s i)) :
    ClosedRuns (pre (A,W)) (allowance A degree ∘ s) (allowance A degree ∘ s)
      (fun i => send (Header.wire A (s i),laneFlat A W (s i) (x i)))
      (fun i => send (Header.wire A (s i),stream (paddedSize A W (s i)) (extend A W (s i) (x i)))) :=
  specialize true A W s x

theorem post_runs {I : Type} (A W : ℕ) (s : I → Shape) (x : (i:I) → Data (s i)) :
    ClosedRuns (post (A,W)) (allowance A degree ∘ s) (allowance A degree ∘ s)
      (fun i => send (Header.wire A (s i),stream (paddedSize A W (s i)) (x i)))
      (fun i => send (laneFlat A W (s i) (x i))) :=
  specialize false A W s x

end PhysicalWalshNode.SwapPrefixCmd

end NearSquareRoot
end Computability
end OAI
