import OAI.Computability.BorderVNP.TeamSiteProcessorSort

/-! # Deterministic terminal witnesses of the physical signed team sorter

The record routing and sorting routines read their branches from stacks. Their unique
terminal execution leaves an arbitrary suffix of private choice bits untouched. The
unmasked sorter verdict records whether the physical assignment is consistent even when
the incoming signed weight is zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor

open VPVNP BurstRAM RAMTape RAMSerialization Layout TeamTapeSorting
attribute [local instance] TeamTapeSorting.portDecidableEq

private def quiet {K Q : Type} : StackOp K Q → Bool
  | .choose .. => false
  | _ => true

private theorem terminal_quiet (q : SitePost.terminal.State) : quiet (SitePost.terminal.body.code q) = true := by
  rcases q with (q | q)
  · rcases q with (q | ⟨_,q⟩)
    · cases q <;> rfl
    · cases q with
      | field m j ok phase => cases phase <;> rfl
      | _ => rfl
  · cases q <;> rfl

variable {K L Q : Type} [DecidableEq K] [DecidableEq L]

/-- An internal halting row reached by a deterministic execution. The routine's ordinary
return port is excluded so the verdict survives installation into a larger routine. -/
private def Ends (r : FiniteRoutine K) (s : Stacks K) := ∃ t q out b,
  StackRuns r.body.standalone t (some r.body.entry) s (some q) out ∧ r.body.code q = .halt b

private theorem terminal_of_stops (r : FiniteRoutine K) (det : ∀ q, quiet (r.body.code q) = true)
    (n : ℕ) (q : Option r.State) (s : Stacks K) (stop : r.body.AllStopsFrom (fun _ _ => False) n q s) :
    ∃ t u out b, StackRuns r.body.standalone t q s (some u) out ∧ r.body.code u = .halt b := by
  induction n generalizing q s with
  | zero => cases q <;> exact stop.elim
  | succ n ih =>
    cases q with
    | none => exact stop.elim
    | some q =>
      rw [Routine.AllStopsFrom] at stop
      have go {q' s'} (step : StackStep r.body.standalone (some q) s q' s')
          (h : r.body.AllStopsFrom (fun _ _ => False) n q' s') :
          ∃ t u out b, StackRuns r.body.standalone t (some q) s (some u) out ∧ r.body.code u = .halt b := by
        obtain ⟨t,u,out,b,run,halt⟩ := ih q' s' h
        exact ⟨t+1,u,out,b,StackRuns.cons step run,halt⟩
      cases he : r.body.code q with
      | push k b u => exact go (.push he) (by simpa only [he] using stop)
      | pop k f => exact go (.pop he) (by simpa only [he] using stop)
      | goto u => exact go (.goto he) (by simpa only [he] using stop)
      | choose l h => have hh := det q; simp [he,quiet] at hh
      | halt b => exact ⟨0,q,s,b,.nil ..,he⟩

private theorem installed {src : Routine K Q} {R : Type} {target : Routine K R}
    (labels : Q → R) (next : Option R) (rows : ∀ u, target.code (labels u) = src.install labels next u)
    {q u s out t} (run : StackRuns src.standalone t (some q) s (some u) out) :
    StackRuns target.standalone t (some (labels q)) s (some (labels u)) out := by
  let lab (x : Option Q) := x.elim next (some ∘ labels)
  have h := run.lift id Function.injective_id lab s (target := target.standalone) (by
    rintro (_ | i) h
    · contradiction
    · exact rows i)
  have eq (v : Stacks K) : installStacks id s v = v := funext fun i => installStacks_at Function.injective_id ..
  simpa only [lab,Option.elim_some,Function.comp_apply,eq] using h

private theorem followed {a b : FiniteRoutine K} {s mid : Stacks K} {n : ℕ}
    (first : a.Runs n s mid) (last : Ends b mid) : Ends (a.followedBy b) s := by
  obtain ⟨t,q,out,ok,run,halt⟩ := last
  let target := (a.followedBy b).body
  have l := first.link target Sum.inl (some (.inr b.body.entry)) (fun _ => rfl)
  have r := installed Sum.inr none (target := target) (fun _ => rfl) run
  exact ⟨_,.inr q,out,ok,l.trans r,by change (b.body.code q).rename _ _ = _; rw [halt]; rfl⟩

private theorem on_ports {r : FiniteRoutine K} (ports : K → L) (inj : Function.Injective ports)
    (s : Stacks L) (h : Ends r (s ∘ ports)) : Ends (r.onPorts ports) s := by
  obtain ⟨t,q,out,b,run,halt⟩ := h
  have lift := run.lift ports inj id s (target := (r.onPorts ports).body.standalone) (by
    intro i _; cases i <;> rfl)
  rw [installStacks_eq inj s (s ∘ ports) (fun _ => rfl)] at lift
  exact ⟨t,q,_,b,lift,by change (r.body.code q).rename _ _ = _; rw [halt]; rfl⟩

variable {d e w : ℕ}

private theorem site_ends (hw : 2 ≤ w) (cap : 2^d*2^e < 2^w) (a : Fields d e w)
    (v : Word d) (x : ℕ → Option (WordRecord w)) : Ends TeamTapeSorting.program (siteInput hw a v x) := by
  let prev := incoming a v
  let sent := outgoing a v
  let raw := rawBlock hw e v x
  let tail := (List.ofFn (RAMLayout.incidentBits (embedFields a) v)).drop (16*w)
  let flags := [Sorter.verifyOK sent sent,Sorter.verifyOK prev prev]
  obtain ⟨out,guardRun,hbank⟩ := guard_runs v prev sent (raw,[]) tail
  change guard.Runs _ (siteInput hw a v x) out at guardRun
  change out ∘ Sum.inr = SitePost.prestate v prev sent (raw,flags) tail at hbank
  apply followed guardRun
  apply on_ports Sum.inr Sum.inr_injective
  rw [hbank]
  have can : SortReplay.CanonicalBlock hw raw := fun i => (SortReplay.canonical_iff hw _).mpr ⟨_,rfl⟩
  obtain ⟨t,_,y,run,_,_,_⟩ := SitePost.prepareSort_messages hw cap (embedFields a) v prev sent (raw,flags) can
  apply followed run
  exact terminal_of_stops SitePost.terminal terminal_quiet _ _ _ (SitePost.terminal_total v prev sent y _ 0)

private def firstLane (r : FiniteRoutine K) : FiniteRoutine K := .ofRoutine
  { entry := r.body.entry
    code := fun q => match r.body.code q with
      | .halt true => .goto none
      | op => op }

private theorem both_ends (r : FiniteRoutine K) (s : Stacks (Bool × K))
    (low : Ends r (s ∘ Prod.mk false)) (high : Ends r (s ∘ Prod.mk true)) : Ends (Lanes.both r) s := by
  let a := (firstLane r).onPorts (Prod.mk false)
  let b := r.onPorts (Prod.mk true)
  have eq : Lanes.both r = a.followedBy b := by
    unfold Lanes.both a b
    congr 3
    change Routine.mk _ _ = Routine.mk _ _
    congr 1
    funext q
    cases he : r.body.code q <;> first | rfl | (rename_i ok; cases ok <;> rfl)
  rw [eq]
  have inj (i : Bool) : Function.Injective (Prod.mk i : K → Bool × K) := fun _ _ h => (Prod.mk.inj h).2
  obtain ⟨t,q,out,ok,run,halt⟩ := low
  let z := installStacks (Prod.mk false) s out
  have h := run.lift (Prod.mk false) (inj false) id s (target := a.body.standalone) (by
    rintro (_|u) h
    · contradiction
    · change (((match r.body.code u with | .halt true => StackOp.goto none | op => op)).rename _ id) = _
      change (r.body.code u).returns = false at h
      cases op : r.body.code u <;> simp_all only [Routine.standalone,Routine.close,StackOp.returns,Bool.true_eq_false] <;> rfl)
  rw [installStacks_eq (inj false) s (s ∘ Prod.mk false) (fun _ => rfl)] at h
  change StackRuns a.body.standalone t (some a.body.entry) s (some q) z at h
  cases ok with
  | false =>
    have last : a.body.code q = .halt false := by change ((match r.body.code q with | .halt true => StackOp.goto none | op => op).rename _ id) = _; rw [halt]; rfl
    exact ⟨_,.inl q,z,false,installed Sum.inl (some (.inr b.body.entry)) (target := (a.followedBy b).body)
      (fun _ => rfl) h, by change (a.body.code q).rename _ _ = _; rw [last]; rfl⟩
  | true =>
    have last : a.body.standalone (some q) = .goto none := by change ((match r.body.code q with | .halt true => StackOp.goto none | op => op).rename _ id) = _; rw [halt]; rfl
    apply followed (h.trans (.cons (.goto last) (.nil ..)))
    apply on_ports (Prod.mk true) (inj true)
    have same : z ∘ Prod.mk true = s ∘ Prod.mk true := funext fun i => installStacks_outside s out (by simp)
    rwa [same]

private theorem pop_low {U V : Type} [Fintype U] [Fintype V] (port : K) (low : FiniteRoutine K) (high : Routine K U)
    (missing : Routine K V) (s : Stacks K) (tail : List Bool) (h : s port = false :: tail)
    (st : Ends low (Function.update s port tail)) : Ends (.ofRoutine (Routine.popCase port missing low.body high)) s := by
  let outer := Routine.popCase port missing low.body high
  obtain ⟨t,q,out,ok,run,halt⟩ := st
  let lab : low.State → Unit ⊕ (V ⊕ (low.State ⊕ U)) := Sum.inr ∘ Sum.inr ∘ Sum.inl
  have follow := installed lab none (target := outer) (fun _ => rfl) run
  have step : StackStep outer.standalone (some outer.entry) s (some (lab low.body.entry)) (Function.update s port tail) := by
    simpa only [lab,Function.comp_apply,h,List.head?_cons,List.tail_cons] using StackStep.pop (code := outer.standalone) (s := s)
      (q := some outer.entry) (show outer.standalone (some outer.entry) = .pop port _ from rfl)
  exact ⟨_,lab q,out,ok,.cons step follow,by change (low.body.code q).rename _ _ = _; rw [halt]; rfl⟩

private theorem pop_high {U V : Type} [Fintype U] [Fintype V] (port : K) (low : Routine K U) (high : FiniteRoutine K)
    (missing : Routine K V) (s : Stacks K) (tail : List Bool) (h : s port = true :: tail)
    (st : Ends high (Function.update s port tail)) : Ends (.ofRoutine (Routine.popCase port missing low high.body)) s := by
  let outer := Routine.popCase port missing low high.body
  obtain ⟨t,q,out,ok,run,halt⟩ := st
  let lab : high.State → Unit ⊕ (V ⊕ (U ⊕ high.State)) := Sum.inr ∘ Sum.inr ∘ Sum.inr
  have follow := installed lab none (target := outer) (fun _ => rfl) run
  have step : StackStep outer.standalone (some outer.entry) s (some (lab high.body.entry)) (Function.update s port tail) := by
    simpa only [lab,Function.comp_apply,h,List.head?_cons,List.tail_cons] using StackStep.pop (code := outer.standalone) (s := s)
      (q := some outer.entry) (show outer.standalone (some outer.entry) = .pop port _ from rfl)
  exact ⟨_,lab q,out,ok,.cons step follow,by change (high.body.code q).rename _ _ = _; rw [halt]; rfl⟩

private theorem owner_ends (hw : 2 ≤ w) (cap : 2^d*2^e < 2^w) (a : Fields d e w)
    (v : Word d) (x : ℕ → Option (WordRecord w)) (other : Option (Word d))
    (s : Stacks TeamTapeInputRoute.Verify.Port) (tail : List Bool)
    (flag : s (.inr TeamTapeInputRoute.secondFlag) = other.isSome :: tail)
    (real : s ∘ TeamTapeInputRoute.Verify.lanePort false = siteInput hw a v x)
    (virt : ∀ u, other = some u → s ∘ TeamTapeInputRoute.Verify.lanePort true = siteInput hw a u x) :
    Ends TeamTapeInputRoute.Verify.terminal s := by
  let port : TeamTapeInputRoute.Verify.Port := .inr TeamTapeInputRoute.secondFlag
  let pair (i : Bool × TeamTapeSorting.Port) := TeamTapeInputRoute.Verify.lanePort i.1 i.2
  let low := TeamTapeSorting.program.onPorts (TeamTapeInputRoute.Verify.lanePort false)
  let high := (Lanes.both TeamTapeSorting.program).onPorts pair
  let after := Function.update s port tail
  have eq (b : Bool) : after ∘ TeamTapeInputRoute.Verify.lanePort b = s ∘ TeamTapeInputRoute.Verify.lanePort b := by
    funext i; cases i <;> simp [after,port,TeamTapeInputRoute.Verify.lanePort]
  have hi : Function.Injective pair := by
    rintro ⟨b,i|i⟩ ⟨j,k|k⟩ he <;> simp_all [pair,TeamTapeInputRoute.Verify.lanePort]
  cases other with
  | none =>
    apply pop_low port low high.body (Routine.halt false) s tail flag
    apply on_ports _ (fun i j h => (Prod.mk.inj (hi (a₁ := (false,i)) (a₂ := (false,j)) h)).2)
    change Ends _ (after ∘ _)
    rw [eq,real]; exact site_ends hw cap a v x
  | some u =>
    apply pop_high port low.body high (Routine.halt false) s tail flag
    apply on_ports pair hi
    apply both_ends
    · change Ends _ (after ∘ TeamTapeInputRoute.Verify.lanePort false)
      rw [eq,real]; exact site_ends hw cap a v x
    · change Ends _ (after ∘ TeamTapeInputRoute.Verify.lanePort true)
      rw [eq,virt u rfl]; exact site_ends hw cap a u x

private theorem before_clock {C : StackCode K Q} {n q s u out t}
    (run : StackRuns C n q s u out) (stop : StopsWithin C t q s) : n < t := by
  by_contra hn
  have h := (run.stopsWithin_iff 0).mp (stop.mono (by omega))
  exact h

private theorem raw_sort_replay (n : ℕ) (hw₂ : 2 ≤ w) (cap : 2^d*2^e < 2^w) (f : Fields d e w)
    (v : Word d) (other : Option (Word d)) (rows : Word d → List (WordRecord w))
    (empty : ∀ u, other = some u → rows u = []) (raw : Stacks TeamTapeInputRoute.Port)
    (tail rest : List Bool) (hd : d ≤ n) (hw : w ≤ n) (hc : 2^e ≤ n) (hL : TeamTapeInputRoute.comparisonSize d e w ≤ n)
    (hi : raw TeamTapeInputRoute.metadata = TeamTapeInputRoute.metadataBits n e w v other ++ tail)
    (hs : raw TeamTapeInputRoute.source = TeamTapeInputRoute.ownerBits f v other ++ rest)
    (width : (raw TeamTapeInputRoute.widthSource).length = w) (bucket : (raw TeamTapeInputRoute.bucket).length = 2^e)
    (suffix : raw .suffixSize = []) (bits : raw (.entry (.inl .bits)) = []) (hh : raw (.entry (.inl .high)) = [])
    (tmp : raw (.entry (.inl .scratch)) = []) (count : raw (.work .count) = []) (scratch : raw (.work .tmp) = [])
    (post : ∀ b i, raw (.post b i) = [])
    (closed : raw TeamTapeInputRoute.closedBlock = List.ofFn ((blockFormat (2^e) hw₂).encode (RecordBuffer.slots (2^e) (rows v))))
    (fuel : ℕ) (budget : 600*(n+1)^2+2*siteBudget d e w+1 ≤ fuel) :
    let r := TeamTapeInputRoute.Verify.processor
    let ok := TeamTapeInputRoute.Verify.ownerValid hw₂ cap f (rowInput e rows) v other
    ∃ t < fuel, ∃ q out b, StackRuns r.body.standalone t (some r.body.entry) (TeamTapeInputRoute.Verify.initial raw)
      (some q) out ∧ r.body.code q = .halt b ∧ (b = true ↔ ok) := by
  intro r ok
  obtain ⟨_,_,out,run,_,_,hflag,hfirst,hsecond,_,_⟩ := TeamTapeInputRoute.loader_spec n hw₂ f v other raw tail rest (rows v)
    hd hw hc hL hi hs width bucket suffix bits hh tmp count scratch post closed
  have load := run.lift Sum.inr Sum.inr_injective id (TeamTapeInputRoute.Verify.initial raw)
    (target := (TeamTapeInputRoute.loader.onPorts Sum.inr).body.standalone) (by intro q _; cases q <;> rfl)
  have eq (x : Stacks TeamTapeInputRoute.Port) : installStacks Sum.inr (TeamTapeInputRoute.Verify.initial raw) x =
      TeamTapeInputRoute.Verify.initial x := by
    apply installStacks_frame (target := TeamTapeInputRoute.Verify.initial x) (small := x) Sum.inr_injective (fun _ => rfl)
    rintro (i|i) h; exacts [rfl,(h i rfl).elim]
  rw [eq,eq] at load
  have bank_eq (lane : Bool) (u : Word d) (h : out ∘ TeamTapeInputRoute.Port.post lane = SitePost.prestate u (incoming f u) (outgoing f u)
      (SortReplay.emittedBlock hw₂ e (rows u),[]) (TeamTapeInputRoute.comparisonBits f u)) :
      TeamTapeInputRoute.Verify.initial out ∘ TeamTapeInputRoute.Verify.lanePort lane = siteInput hw₂ f u (rowInput e rows) := by
    rw [siteInput,rawBlock_eq_emitted]; funext i; cases i with | inl => rfl | inr => exact congrFun h _
  have endRun : Ends r (TeamTapeInputRoute.Verify.initial raw) := followed load (owner_ends hw₂ cap f v (rowInput e rows) other
    _ _ hflag (bank_eq _ _ hfirst) (fun u hu => bank_eq _ _ (by simpa only [empty u hu] using hsecond u hu)))
  obtain ⟨t,q,out,b,path,halt⟩ := endRun
  have spec := TeamTapeInputRoute.Verify.processor_spec n hw₂ cap f v other rows empty raw tail rest hd hw hc hL hi hs
    width bucket suffix bits hh tmp count scratch post closed fuel budget
  have bound : t < fuel := before_clock path ((Routine.stopsWithin_close_iff ..).2 (spec.2 _))
  refine ⟨t,bound,q,out,b,path,halt,?_⟩
  let rem := fuel - (t+1)
  have he : rem+1+t = fuel := by dsimp [rem]; omega
  have countEq := path.paths (rem+1)
  rw [he,stackPaths,show r.body.standalone (some q) = .halt b from halt,Routine.stackPaths_close] at countEq
  have verdict := (spec.1 (fun n _ => if n = 0 then 0 else false.toNat)).symm.trans countEq
  change (@ite ℕ ok (Classical.propDecidable _) 1 0) = b.toNat at verdict
  by_cases h : ok <;> cases b <;> simp [h] at verdict ⊢

variable {Γ : Type} {p r k a m g n : ℕ}

/-- The actual two-lane sorter reaches an internal terminal without reading any choices.
Its unmasked halt records owner validity. Its physical halt also accounts for zero weight. -/
theorem sort_replay (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (sg : Option Bool)
    (n : ℕ) (hw₂ : 2 ≤ w) (cap : 2^d*2^e < 2^w) (f : Fields d e w) (v : Word d)
    (other : Option (Word d)) (rows : Word d → List (WordRecord w))
    (empty : ∀ u, other = some u → rows u = []) (s : Stacks (Layout.Port r k (m*g)))
    (ready : RouteReady n f v other s) (hd : d ≤ n) (hw : w ≤ n) (hc : 2^e ≤ n)
    (hL : TeamTapeInputRoute.comparisonSize d e w ≤ n)
    (closed : s (buffer .output) = List.ofFn ((blockFormat (2^e) hw₂).encode (RecordBuffer.slots (2^e) (rows v))))
    (fuel : ℕ) (budget : 600*(n+1)^2+2*siteBudget d e w+1 ≤ fuel) :
    let checker := TeamTapeInputRoute.Verify.processor.body
    ∃ t < fuel, ∃ q out b, (∀ suffix, StackRuns (TeamPrivateFragment.replay (code P lib)) t
      (.sort sg (some checker.entry),suffix) s (.sort sg (some q),suffix) out) ∧
      checker.code q = .halt b ∧ (b = true ↔ TeamTapeInputRoute.Verify.ownerValid hw₂ cap f (rowInput e rows) v other) ∧
      code P lib (.sort sg (some q)) = .halt (b && sg.isSome) := by
  intro checker
  let raw := s ∘ Layout.Port.route ∘ Sum.inr
  have eq : s ∘ Layout.Port.route = TeamTapeInputRoute.Verify.initial raw := by
    funext i; cases i with | inl i => exact ready.guard i | inr i => rfl
  rcases ready.literal with ⟨tail,hi⟩; rcases ready.wires with ⟨rest,hs⟩
  obtain ⟨t,ht,q,out,b,run,halt,hb⟩ := raw_sort_replay n hw₂ cap f v other rows empty raw tail rest hd hw hc hL
    hi hs ready.width ready.bucket ready.suffix ready.bits ready.high ready.tmp ready.count ready.scratch ready.post closed fuel budget
  have inj : Function.Injective (Layout.Port.route (r := r) (k := k) (d := m*g)) := fun _ _ h => Layout.Port.route.inj h
  have h := run.lift Layout.Port.route inj (.sort sg) s (target := code P lib) (by
    intro u hu
    change (withWeight sg checker.standalone u).rename _ _ = (checker.standalone u).rename _ _
    change (checker.standalone u).returns = false at hu
    unfold withWeight; cases op : checker.standalone u <;> first | rfl | (simp [op] at hu))
  rw [installStacks_eq inj s (TeamTapeInputRoute.Verify.initial raw) (congrFun eq)] at h
  refine ⟨t,ht,q,_,b,TeamPrivateFragment.replay_segment h,halt,hb,?_⟩
  change (withWeight sg checker.standalone (some q)).rename _ _ = _
  unfold withWeight; rw [show checker.standalone (some q) = .halt b from halt]; rfl

/-- Closing the record buffer and checking its one or two virtual blocks preserves every
unused choice bit, including when a valid signed path has weight zero. -/
theorem closeSort_replay (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (sg : Option Bool)
    (n : ℕ) (hw₂ : 2 ≤ w) (cap : 2^d*2^e < 2^w) (f : Fields d e w) (v : Word d)
    (other : Option (Word d)) (rows : Word d → List (WordRecord w))
    (empty : ∀ u, other = some u → rows u = []) (s : Stacks (Layout.Port r k (m*g)))
    (ready : RouteReady n f v other s) (hd : d ≤ n) (hw : w ≤ n) (hc : 2^e ≤ n)
    (hL : TeamTapeInputRoute.comparisonSize d e w ≤ n) (records : RecordBuffer.Holds hw₂ (2^e) (rows v) (s ∘ buffer))
    (fuel : ℕ) (budget : 600*(n+1)^2+2*siteBudget d e w+1 ≤ fuel) :
    let closeTime := (4*2^e-(rows v).length)*(25*w+12)+1+(2*(4*2^e*5*w)+1)
    let checker := TeamTapeInputRoute.Verify.processor.body
    ∃ t < fuel+closeTime, ∃ q out b, (∀ suffix, StackRuns (TeamPrivateFragment.replay (code P lib)) t
      (.close sg RecordBuffer.close.body.entry,suffix) s (.sort sg (some q),suffix) out) ∧
      checker.code q = .halt b ∧ (b = true ↔ TeamTapeInputRoute.Verify.ownerValid hw₂ cap f (rowInput e rows) v other) ∧
      code P lib (.sort sg (some q)) = .halt (b && sg.isSome) := by
  intro closeTime checker
  let out := Function.update (Function.update (Function.update (s ∘ buffer) .remaining []) .reverseBuffer [])
    .output (Boundary.blockBytes (List.ofFn (SortReplay.emittedBlock hw₂ e (rows v))))
  have hclose := SortReplay.close_emittedBlock records
  have inj : Function.Injective (buffer (r := r) (k := k) (d := m*g)) := by intro i j he; simpa using he
  have hr := TeamLink.routine hclose (code P lib) buffer inj (.close sg)
    (.sort sg (some checker.entry)) s (fun _ => rfl)
  rw [installStacks_eq inj s (s ∘ buffer) (fun _ => rfl)] at hr
  have closed : installStacks buffer s out (buffer .output) =
      List.ofFn ((blockFormat (2^e) hw₂).encode (RecordBuffer.slots (2^e) (rows v))) := by
    rw [installStacks_at inj,show out .output = Boundary.blockBytes (List.ofFn (SortReplay.emittedBlock hw₂ e (rows v))) from Function.update_self ..]
    exact SortReplay.emittedBlock_bytes ..
  obtain ⟨t,ht,q,u,b,run,halt,valid,physical⟩ := sort_replay P lib sg n hw₂ cap f v other rows empty _
    (ready.installBuffer _) hd hw hc hL closed fuel budget
  exact ⟨closeTime+t,by omega,q,u,b,fun bs => (TeamPrivateFragment.replay_segment hr bs).trans (run bs),halt,valid,physical⟩

/-- A terminal replay from the same sorter input uses the same time, terminal state and bank,
and returns the entire choice suffix. The accepted bit includes the incoming path's weight. -/
theorem sort_terminal_unique {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
    {entry u : Label P Q m g} {sg : Option Bool} {q : TeamTapeInputRoute.Verify.processor.State}
    {s out other : Stacks (Layout.Port r k (m*g))} {t t' : ℕ} {b ok : Bool} {bits rest : List Bool}
    (canonical : ∀ suffix, StackRuns (TeamPrivateFragment.replay (code P lib)) t
      (entry,suffix) s (.sort sg (some q),suffix) out)
    (row : code P lib (.sort sg (some q)) = .halt (b && sg.isSome))
    (run : StackRuns (TeamPrivateFragment.replay (code P lib)) t' (entry,bits) s (u,rest) other)
    (halt : code P lib u = .halt ok) :
    t' = t ∧ u = .sort sg (some q) ∧ rest = bits ∧ other = out ∧ ok = (b && sg.isSome) := by
  have h₁ : TeamPrivateFragment.replay (code P lib) (u,rest) = .halt ok := by simp [TeamPrivateFragment.replay,halt]
  have h₂ : TeamPrivateFragment.replay (code P lib) (.sort sg (some q),bits) = .halt (b && sg.isSome) := by
    simp [TeamPrivateFragment.replay,row]
  obtain ⟨time,control,bank⟩ := TeamContraction.Replay.terminal_unique run (canonical bits) h₁ h₂
  obtain ⟨rfl,suffix⟩ := Prod.mk.inj control
  exact ⟨time,rfl,suffix,bank,StackOp.halt.inj (halt.symm.trans row)⟩

/-- The sorter's accepting-leaf dictionary contains exactly the empty choice word with
its incoming sign on success. A valid zero-weight path retains its unmasked terminal
witness in `closeSort_replay`. -/
theorem sort_mem_leaves_iff {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
    {entry : Label P Q m g} {sg : Option Bool} {q : TeamTapeInputRoute.Verify.processor.State}
    {s out : Stacks (Layout.Port r k (m*g))} {t fuel : ℕ} {b : Bool} (time : t < fuel)
    (canonical : ∀ suffix, StackRuns (TeamPrivateFragment.replay (code P lib)) t
      (entry,suffix) s (.sort sg (some q),suffix) out)
    (row : code P lib (.sort sg (some q)) = .halt (b && sg.isSome)) (bits : List Bool) (z : Bool) :
    (bits,z) ∈ TeamContraction.Replay.leaves (code P lib) negative fuel entry s ↔ bits = [] ∧ b = true ∧ sg = some z := by
  rw [TeamContraction.Replay.mem_leaves_iff]
  constructor
  · rintro ⟨t',_,u,other,run,halt,sign⟩
    obtain ⟨_,rfl,suffix,_,accept⟩ := sort_terminal_unique canonical row run halt
    have ⟨valid,live⟩ := Bool.and_eq_true_iff.mp accept.symm
    exact ⟨suffix.symm,valid,by cases sg with | none => contradiction | some v => exact congrArg some sign⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨t,time,_,_,canonical [],row,rfl⟩

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
