import OAI.Computability.VPVNP.CompressorSurvivingImage
import OAI.Computability.VPVNP.PrimedScheduleRAM
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint

/-!
# Native scans of surviving wire subdivisions

Each role has a rectangular pass indexed by the dense motif and the subdivision.
A call writes the cells of one subdivision, including shared fields of its row.
Shared cells receive the same value on every write. The terminal memory therefore
contains every slice of every motif, even for widths smaller than the number of
subdivisions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingPass

open BurstRAM Allocation

variable {w : ℕ} {C : Type*}

/-- A scan starts at ordinal zero, returns the ordinal after the last call,
and satisfies the stated per-call bounds and memory access conditions. -/
structure Segment (P : Program w C) (fuel count : ℕ) (site : Report w → Prop)
    (initial : Memory w) (rs : List (Report w)) : Prop where
  executed : runSegment P fuel (some 0) initial (List.replicate count []) = some rs
  cursor : endState (some 0) rs = some (Fin.ofNat _ count)
  length : rs.length = count
  advance : ∀ j (hj : j < rs.length), rs[j].result = some (Fin.ofNat _ (j+1))
  sites : ∀ r ∈ rs, site r

private theorem fill {N : ℕ} (P : Program w C) (fuel : ℕ) (site : Report w → Prop)
    (address value : Fin N → Fin 13 → ℕ) (ready : Memory w → Prop)
    (consistent : ∀ i j f g, address i f = address j g → value i f = value j g)
    (keep : ∀ i m out, ready m → (∀ x, (∀ f, x ≠ address i f) → out x = m x) → ready out)
    (one : ∀ (i : Fin N) m, ready m → ∃ es,
      let r : Report w := ⟨es,some (Fin.ofNat _ (i.val+1))⟩
      execute P fuel (P.start (Fin.ofNat _ i.val)) m [] = some r ∧ site r ∧
      (∀ f, (after m es (address i f)).val = value i f) ∧
      ∀ x, (∀ f, x ≠ address i f) → after m es x = m x)
    (initial : Memory w) (start : ready initial) (k : ℕ) (hk : k ≤ N) :
    ∃ rs, Segment P fuel k site initial rs ∧ ready (after initial (eventLog rs)) ∧
      (∀ (i : Fin N), i.val < k → ∀ f, (after initial (eventLog rs) (address i f)).val = value i f) ∧
      ∀ x, (∀ (i : Fin N), i.val < k → ∀ f, x ≠ address i f) → after initial (eventLog rs) x = initial x := by
  classical
  induction k with
  | zero => exact ⟨[],⟨rfl,rfl,rfl,by simp,by simp⟩,start,by simp,fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨rs,run,input,previous,unchanged⟩ := ih (by omega)
    let i : Fin N := ⟨k,hk⟩
    let m := after initial (eventLog rs)
    obtain ⟨es,exec,legal,fields,frame⟩ := one i m input
    let r : Report w := ⟨es,some (Fin.ofNat _ (k+1))⟩
    have hm : after initial (eventLog (rs++[r])) = after m es := by
      simp only [eventLog,List.flatMap_append,List.flatMap_singleton,after,List.foldl_append,m,r]
    refine ⟨rs++[r],⟨?_,?_,by simp [run.length],?_,?_⟩,hm ▸ keep i m _ input frame,?_,?_⟩
    · rw [List.replicate_succ',PrimedSchedule.runSegment_append,run.executed]
      simp only [Option.bind_some,run.cursor,runSegment,Option.map_some]
      change (match execute P fuel (P.start (Fin.ofNat _ k)) m [] with
        | none => none | some a => some [a]).map (rs ++ ·) = some (rs ++ [r])
      rw [exec]; rfl
    · rw [endState_append]; rfl
    · intro j hj
      by_cases h : j < rs.length
      · rw [List.getElem_append_left h]; exact run.advance j h
      · rw [List.getElem_append_right (by omega)]
        have e : j = k := by simp only [List.length_append,List.length_singleton,run.length] at hj; rw [run.length] at h; omega
        subst j; simp [run.length,r]
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact run.sites _ hs
      · exact (List.mem_singleton.mp hs) ▸ legal
    · intro j hj f
      rw [hm]
      by_cases hit : ∃ g, address j f = address i g
      · obtain ⟨g,he⟩ := hit
        rw [he,fields,consistent j i f g he]
      · have hji : j ≠ i := fun he => hit ⟨f,he ▸ rfl⟩
        have hlt : j.val < k := by have hv : j.val ≠ k := fun e => hji (Fin.ext e); omega
        rw [frame _ (fun g he => hit ⟨g,he⟩)]
        exact previous j hlt f
    · intro x hx
      rw [hm,frame x (hx i (Nat.lt_succ_self _))]
      exact unchanged x (fun j hj => hx j (by omega))

/-- A segment's read and write regions are the union of the regions used by
its individual calls. -/
theorem Segment.footprint {P : Program w C} {fuel N site m rs} (h : Segment P fuel N site m rs)
    {readable writable : ℕ → Prop}
    (region : ∀ r, site r → SourceTransport.Reads readable r.events ∧ SourceTransport.Writes writable r.events) :
    SourceTransport.Reads readable (eventLog rs) ∧ SourceTransport.Writes writable (eventLog rs) := by
  constructor <;> intro a v hv <;> obtain ⟨r,hr,he⟩ := List.mem_flatMap.mp hv
  · exact (region r (h.sites r hr)).1 a v he
  · exact (region r (h.sites r hr)).2 a v he

/-- The four role passes can use the ordinary guarded dispatcher. Its bound
is exclusive, and the final cursor equals that bound. -/
theorem Segment.validTrace {P : Program w C} {fuel N site m rs} (h : Segment P fuel N site m rs)
    {d : ℕ} (catalog : Schedule.Catalog d) (worker : Fin d) (ports : Schedule.Ports w)
    (pub : Fin (catalog worker).params → Word w) (fit : N < 2^w)
    (keep : ∀ r, site r → ∀ mem, OrdinalRun.Preserved (catalog worker).params ports mem (after mem r.events))
    (active : Schedule.Ready catalog worker ports pub (Fin.ofNat _ N) m) :
    Schedule.ValidTrace catalog worker ports pub (Fin.ofNat _ N) 0 m rs ∧
      OrdinalRun.Preserved (catalog worker).params ports m (after m (eventLog rs)) := by
  let cursor := Fin.ofNat (2^w)
  have loop (j : ℕ) (mem : Memory w) (tail : List (Report w)) (len : j+tail.length=N)
      (sites : ∀ r ∈ tail, site r) (inc : ∀ k (hk : k < tail.length), tail[k].result = some (cursor (j+k+1)))
      (ready : Schedule.Ready catalog worker ports pub (cursor N) mem) :
      Schedule.ValidTrace catalog worker ports pub (cursor N) (cursor j) mem tail ∧
        OrdinalRun.Preserved (catalog worker).params ports mem (after mem (eventLog tail)) := by
    induction tail generalizing j mem with
    | nil =>
      have ej : j = N := by simpa only [List.length_nil,Nat.add_zero] using len
      exact ⟨⟨ready,ej ▸ le_rfl⟩,fun _ _ => rfl⟩
    | cons r tail ih =>
      have hj : j < N := by simp only [List.length_cons] at len; omega
      have guard : cursor j < cursor N := by
        change j % 2^w < N % 2^w
        rwa [Nat.mod_eq_of_lt (hj.trans fit),Nat.mod_eq_of_lt fit]
      have frame := keep r (sites r List.mem_cons_self) mem
      have next := OrdinalRun.ready_of_preserved catalog worker ports ready frame
      obtain ⟨rest,last⟩ := ih (j+1) _ (by simp only [List.length_cons] at len; omega)
        (fun s hs => sites s (List.mem_cons_of_mem r hs)) (fun k hk => by
          have succ := inc (k+1) (by simpa using hk)
          change tail[k].result = some (cursor (j+(k+1)+1)) at succ
          exact (show j+(k+1)+1 = (j+1)+k+1 by omega) ▸ succ) next
      have first : r.result = some (cursor (j+1)) := by exact inc 0 (by simp)
      refine ⟨⟨ready,guard,_,first,rest⟩,fun x hx => ?_⟩
      change after mem (r.events ++ eventLog tail) x = mem x
      rw [show after mem (r.events ++ eventLog tail) = after (after mem r.events) (eventLog tail) from List.foldl_append]
      exact (last x hx).trans (frame x hx)
  exact loop 0 m rs (by simpa using h.length) h.sites (by simpa only [Nat.zero_add] using h.advance) active

variable {n A : ℕ}

/-- All native calls of one fixed role, and all output rows in their shared
terminal memory. -/
structure RoleRun (T : Allocation w n A) (width : Id n → ℕ) (t : Fin 4)
    (P : Program w C) (fuel : ℕ) (site : Report w → Prop) (initial : Memory w) (rs : List (Report w)) : Prop
    extends Segment P fuel (n*T.subdiv t) site initial rs where
  images : ∀ i, Image (T.row (i,t)) (width (i,t)) (after initial (eventLog rs))
  frame : ∀ x, (∀ i, (T.row (i,t)).Outside x) → after initial (eventLog rs) x = initial x

variable {E : Fin 4 → Type*}

/-- Successive role programs start at zero, with the memory actually produced
by all earlier programs. Each list in `batches` is one role's native segment. -/
inductive Roles (T : Allocation w n A) (width : Id n → ℕ) (P : ∀ t, Program w (E t))
    (fuel : Fin 4 → ℕ) (site : Fin 4 → Report w → Prop) :
    List (Fin 4) → Memory w → Memory w → List (List (Report w)) → Prop where
  | nil (m : Memory w) : Roles T width P fuel site [] m m []
  | cons {t ts m out rs batches} : RoleRun T width t (P t) (fuel t) (site t) m rs →
      Roles T width P fuel site ts (after m (eventLog rs)) out batches →
      Roles T width P fuel site (t::ts) m out (rs::batches)

variable {T : Allocation w n A} {width : Id n → ℕ} {P : ∀ t, Program w (E t)}
variable {fuel : Fin 4 → ℕ} {site : Fin 4 → Report w → Prop} {ts : List (Fin 4)}
variable {m out : Memory w} {batches : List (List (Report w))}

theorem Roles.replay (h : Roles T width P fuel site ts m out batches) : after m (eventLog batches.flatten) = out := by
  induction h with
  | nil => rfl
  | cons head _ ih =>
    simp only [List.flatten_cons,eventLog,List.flatMap_append,after,List.foldl_append] at ih ⊢
    exact ih

theorem Roles.frame (h : Roles T width P fuel site ts m out batches) {x : ℕ}
    (outside : ∀ t ∈ ts, ∀ i, (T.row (i,t)).Outside x) : out x = m x := by
  induction h with
  | nil => rfl
  | cons head _ ih =>
    exact (ih fun _ ht => outside _ (List.mem_cons_of_mem _ ht)).trans (head.frame x (outside _ List.mem_cons_self))

theorem Roles.lengths (h : Roles T width P fuel site ts m out batches) :
    batches.map List.length = ts.map (fun t => n*T.subdiv t) := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons,head.length,ih]

/-- Recover an individual native role segment at its actual starting memory.
The preceding batches are replayed in chronological order. -/
theorem Roles.get (h : Roles T width P fuel site ts m out batches) (j : ℕ) (hj : j < ts.length) :
    ∃ rs, batches[j]? = some rs ∧ RoleRun T width ts[j] (P ts[j]) (fuel ts[j]) (site ts[j])
      (after m (eventLog (batches.take j).flatten)) rs := by
  induction h generalizing j with
  | nil => simp at hj
  | @cons t ts m out rs tail head _ ih =>
    cases j with
    | zero => exact ⟨rs,rfl,head⟩
    | succ j =>
      have lt : j < ts.length := by simpa using hj
      obtain ⟨last,hindex,hrun⟩ := ih j lt
      refine ⟨last,hindex,?_⟩
      change RoleRun T width ts[j] (P ts[j]) (fuel ts[j]) (site ts[j])
        (after m (eventLog (rs ++ (tail.take j).flatten))) last
      simpa only [eventLog,List.flatMap_append,after,List.foldl_append] using hrun

theorem Roles.roleAt (h : Roles T width P fuel site (List.finRange 4) m out batches) (t : Fin 4) :
    ∃ rs, batches[t.val]? = some rs ∧ RoleRun T width t (P t) (fuel t) (site t)
      (after m (eventLog (batches.take t.val).flatten)) rs := by
  have lt : t.val < (List.finRange 4).length := by simp
  obtain ⟨rs,entry,hrun⟩ := h.get t.val lt
  have atRole : (List.finRange 4)[t.val] = t := by simp
  exact ⟨rs,entry,Eq.mp (congrArg (fun i => RoleRun T width i (P i) (fuel i) (site i)
    (after m (eventLog (batches.take t.val).flatten)) rs) atRole) hrun⟩

theorem Roles.sites (h : Roles T width P fuel site ts m out batches) {r : Report w}
    (hr : r ∈ batches.flatten) : ∃ t ∈ ts, site t r := by
  induction h with
  | nil => simp at hr
  | @cons t ts m out rs tail head _ ih =>
    rcases List.mem_append.mp (show r ∈ rs ++ tail.flatten from hr) with hh | ht
    · exact ⟨t,List.mem_cons_self,head.sites r hh⟩
    · obtain ⟨v,hv,hsite⟩ := ih ht
      exact ⟨v,List.mem_cons_of_mem t hv,hsite⟩

theorem Roles.calls (h : Roles T width P fuel site (List.finRange 4) m out batches) :
    batches.flatten.length = n*T.stride := by
  rw [List.length_flatten,h.lengths,← List.ofFn_eq_map,List.sum_ofFn,Allocation.stride,Finset.mul_sum]

/-- The four role stages leave the complete endpoint tables of every motif
simultaneously readable. Their per-role traces have exactly `n * subdiv t` calls. -/
theorem four (fit : T.Fits) (ready : Memory w → Prop)
    (worker : ∀ t mem, ready mem → ∃ rs, RoleRun T width t (P t) (fuel t) (site t) mem rs ∧
      ready (after mem (eventLog rs))) (initial : Memory w) (input : ready initial) :
    ∃ out batches, Roles T width P fuel site (List.finRange 4) initial out batches ∧
      ready out ∧ (∀ i, Image (T.row i) (width i) out) ∧
      (∀ x, (∀ i, (T.row i).Outside x) → out x = initial x) ∧
      batches.map List.length = List.ofFn (fun t => n*T.subdiv t) := by
  have scan (ts : List (Fin 4)) (nd : ts.Nodup) (m : Memory w) (hm : ready m) :
      ∃ out batches, Roles T width P fuel site ts m out batches ∧ ready out ∧
        ∀ t ∈ ts, ∀ i, Image (T.row (i,t)) (width (i,t)) out := by
    induction ts generalizing m with
    | nil => exact ⟨m,[],.nil m,hm,by simp⟩
    | cons t ts ih =>
      obtain ⟨rs,head,next⟩ := worker t m hm
      obtain ⟨missing,unique⟩ := List.nodup_cons.mp nd
      obtain ⟨out,tail,run,last,rows⟩ := ih unique _ next
      refine ⟨out,rs::tail,.cons head run,last,fun s hs i => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · apply (head.images i).keep
        intro x hx
        apply run.frame
        intro v hv j
        apply T.separate fit (i := (i,s)) (j := (j,v)) _ x hx
        intro eqn
        have eqRole : s = v := congrArg Prod.snd eqn
        exact missing (eqRole.symm ▸ hv)
      · exact rows s hs i
  obtain ⟨out,bs,done,hr,rows⟩ := scan (List.finRange 4) (List.nodup_finRange _) initial input
  exact ⟨out,bs,done,hr,fun i => rows i.2 (List.mem_finRange i.2) i.1,
    fun x hx => done.frame (fun t _ i => hx (i,t)),by simpa only [List.ofFn_eq_map] using done.lengths⟩

/-- Local specification of the native program at a dense motif and subdivision.
The single ordinal is computed from these two indices without external advice. -/
def One (T : Allocation w n A) (width : Id n → ℕ) (ready : Memory w → Prop) (t : Fin 4)
    (P : Program w C) (fuel : ℕ) (site : Report w → Prop) : Prop :=
  ∀ (i : Fin n) (j : Fin (T.subdiv t)) (m : Memory w), ready m → ∃ es,
    let k := i.val*T.subdiv t+j.val
    let r : Report w := ⟨es,some (Fin.ofNat _ (k+1))⟩
    execute P fuel (P.start (Fin.ofNat _ k)) m [] = some r ∧ site r ∧
      (∀ f, (after m es (SurvivingCells.address (T.row (i,t)) j.val f)).val =
        SurvivingCells.value (width (i,t)) (T.subdiv t) j.val f) ∧
      ∀ x, (∀ f, x ≠ SurvivingCells.address (T.row (i,t)) j.val f) → after m es x = m x

/-- Run all subdivisions of a single role. Equal-address writes agree, whether
shared by two subdivisions or made at the last unfilled position. -/
theorem role {Q : Program w C} {cap : ℕ} {ok : Report w → Prop}
    (fit : T.Fits) (ready : Memory w → Prop) (t : Fin 4)
    (keep : ∀ i m out, ready m → (∀ x, (T.row i).Outside x → out x = m x) → ready out)
    (worker : One T width ready t Q cap ok) (initial : Memory w) (input : ready initial) :
    ∃ rs, RoleRun T width t Q cap ok initial rs ∧ ready (after initial (eventLog rs)) := by
  let pieces := T.subdiv t
  let decode : Fin (n*pieces) ≃ Fin n × Fin pieces := finProdFinEquiv.symm
  let row (k : Fin (n*pieces)) := ((decode k).1,t)
  let piece (k : Fin (n*pieces)) := (decode k).2.val
  let addr k := SurvivingCells.address (T.row (row k)) (piece k)
  let val k := SurvivingCells.value (width (row k)) pieces (piece k)
  have count (i : Fin n) : (T.row (i,t)).count.val = pieces := (T.row_vals fit (i,t)).2.2.2.2
  have bound (k : Fin (n*pieces)) : piece k < (T.row (row k)).count.val := by
    rw [show (T.row (row k)).count.val = pieces from count _]; exact (decode k).2.isLt
  have inside (k : Fin (n*pieces)) (f : Fin 13) : ¬ (T.row (row k)).Outside (addr k f) :=
    SurvivingCells.inside (bound k) f
  have consistent (i j : Fin (n*pieces)) (f g : Fin 13) (e : addr i f = addr j g) : val i f = val j g := by
    by_cases same : row i = row j
    · change SurvivingCells.address (T.row (row i)) (piece i) f = SurvivingCells.address (T.row (row j)) (piece j) g at e
      change SurvivingCells.value (width (row i)) pieces (piece i) f = SurvivingCells.value (width (row j)) pieces (piece j) g
      rw [same] at e ⊢
      rw [← count (decode j).1]
      exact SurvivingCells.same_value (T.space fit (row j)) (T.apart fit (row j)) (same ▸ bound i) (bound j) e
    · have outside := T.separate fit same (addr i f) (inside i f)
      exact False.elim (inside j g (e ▸ outside))
  have retain (k : Fin (n*pieces)) (m out : Memory w) (hm : ready m)
      (frame : ∀ x, (∀ f, x ≠ addr k f) → out x = m x) : ready out :=
    keep (row k) m out hm (fun x hx => frame x (fun f he => inside k f (he ▸ hx)))
  have calls (k : Fin (n*pieces)) (m : Memory w) (hm : ready m) := worker (decode k).1 (decode k).2 m hm
  have ordinal (k : Fin (n*pieces)) : (decode k).1.val*T.subdiv t+(decode k).2.val = k.val := by
    have e := congrArg Fin.val (finProdFinEquiv.apply_symm_apply k)
    change (decode k).2.val+pieces*(decode k).1.val = k.val at e
    change (decode k).1.val*pieces+(decode k).2.val = k.val
    rw [← e]; ac_rfl
  obtain ⟨rs,run,next,fields,frame⟩ := fill Q cap ok addr val ready consistent retain
    (fun k m hm => by simpa only [ordinal k] using calls k m hm) initial input (n*pieces) le_rfl
  refine ⟨rs,⟨run,?_,?_⟩,next⟩
  · intro i
    have positive : 0 < (T.row (i,t)).count.val := (count i).symm ▸ fit.positive t
    apply SurvivingWords.image _ positive (T.space fit (i,t)).fits
    apply SurvivingCells.words_of_fields _ positive
    intro j f
    let part : Fin pieces := ⟨j.val,(count i) ▸ j.isLt⟩
    let k := decode.symm (i,part)
    have he : (after initial (eventLog rs) (SurvivingCells.address (T.row (i,t)) j.val f)).val =
        SurvivingCells.value (width (i,t)) pieces j.val f := by
      simpa only [addr,val,row,piece,k,Equiv.apply_symm_apply,part] using fields k k.isLt f
    exact he.trans (congrArg (fun q => SurvivingCells.value (width (i,t)) q j.val f) (count i).symm)
  · intro x outside
    exact frame x (fun k _ f he => inside k f (he ▸ outside (decode k).1))

/-- Execute all four rectangular passes in role order. The frames of earlier
roles and the read-only directory survive, and every resulting interval image
has the chosen width. -/
theorem full (fit : T.Fits) (ready : Memory w → Prop)
    (keep : ∀ i m out, ready m → (∀ x, (T.row i).Outside x → out x = m x) → ready out)
    (workers : ∀ t, One T width ready t (P t) (fuel t) (site t))
    (initial : Memory w) (input : ready initial) :
    ∃ out batches, Roles T width P fuel site (List.finRange 4) initial out batches ∧
      ready out ∧ (∀ i, Image (T.row i) (width i) out) ∧
      (∀ x, (∀ i, (T.row i).Outside x) → out x = initial x) ∧
      batches.map List.length = List.ofFn (fun t => n*T.subdiv t) :=
  four fit ready (fun t m hm => role fit ready t keep (workers t) m hm) initial input

end CompressorRecords.ShrinkSliceSweep.SurvivingPass

end VPVNP
end Computability
end OAI
