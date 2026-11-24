import OAI.Computability.VPVNP.CompressorTermWorkerRun
import OAI.Computability.VPVNP.CompressorTermRecordScan

/-!
# A complete motif pass of the fixed native program

The native RAM starts at ordinal zero and returns the successor on every
admitted row. Its execution on a list of row tapes has the same final memory
as the five-call descriptor scan. Disjoint term rows preserve all demand
inputs as well as the descriptors already written.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker

open BurstRAM PrimedInputRAM TermRecordScan MotifGrid MotifBlocks MotifConversion MotifSelector
open scoped Fin.CommRing

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
variable {m d n w : ℕ} (order : Fin d ≃ D) (supply : Fin n ≃ S)

/-- Public address operands describe every ordinal in the supplied layout. -/
def Addresses (L : Layout m d n w) (addr : Fin 4 → BurstRAM.Word w) : Prop :=
  ∀ i, source addr (i.val : BurstRAM.Word w) = L.source i ∧ base addr (i.val : BurstRAM.Word w) = L.base i

theorem addresses_strided (src dst srcStride termStride : ℕ) (hd : d ≤ srcStride) (hn : 2+n ≤ termStride)
    (hsep : src+m*srcStride ≤ dst) (hfit : dst+m*termStride < 2^w) :
    Addresses (strided m d n w src dst srcStride termStride hd hn hsep hfit)
      ![src,srcStride,dst,termStride] := fun i => strided_addresses w src dst srcStride termStride i.val

private theorem row_unique {α : Type*} {xs : List α} (nodup : xs.Nodup) {i j : ℕ} {x : α}
    (hi : xs[i]? = some x) (hj : xs[j]? = some x) : i = j := by
  obtain ⟨hi,ei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj,ej⟩ := List.getElem?_eq_some_iff.mp hj
  exact nodup.getElem_inj_iff.mp (ei.trans ej.symm)

/-- Native strided motif program instantiated with the grid, column orders, and four address
operands. -/
noncomputable abbrev program (addr : Fin 4 → BurstRAM.Word w) :=
  ((motifPass B order n).table.instantiate w (motifData B order supply w addr)).program

private structure RowEffect (L : Layout m d n w) (demand : Fin m → D → ℕ) (M : ℕ) (i : Fin m)
    (initial : Memory w) (fresh : Report w) (old : List (Report w)) : Prop where
  cursor : fresh.result = some ((i.val+1 : ℕ) : BurstRAM.Word w)
  memory : after initial fresh.events = after initial (eventLog old)
  inputs : Inputs order L demand (after initial fresh.events)
  frame : ∀ x, L.Outside i x → after initial fresh.events x = initial x
  probes : fresh.probes ≤ probesPerRow B d n
  steps : fresh.events.length < budget B d n w M

private def Ready (L : Layout m d n w) (addr : Fin 4 → BurstRAM.Word w) (demand : Fin m → D → ℕ) (M cap : ℕ) :=
  ∀ mem, Inputs order L demand mem → ∀ (i : Fin m) (bits : List Bool),
    let T := program B order supply addr
    Option.Rel (RowEffect B order L demand M i mem)
      (execute T cap (T.start (i.val : BurstRAM.Word w)) mem bits)
      (TermRecord.run B order supply (L.source i) (L.base i) mem (prepFuel (p := p) d M) bits)

private theorem row_ready (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ m M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (L : Layout m d n w) addr,
      Addresses L addr → ∀ (demand : Fin m → D → ℕ), (∀ i e, demand i e ≤ M) →
      ∀ cap, budget B d n w M ≤ cap → Ready B order supply L addr demand M cap := by
  obtain ⟨kn,native⟩ := native B order supply hp hq
  obtain ⟨ko,original⟩ := TermRecord.run_spec B order supply hp hq
  refine ⟨max kn ko,fun m M w hW L addr haddr demand hD cap hcap mem hin i bits => ?_⟩
  let j : BurstRAM.Word w := i.val
  have hkn := le_max_left kn ko
  have hko := le_max_right kn ko
  have hn := native M w (by omega) addr j mem
  dsimp only at hn
  rw [(haddr i).1,(haddr i).2] at hn
  obtain ⟨hw,row,u,hrow,hu,hf⟩ := hn (L.sourceFits i) (L.termFits i) (L.separate i i) ((hin i) ▸ hD i)
  obtain ⟨hw',row',u',hrow',hu',ha,complete⟩ :=
    original M w (by omega) (L.source i) (L.base i) mem (L.sourceFits i) (L.termFits i)
      (L.separate i i) ((hin i) ▸ hD i)
  obtain ⟨hnative,selected⟩ := hf cap hcap
  have hroweq : row = row' := Fin.ext (row_unique (Finset.nodup_toList _) hrow hrow')
  have hueq : u = u' := Fin.ext (hu.trans hu'.symm)
  subst row' u'
  let T := program B order supply addr
  let old := TermRecord.run B order supply (L.source i) (L.base i) mem (prepFuel (p := p) d M)
  change Option.Rel _ (execute T cap (T.start j) mem bits) (old bits)
  cases hs : execute T cap (T.start j) mem bits with
  | none =>
    have ho : old bits = none := by
      apply Option.not_isSome_iff_eq_none.mp
      intro hsome
      have h := (hnative bits).mpr ((ha bits).mp hsome)
      change (execute T cap (T.start j) mem bits).isSome at h
      simp [hs] at h
    rw [ho]; exact .none
  | some fresh =>
    obtain ⟨v,read⟩ := (hnative bits).mp (by change (execute T cap (T.start j) mem bits).isSome; simp [hs])
    have hbs : bits = (outerReader B supply hq _ w hw).encode v := by
      simpa only [List.append_nil] using (ChoiceReader.read_iff ..).mp read
    obtain ⟨es,he,hm,_,hprobe,hlen⟩ := selected v
    rw [← hbs] at he
    change execute T cap (T.start j) mem bits = some _ at he
    rw [hs] at he
    cases Option.some.inj he
    obtain ⟨rs,ho,_,hmem,_,_,_⟩ := complete v
    rw [← hbs] at ho
    change old bits = some rs at ho
    rw [ho]
    have frame : ∀ x, L.Outside i x → after mem es x = mem x := by
      intro x hx
      rw [hm]
      exact (TermRecord.recordMemory_fields mem (L.base i) row u supply v.val (L.termFits i)).2.2.2 x hx
    exact .some ⟨by simp [j],hm.trans hmem.symm,inputs_after order L hin i frame,frame,hprobe,hlen⟩

/-- Any successful call at a valid row ordinal returns its successor and
preserves every demand input and every cell outside that row's descriptor.
This includes the dispatch frame when it is allocated outside the term rows. -/
theorem call_frame (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ m M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (L : Layout m d n w) addr,
      Addresses L addr → ∀ (demand : Fin m → D → ℕ), (∀ i e, demand i e ≤ M) →
      ∀ cap, budget B d n w M ≤ cap → ∀ mem, Inputs order L demand mem →
      ∀ (i : Fin m) (bits : List Bool) (rep : Report w),
        let T := program B order supply addr
        execute T cap (T.start (i.val : BurstRAM.Word w)) mem bits = some rep →
        rep.result = some ((i.val+1 : ℕ) : BurstRAM.Word w) ∧ Inputs order L demand (after mem rep.events) ∧
          (∀ x, L.Outside i x → after mem rep.events x = mem x) ∧ rep.probes ≤ probesPerRow B d n ∧
          rep.events.length < budget B d n w M := by
  obtain ⟨K,hw⟩ := row_ready B order supply hp hq
  refine ⟨K,fun m M w hW L addr ha demand hD cap hc mem hin i bs r hr => ?_⟩
  have he := hw m M w hW L addr ha demand hD cap hc mem hin i bs
  dsimp only at he
  rw [hr] at he
  cases ho : TermRecord.run B order supply (L.source i) (L.base i) mem (prepFuel (p := p) d M) bs with
  | none => rw [ho] at he; cases he
  | some old =>
    rw [ho] at he
    cases he with | some h => exact ⟨h.cursor,h.inputs,h.frame,h.probes,h.steps⟩

private structure PassEffect (start M : ℕ) (ids : List (Fin m)) (initial : Memory w)
    (fresh old : List (Report w)) : Prop where
  memory : after initial (eventLog fresh) = after initial (eventLog old)
  cursor : endState (some (start : BurstRAM.Word w)) fresh = some ((start+ids.length : ℕ) : BurstRAM.Word w)
  length : fresh.length = ids.length
  probes : countProbes (eventLog fresh) ≤ ids.length * probesPerRow B d n
  steps : (eventLog fresh).length ≤ ids.length * budget B d n w M
  sites : ∀ r ∈ fresh, r.events.length < budget B d n w M

private theorem paired {L : Layout m d n w} {addr : Fin 4 → BurstRAM.Word w} {demand : Fin m → D → ℕ}
    {M cap : ℕ} (ready : Ready B order supply L addr demand M cap) (tapes : Fin m → List Bool)
    (ids : List (Fin m)) (start : ℕ) (sorted : ids.map Fin.val = List.range' start ids.length)
    (mem : Memory w) (hin : Inputs order L demand mem) :
    Option.Rel (PassEffect (d := d) (n := n) B start M ids mem)
      (runSegment (program B order supply addr) cap (some (start : BurstRAM.Word w)) mem (ids.map tapes))
      (walk B order supply L (prepFuel (p := p) d M) tapes ids mem) := by
  induction ids generalizing start mem with
  | nil =>
    exact .some ⟨rfl,rfl,rfl,by simp [eventLog,countProbes],by simp [eventLog],by simp⟩
  | cons i ids ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] at sorted
    obtain ⟨rfl,htail⟩ := sorted
    let T := program B order supply addr
    let old := TermRecord.run B order supply (L.source i) (L.base i) mem (prepFuel (p := p) d M) (tapes i)
    let fresh := execute T cap (T.start (i.val : BurstRAM.Word w)) mem (tapes i)
    have both : Option.Rel _ fresh old := ready mem hin i (tapes i)
    cases hf : fresh with
    | none =>
      cases ho : old with
      | none =>
        change Option.Rel _ (match fresh with | none => none | some _ => _) (old.bind _)
        rw [hf,ho]; exact .none
      | some o => rw [hf,ho] at both; cases both
    | some f =>
      cases ho : old with
      | none => rw [hf,ho] at both; cases both
      | some o =>
        rw [hf,ho] at both
        cases both with | some effect =>
        let next := after mem f.events
        have tails := ih (i.val+1) htail next effect.inputs
        simp only [List.map_cons,runSegment,walk,bind]
        change Option.Rel _ (match fresh with | none => none | some f => _) (old.bind _)
        rw [hf,ho]
        simp only [Option.bind_some,effect.cursor,← effect.memory]
        cases ht : runSegment T cap (some ((i.val+1 : ℕ) : BurstRAM.Word w)) next (ids.map tapes) with
        | none =>
          cases hto : walk B order supply L (prepFuel (p := p) d M) tapes ids next with
          | none => exact .none
          | some _ => rw [ht,hto] at tails; cases tails
        | some fs =>
          cases hto : walk B order supply L (prepFuel (p := p) d M) tapes ids next with
          | none => rw [ht,hto] at tails; cases tails
          | some os =>
            rw [ht,hto] at tails
            cases tails with | some effects =>
            refine .some ⟨?_,?_,?_,?_,?_,?_⟩
            · change after mem (f.events++eventLog fs) = after mem (eventLog (o++os))
              rw [show after mem (f.events++eventLog fs) = after next (eventLog fs) from List.foldl_append]
              rw [effects.memory,show eventLog (o++os) = eventLog o ++ eventLog os from List.flatMap_append,
                show after mem (eventLog o ++ eventLog os) = after (after mem (eventLog o)) (eventLog os) from List.foldl_append,
                ← effect.memory]
            · change endState f.result fs = _
              rw [effect.cursor,effects.cursor]
              simp [Nat.add_assoc,Nat.add_comm 1]
            · simp [effects.length]
            · change countProbes (f.events++eventLog fs) ≤ (ids.length+1)*probesPerRow B d n
              rw [DemandPreparation.probes_append,Nat.succ_mul]
              have h := effect.probes
              change countProbes f.events ≤ _ at h
              exact (Nat.add_le_add h effects.probes).trans_eq (Nat.add_comm ..)
            · change (f.events++eventLog fs).length ≤ (ids.length+1)*budget B d n w M
              rw [List.length_append,Nat.succ_mul]
              exact (Nat.add_le_add effect.steps.le effects.steps).trans_eq (Nat.add_comm ..)
            · intro r hr
              rcases List.mem_cons.mp hr with rfl | h
              · exact effect.steps
              · exact effects.sites r h

private theorem ordinal_order (m : ℕ) : (List.finRange m).map Fin.val = List.range' 0 (List.finRange m).length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem isSome_iff_of_rel {X Y : Type*} {r : X → Y → Prop} {x : Option X} {y : Option Y}
    (h : Option.Rel r x y) : x.isSome ↔ y.isSome := by cases h <;> rfl

/-- One fixed native table traverses the complete layout. Each vector family
determines one successful tape tuple, and all stored row headers and supply
fields survive in the final memory. -/
theorem scan_native (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ m M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (L : Layout m d n w) addr,
      Addresses L addr → ∀ (demand : Fin m → D → ℕ), (∀ i e, demand i e ≤ M) →
      ∀ (mem : Memory w), Inputs order L demand mem → ∀ cap, budget B d n w M ≤ cap →
      let T := program B order supply addr
      let run := fun tapes : Fin m → List Bool => runSegment T cap (some 0) mem (List.ofFn tapes)
      (∀ tapes, (run tapes).isSome ↔ ∃! v : Choices B demand,
        tapes = fun i => tape B supply (demand i) w (v i).val) ∧
      ∀ v : Choices B demand, ∃ rs, run (fun i => tape B supply (demand i) w (v i).val) = some rs ∧
        (∀ i, Fields B supply hp (demand i) (v i).val (L.base i) (after mem (eventLog rs))) ∧
        (∀ x, (∀ i, L.Outside i x) → after mem (eventLog rs) x = mem x) ∧
        endState (some (0 : BurstRAM.Word w)) rs = some (m : BurstRAM.Word w) ∧
        rs.length = m ∧ branchPaths rs = List.ofFn (fun i => tape B supply (demand i) w (v i).val) ∧
        countProbes (eventLog rs) ≤ m*probesPerRow B d n ∧ (eventLog rs).length ≤ m*budget B d n w M := by
  obtain ⟨kw,workers⟩ := row_ready B order supply hp hq
  obtain ⟨kr,records⟩ := TermRecordScan.run_spec B order supply hp hq
  refine ⟨max kw kr,fun m M w hW L addr addrs demand hD mem hin cap hcap => ?_⟩
  have hkw := le_max_left kw kr
  have hkr := le_max_right kw kr
  have ready := workers m M w (by omega) L addr addrs demand hD cap hcap
  obtain ⟨legal,full⟩ := records m M w (by omega) L demand hD mem hin
  let ids := List.finRange m
  let run := fun tapes : Fin m → List Bool => runSegment (program B order supply addr) cap (some 0) mem (List.ofFn tapes)
  have sync (tapes : Fin m → List Bool) :
      Option.Rel (PassEffect (d := d) (n := n) B 0 M ids mem) (run tapes)
        (walk B order supply L (prepFuel (p := p) d M) tapes ids mem) := by
    simpa only [run,ids,List.ofFn_eq_map,Nat.cast_zero] using paired B order supply ready tapes ids 0 (ordinal_order m) mem hin
  refine ⟨fun tapes => (isSome_iff_of_rel (sync tapes)).trans (legal tapes),fun v => ?_⟩
  let bs := fun i => tape B supply (demand i) w (v i).val
  obtain ⟨old,ho,fields,frame,_⟩ := full v
  change walk B order supply L (prepFuel (p := p) d M) bs ids mem = some old at ho
  have he := sync bs
  rw [ho] at he
  cases hf : run bs with
  | none => rw [hf] at he; cases he
  | some fresh =>
    rw [hf] at he
    cases he with | some effect =>
    have branches := ((runSegment_iff ..).mp hf).2.2
    refine ⟨fresh,hf,?_,?_,?_,?_,branches,?_,?_⟩
    · rw [effect.memory]; exact fields
    · rw [effect.memory]; exact frame
    · simpa only [ids,List.length_finRange,Nat.zero_add,Nat.cast_zero] using effect.cursor
    · simpa only [ids,List.length_finRange] using effect.length
    · simpa only [ids,List.length_finRange] using effect.probes
    · simpa only [ids,List.length_finRange] using effect.steps

/-- The local resource bound applies to each reset call even when the full
segment runs with a larger instruction cap. -/
theorem scan_site_bound (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ m M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (L : Layout m d n w) addr,
      Addresses L addr → ∀ (demand : Fin m → D → ℕ), (∀ i e, demand i e ≤ M) →
      ∀ (mem : Memory w), Inputs order L demand mem → ∀ cap, budget B d n w M ≤ cap →
      ∀ (tapes : Fin m → List Bool) (rs : List (Report w)),
        runSegment (program B order supply addr) cap (some 0) mem (List.ofFn tapes) = some rs →
        ∀ r ∈ rs, r.events.length < budget B d n w M := by
  obtain ⟨K,hw⟩ := row_ready B order supply hp hq
  refine ⟨K,fun m M w hW L addr haddr demand hD mem hin cap hcap tapes rs hr => ?_⟩
  let ids := List.finRange m
  have sync := paired B order supply (hw m M w hW L addr haddr demand hD cap hcap) tapes ids 0
    (ordinal_order m) mem hin
  have he : runSegment (program B order supply addr) cap (some ((0 : ℕ) : BurstRAM.Word w)) mem (ids.map tapes)
      = some rs := by simpa only [ids,Nat.cast_zero,← List.ofFn_eq_map] using hr
  rw [he] at sync
  cases ho : walk B order supply L (prepFuel (p := p) d M) tapes ids mem with
  | none => rw [ho] at sync; cases sync
  | some os => rw [ho] at sync; cases sync with | some h => exact h.sites

end CompressorRecords.TermWorker

end VPVNP
end Computability
end OAI
