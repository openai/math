import OAI.Computability.VPVNP.CompressorTermRecord

/-!
# Ordered native term-record scans for a compressor pass

Each motif has a contiguous input demand row and a disjoint output descriptor.
The scan threads the post-call memory into the next motif. Every legal outer
choice is therefore counted once and all emitted rows are still available to
the later score and slice scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermRecordScan

open BurstRAM MotifGrid MotifBlocks MotifConversion MotifSelector

variable {m d n w : ℕ}

/-- The rows may have arbitrary identifiers. Demand words are read-only and
term rows have two headers followed by the supply coordinates. -/
structure Layout (m d n w : ℕ) where
  /-- First address of the contiguous input demand widths for each motif. -/
  source : Fin m → BurstRAM.Word w
  /-- First address of the disjoint output term descriptor for each motif. -/
  base : Fin m → BurstRAM.Word w
  sourceFits : ∀ i, (source i).val + d ≤ 2^w
  termFits : ∀ i, (base i).val + 2 + n < 2^w
  separate : ∀ i j, (source j).val + d ≤ (base i).val ∨ (base i).val + 2+n ≤ (source j).val
  different : ∀ i j, i ≠ j →
    (base j).val + 2+n ≤ (base i).val ∨ (base i).val + 2+n ≤ (base j).val

/-- The address lies outside the grid index, repetition count, and payload columns of motif
`i`'s descriptor. -/
def Layout.Outside (L : Layout m d n w) (i : Fin m) (x : ℕ) : Prop :=
  x < (L.base i).val ∨ (L.base i).val + 2+n ≤ x

/-- A dense or strided directory of demand rows followed by disjoint
descriptor rows is a concrete instance of the scan's address layout. -/
def strided (m d n w src dst srcStride termStride : ℕ)
    (hd : d ≤ srcStride) (hn : 2+n ≤ termStride)
    (hsep : src + m*srcStride ≤ dst) (hfit : dst + m*termStride < 2^w) :
    Layout m d n w := by
  let source (i : Fin m) : BurstRAM.Word w := Fin.ofNat _ (src+i.val*srcStride)
  let base (i : Fin m) : BurstRAM.Word w := Fin.ofNat _ (dst+i.val*termStride)
  have sup (i : Fin m) : src+i.val*srcStride + d ≤ dst := by
    have h := Nat.mul_le_mul_right srcStride (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    omega
  have endFits (i : Fin m) : dst+i.val*termStride + 2+n < 2^w := by
    have h := Nat.mul_le_mul_right termStride (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    omega
  have hs (i : Fin m) : (source i).val = src+i.val*srcStride :=
    Nat.mod_eq_of_lt (by have := sup i; omega)
  have hb (i : Fin m) : (base i).val = dst+i.val*termStride :=
    Nat.mod_eq_of_lt (by have := endFits i; omega)
  refine ⟨source,base,fun i => ?_,fun i => ?_,fun i j => Or.inl ?_,fun i j hne => ?_⟩
  · rw [hs]; exact (sup i).trans (by omega)
  · rw [hb]; exact endFits i
  · rw [hs,hb]; exact (sup j).trans (Nat.le_add_right ..)
  · rw [hb,hb]
    have step (i j : Fin m) (h : i.val < j.val) : i.val*termStride + 2+n ≤ j.val*termStride := by
      have h' := Nat.mul_le_mul_right termStride (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at h'
      omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · right; have := step i j h; omega
    · left; have := step j i h; omega

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
variable (order : Fin d ≃ D) (supply : Fin n ≃ S) (L : Layout m d n w)

/-- Expected demand vectors of a pass, read from the given memory. -/
def Inputs (demand : Fin m → D → ℕ) (mem : Memory w) : Prop :=
  ∀ i, DemandPreparation.demandAt order (L.source i) mem = demand i

/-- Exact row contents for an individual motif. -/
def Fields (hp : ∀ i, 0 < p i) (demand : D → ℕ) (v : S → ℕ) (base : BurstRAM.Word w) (mem : Memory w) : Prop :=
  B.grid.demands.toList[(mem base.val).val]? = some (demandGrid B hp demand).val ∧
    (mem (base.val+1)).val = repetitions B demand ∧
    ∀ j, (mem (base.val+2+j.val)).val = v (supply j)

/-- Canonical branch bits for an individual descriptor. -/
def tape (demand : D → ℕ) (w : ℕ) (v : S → ℕ) : List Bool :=
  (List.ofFn fun i => PrimedCounter.digits (coordinateBits B demand w) (v (supply i))).flatten

theorem tape_eq (demand : D → ℕ) (hq : ∀ i, 0 < q i) (v : ↥(outerIndices B demand))
    (hw : outerCap B demand < 2^w) : (outerReader B supply hq demand w hw).encode v = tape B supply demand w v.val := by
  have he := (ChoiceReader.read_iff (outerReader B supply hq demand w hw) _ v []).mpr (List.append_nil _).symm
  simpa [tape] using (read_outer_iff B supply hq demand w hw _ [] v).mp he

/-- Instruction cap for computing the repetition count from `d` demand widths bounded by `M`. -/
def prepFuel (d M : ℕ) := 6*d+7*((∑ i, MotifAdmission.weight p i).size+2*Nat.clog 2 (M+1))+10

/-- One uniform event budget and one probe budget apply to every motif in the pass. -/
noncomputable def eventsPerRow (d n w M : ℕ) := 6*d+(11*d+4)*B.grid.demands.toList.length+8 +
  prepFuel (p := p) d M+8+PayloadWrite.storedFuel B n w

/-- Probe bound for constructing one term record, including grid search, repetition
preparation, and payload stores. -/
noncomputable def probesPerRow (d n : ℕ) := d+B.grid.demands.toList.length*d+d+n+3

/-- Execute the five reset calls at each visited motif, threading the physical
external memory and preserving every report in order. -/
noncomputable def walk (fuel : ℕ) (tapes : Fin m → List Bool) : List (Fin m) → Memory w → Option (List (Report w))
  | [], _ => some []
  | i :: is, mem => do
    let head ← TermRecord.run B order supply (L.source i) (L.base i) mem fuel (tapes i)
    let tail ← walk fuel tapes is (after mem (eventLog head))
    return head ++ tail

private structure Visit (hp : ∀ i, 0 < p i) (demand : D → ℕ) (i : Fin m) (v : S → ℕ)
    (M : ℕ) (initial : Memory w) (rs : List (Report w)) : Prop where
  fields : Fields B supply hp demand v (L.base i) (after initial (eventLog rs))
  frame : ∀ x, L.Outside i x → after initial (eventLog rs) x = initial x
  length : rs.length = 5
  bits : branchPaths rs = [[],[],[],[],tape B supply demand w v]
  probes : countProbes (eventLog rs) ≤ probesPerRow B d n
  steps : (eventLog rs).length ≤ eventsPerRow B d n w M

private def Ready (hp : ∀ i, 0 < p i) (demand : Fin m → D → ℕ) (M : ℕ) : Prop :=
  ∀ (mem : Memory w), Inputs order L demand mem → ∀ i,
    let call := TermRecord.run B order supply (L.source i) (L.base i) mem (prepFuel (p := p) d M)
    (∀ bs, (call bs).isSome ↔ ∃ v : ↥(outerIndices B (demand i)), bs = tape B supply (demand i) w v.val) ∧
    ∀ v : ↥(outerIndices B (demand i)), ∃ rs, call (tape B supply (demand i) w v.val) = some rs ∧
      Visit B supply L hp (demand i) i v.val M mem rs

private theorem ready (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ m M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (L : Layout m d n w) (demand : Fin m → D → ℕ),
      (∀ i e, demand i e ≤ M) → Ready B order supply L hp demand M := by
  obtain ⟨K,hK⟩ := TermRecord.run_spec B order supply hp hq
  refine ⟨K,fun m M w hW L demand hD mem hmem i => ?_⟩
  have hd := hmem i
  have all := hK M w hW (L.source i) (L.base i) mem (L.sourceFits i) (L.termFits i) (L.separate i i) (hd ▸ hD i)
  dsimp only at all
  rw [hd] at all
  obtain ⟨hw,row,u,hr,hu,hs,complete⟩ := all
  dsimp only
  constructor
  · intro bits
    unfold prepFuel
    rw [hs]
    exact exists_congr fun v => by rw [ChoiceReader.read_iff, List.append_nil, tape_eq B supply _ hq v hw]
  · intro v
    obtain ⟨rs,he,hlen,hm,hbs,hps,hst⟩ := complete v
    rw [tape_eq B supply _ hq v hw] at he hbs
    obtain ⟨hrow,hrp,hv,hframe⟩ := TermRecord.recordMemory_fields mem (L.base i) row u supply v.val (L.termFits i)
    refine ⟨rs,he,⟨?_,fun x hx => hm ▸ hframe x hx,hlen,hbs,hps,hst⟩⟩
    unfold Fields
    rw [hm,hrow,hrp]
    refine ⟨hr,hu,fun j => ?_⟩
    rw [hv, Fin.val_natCast]
    exact Nat.mod_eq_of_lt ((MotifAdmission.payload_le_cap q hq _ _ _ _
      ((mem_outerIndices_iff B hq _ _).mp v.property) _).trans_lt hw)

omit [Fintype D] in
theorem inputs_after {demand : Fin m → D → ℕ} {mem next : Memory w} (h : Inputs order L demand mem)
    (i : Fin m) (hf : ∀ x, L.Outside i x → next x = mem x) : Inputs order L demand next := by
  intro j
  rw [← h j]
  funext e
  obtain ⟨a,rfl⟩ := order.surjective e
  rw [DemandPreparation.demandAt_address _ _ _ (L.sourceFits j), DemandPreparation.demandAt_address _ _ _ (L.sourceFits j),hf]
  rcases L.separate i j with hl | hr
  · left; have := a.isLt; omega
  · right; omega

private theorem otherFields {demand : D → ℕ} {hp : ∀ i, 0 < p i} {v : S → ℕ} {i : Fin m}
    {mem next : Memory w} (h : Fields B supply hp demand v (L.base i) mem)
    (hf : ∀ x, ¬ L.Outside i x → next x = mem x) : Fields B supply hp demand v (L.base i) next := by
  obtain ⟨hg,hr,hv⟩ := h
  have inside (j : ℕ) (hj : j < 2+n) : ¬ L.Outside i ((L.base i).val+j) := by unfold Layout.Outside; omega
  constructor
  · rwa [hf _ (by simpa using inside 0 (by omega))]
  · constructor
    · rwa [hf _ (inside 1 (by omega))]
    · intro j
      rw [hf _ (by simpa [Nat.add_assoc] using inside (2+j.val) (by have := j.isLt; omega))]
      exact hv j


/-- Supply-index assignments for all motifs in the pass, with independently
admitted sets defined by each actual demand row. -/
noncomputable abbrev Choices (demand : Fin m → D → ℕ) := ∀ i, ↥(outerIndices B (demand i))

private structure Result (hp : ∀ i, 0 < p i) (demand : Fin m → D → ℕ) (v : Choices B demand)
    (ids : List (Fin m)) (M : ℕ) (initial : Memory w) (rs : List (Report w)) : Prop where
  fields : ∀ i ∈ ids, Fields B supply hp (demand i) (v i).val (L.base i) (after initial (eventLog rs))
  frame : ∀ x, (∀ i ∈ ids, L.Outside i x) → after initial (eventLog rs) x = initial x
  length : rs.length = ids.length*5
  bits : branchPaths rs = ids.flatMap (fun i => [[],[],[],[],tape B supply (demand i) w (v i).val])
  probes : countProbes (eventLog rs) ≤ ids.length * probesPerRow B d n
  steps : (eventLog rs).length ≤ ids.length * eventsPerRow B d n w M

private theorem walk_selected {hp : ∀ i, 0 < p i} {demand : Fin m → D → ℕ} {M : ℕ}
    (hready : Ready B order supply L hp demand M) (v : Choices B demand) (ids : List (Fin m))
    (hnd : ids.Nodup) (mem : Memory w) (hin : Inputs order L demand mem) :
    ∃ rs, walk B order supply L (prepFuel (p := p) d M) (fun i => tape B supply (demand i) w (v i).val)
      ids mem = some rs ∧ Result B supply L hp demand v ids M mem rs := by
  induction ids generalizing mem with
  | nil => exact ⟨[],rfl,⟨by simp,fun _ _ => rfl,rfl,rfl,by simp [eventLog,countProbes],by simp [eventLog]⟩⟩
  | cons i ids ih =>
    obtain ⟨hi,hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨head,hhead,hh⟩ := (hready mem hin i).2 (v i)
    let mid := after mem (eventLog head)
    obtain ⟨tail,htail,ht⟩ := ih hnd' mid (inputs_after order L hin i hh.frame)
    let final := after mid (eventLog tail)
    have he : after mem (eventLog (head ++ tail)) = final := by simp [eventLog,after,final,mid]
    dsimp only [mid] at htail
    refine ⟨head++tail,by simp [walk,hhead,htail],⟨?_,?_,?_,?_,?_,?_⟩⟩
    · intro j hj
      rw [he]
      rcases List.mem_cons.mp hj with hij | h
      · subst j
        apply otherFields B supply L hh.fields
        intro x hx
        apply ht.frame x
        intro j hj
        have hne : i ≠ j := fun h => hi (h ▸ hj)
        have hsep := L.different i j hne
        unfold Layout.Outside at *
        omega
      · exact ht.fields j h
    · intro x hx
      rw [he]
      exact (ht.frame x (fun j hj => hx j (List.mem_cons_of_mem _ hj))).trans (hh.frame x (hx i (by simp)))
    · simp only [List.length_append,List.length_cons,hh.length,ht.length,Nat.succ_mul]; omega
    · rw [show branchPaths (head ++ tail) = branchPaths head ++ branchPaths tail from List.map_append,hh.bits,ht.bits,List.flatMap_cons]
    · rw [show eventLog (head++tail) = eventLog head ++ eventLog tail from List.flatMap_append,DemandPreparation.probes_append]
      simpa only [List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add hh.probes ht.probes
    · rw [show eventLog (head++tail) = eventLog head ++ eventLog tail from List.flatMap_append,List.length_append]
      simpa only [List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add hh.steps ht.steps

private theorem walk_sound {hp : ∀ i, 0 < p i} {demand : Fin m → D → ℕ} {M : ℕ}
    (hready : Ready B order supply L hp demand M) (tapes : Fin m → List Bool) (ids : List (Fin m))
    (mem : Memory w) (hin : Inputs order L demand mem) (rs : List (Report w))
    (hr : walk B order supply L (prepFuel (p := p) d M) tapes ids mem = some rs) :
    ∀ i ∈ ids, ∃ v : ↥(outerIndices B (demand i)), tapes i = tape B supply (demand i) w v.val := by
  induction ids generalizing mem rs with
  | nil => simp
  | cons i ids ih =>
    cases hh : TermRecord.run B order supply (L.source i) (L.base i) mem (prepFuel (p := p) d M) (tapes i) with
    | none => simp [walk,hh] at hr
    | some head =>
      let mid := after mem (eventLog head)
      cases ht : walk B order supply L (prepFuel (p := p) d M) tapes ids mid with
      | none => simp [walk,hh,mid,ht] at hr
      | some tail =>
        obtain ⟨v,hv⟩ := ((hready mem hin i).1 (tapes i)).mp (by rw [hh]; rfl)
        obtain ⟨head',hh',hfield⟩ := (hready mem hin i).2 v
        rw [← hv,hh] at hh'
        cases Option.some.inj hh'
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨v,hv⟩
        · exact ih mid (inputs_after order L hin i hfield.frame) tail ht j hj

private theorem tape_inj {hp : ∀ i, 0 < p i} {demand : Fin m → D → ℕ} {M : ℕ}
    (hready : Ready B order supply L hp demand M) (mem : Memory w) (hin : Inputs order L demand mem)
    (i : Fin m) {v v' : ↥(outerIndices B (demand i))}
    (h : tape B supply (demand i) w v.val = tape B supply (demand i) w v'.val) : v = v' := by
  obtain ⟨rs,hr,hv⟩ := (hready mem hin i).2 v
  obtain ⟨rs',hr',hv'⟩ := (hready mem hin i).2 v'
  rw [h,hr'] at hr
  cases Option.some.inj hr
  apply Subtype.ext
  funext e
  obtain ⟨j,rfl⟩ := supply.surjective e
  exact ((hv.fields.2.2 j).symm.trans (hv'.fields.2.2 j))

/-- The full pass has exactly the admissible term choices as successful
streams. Every output row survives to the end of the pass, and outside all
term rows the external memory is preserved. -/
theorem run_spec (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ m M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (L : Layout m d n w) (demand : Fin m → D → ℕ),
      (∀ i e, demand i e ≤ M) → ∀ (mem : Memory w), Inputs order L demand mem →
      let fuel := prepFuel (p := p) d M
      let run := fun tapes => walk B order supply L fuel tapes (List.finRange m) mem
      (∀ tapes, (run tapes).isSome ↔ ∃! v : Choices B demand,
        tapes = fun i => tape B supply (demand i) w (v i).val) ∧
      ∀ v : Choices B demand, ∃ rs, run (fun i => tape B supply (demand i) w (v i).val) = some rs ∧
        (∀ i, Fields B supply hp (demand i) (v i).val (L.base i) (after mem (eventLog rs))) ∧
        (∀ x, (∀ i, L.Outside i x) → after mem (eventLog rs) x = mem x) ∧
        rs.length = m*5 ∧ branchPaths rs = (List.finRange m).flatMap
          (fun i => [[],[],[],[],tape B supply (demand i) w (v i).val]) ∧
        countProbes (eventLog rs) ≤ m*probesPerRow B d n ∧ (eventLog rs).length ≤ m*eventsPerRow B d n w M := by
  obtain ⟨K,hK⟩ := ready B order supply hp hq
  refine ⟨K,fun m M w hW L demand hD mem hin => ?_⟩
  have hR := hK m M w hW L demand hD
  have full v := walk_selected B order supply L hR v (List.finRange m) (List.nodup_finRange _) mem hin
  dsimp only
  constructor
  · intro tapes
    constructor
    · intro h
      obtain ⟨rs,hr⟩ := Option.isSome_iff_exists.mp h
      have witness (i : Fin m) := walk_sound B order supply L hR tapes (List.finRange m) mem hin rs hr i (by simp)
      choose v hv using witness
      refine ⟨v,funext hv,fun z hz => ?_⟩
      funext i
      exact tape_inj B order supply L hR mem hin i ((congrFun hz i).symm.trans (hv i))
    · rintro ⟨v,rfl,_⟩
      obtain ⟨rs,hr,_⟩ := full v
      exact Option.isSome_iff_exists.mpr ⟨rs,hr⟩
  · intro v
    obtain ⟨rs,hr,hs⟩ := full v
    exact ⟨rs,hr,fun i => hs.fields i (by simp),fun x h => hs.frame x (fun i _ => h i),
      by simpa using hs.length,hs.bits,by simpa using hs.probes,by simpa using hs.steps⟩

private theorem one_site_bound (i : Fin m) (M : ℕ) (mem : Memory w) (bits : List Bool)
    {rs : List (Report w)} (h : TermRecord.run B order supply (L.source i) (L.base i) mem
      (prepFuel (p := p) d M) bits = some rs) : ∀ r ∈ rs, r.events.length ≤ eventsPerRow B d n w M := by
  simp only [TermRecord.run,TermRecord.headers,bind,Option.bind_eq_some_iff] at h
  obtain ⟨hs,⟨g,hg,row,_,sr,hsr,src',_,rep,hrep,u,_,su,hsu,hlist⟩,cursor,_,pay,hpay,hlast⟩ := h
  change some [g,sr,rep,su] = some hs at hlist
  cases Option.some.inj hlist
  change some ([g,sr,rep,su] ++ [pay]) = some rs at hlast
  cases Option.some.inj hlast
  rw [(TermRecord.save_native ..).1] at hsr hsu
  cases Option.some.inj hsr
  cases Option.some.inj hsu
  have gsteps := (execute_spec hg).1.length_lt
  have rsteps := (execute_spec hrep).1.length_lt
  have psteps := (execute_spec hpay).1.length_lt
  simp only [List.cons_append,List.nil_append,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff]
  unfold eventsPerRow
  change _ ∧ 4 ≤ _ ∧ _ ∧ 4 ≤ _ ∧ _
  repeat' constructor <;> try omega
  simp

/-- Each individual report obeys the same local instruction cap, even in
a pass with an arbitrarily large number of motifs. -/
theorem walk_site_bound (M : ℕ) (tapes : Fin m → List Bool) (ids : List (Fin m)) (mem : Memory w)
    {rs : List (Report w)} (h : walk B order supply L (prepFuel (p := p) d M) tapes ids mem = some rs) :
    ∀ r ∈ rs, r.events.length ≤ eventsPerRow B d n w M := by
  induction ids generalizing mem rs with
  | nil => change some [] = some rs at h; cases Option.some.inj h; simp
  | cons i ids ih =>
    simp only [walk,bind,Option.bind_eq_some_iff] at h
    obtain ⟨head,hh,tail,ht,hall⟩ := h
    change some (head ++ tail) = some rs at hall
    cases Option.some.inj hall
    simpa only [List.forall_mem_append] using And.intro (one_site_bound B order supply L i M mem (tapes i) hh) (ih _ ht)

end CompressorRecords.TermRecordScan

end VPVNP
end Computability
end OAI
