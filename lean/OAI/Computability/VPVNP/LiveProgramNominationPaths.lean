import OAI.Computability.VPVNP.LiveProgramNominationCalls

/-! # Bijection between histogram nominations and native stage histories -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Nominations

open BurstRAM BurstRAM.PrivateRAM LiveStageLink PrimedInputRAM
open scoped Fin.CommRing

variable (G : Group)

/-- One fixed-width nominated count at every position of the dense grammar-label array. -/
abbrev Nom := Fin (labels G) → Word (width G)

private theorem aligned (T : ℕ) :
    (List.finRange T).map Fin.val = List.range' 0 (List.finRange T).length := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp

/-- An active nomination call returns a state, uses one probe, and records exactly five times
the nomination width plus fourteen events. -/
def activeReport (r : Report G.w) : Prop :=
  r.result.isSome ∧ r.events.length = 5*width G+14 ∧ r.probes = 1

private theorem emit (hb : width G ≤ G.w) (hT : labels G < 2^G.w) (hf : 5*width G+15 ≤ fuel G)
    (fit : (base G).val + labels G ≤ 2^G.w) (μ : Nom G) (cells : List (Fin (labels G)))
    (j : ℕ) (ha : cells.map Fin.val = List.range' j cells.length) (hj : j+cells.length = labels G) (m : Memory G.w) :
    ∃ rs, rs.length = cells.length ∧ (∀ r ∈ rs, activeReport G r) ∧
      Completion G.T G.nextStage G.pub G.addr Stage.nominations (fuel G) (j : Word G.w) m
        ((cells.map fun i => wordBits (μ i)) ++ [[]]) (rs ++ [closing G.w])
        (store (scratchAddress (base G).val fit) (fun i => Fin.ofNat _ (μ i).val) cells m) := by
  induction cells generalizing j m with
  | nil =>
    simp only [List.length_nil,Nat.add_zero] at hj
    subst j
    have ce := closed G (by omega) (limit G) le_rfl m []
    have call : execute (P G) (fuel G) ((P G).start (labels G : Word G.w)) m [] = some (closing G.w) := by
      simpa using ce
    have enough : room G.nextStage G.addr Stage.nominations (fuel G) (closing G.w) := by
      change 6 < fuel G
      omega
    exact ⟨[],rfl,by simp,.last call rfl enough⟩
  | cons i is ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] at ha
    obtain ⟨rfl,ha⟩ := ha
    have hs : (i.val : Word G.w) < limit G := by
      change ((i.val : Word G.w) : ℕ) < (limit G).val
      rw [Fin.val_natCast,Nat.mod_eq_of_lt (i.isLt.trans hT),limit_val G hT]
      exact i.isLt
    obtain ⟨r,hc,hr,hm,hl,hp⟩ := active G hb hf _ hs m (μ i)
    have enough : room G.nextStage G.addr Stage.nominations (fuel G) r := by
      simp only [room,exitReport,hr]; omega
    have hnext : (i.val : Word G.w)+1 = ((i.val+1 : ℕ) : Word G.w) := by simp
    obtain ⟨rs, len, each, tail⟩ := ih (i.val+1) ha (by simp only [List.length_cons] at hj; omega) (after m r.events)
    rw [← hnext] at tail
    rw [base_add G fit i] at hm
    have ht := Completion.more hc hr enough tail
    rw [hm] at ht
    refine ⟨r::rs, by simp [len], List.forall_mem_cons.mpr ⟨?_,each⟩, ht⟩
    simp [activeReport,hr,hl,Report.probes,hp]

private theorem decode {m : Memory G.w} {bs rs m'} {s : Word G.w}
    (hb : width G ≤ G.w) (hf : 5*width G+15 ≤ fuel G)
    (h : Completion G.T G.nextStage G.pub G.addr Stage.nominations (fuel G) s m bs rs m')
    (hs : s ≤ limit G) :
    ∃ xs : List (Word (width G)), xs.length + s.val = (limit G).val ∧ bs = xs.map wordBits ++ [[]] := by
  induction h with
  | @last s m bits rep call halt _ =>
    rcases lt_or_eq_of_le hs with lt | rfl
    · obtain ⟨_,_,ret,_⟩ := active_only G hb (by omega) s lt m call
      rw [ret] at halt; contradiction
    · rw [closed G (by omega) _ le_rfl] at call
      split at call
      · exact ⟨[],by simp,by simp_all⟩
      · contradiction
  | @more s m bits rep s' bs rs m' call cont _ _ ih =>
    rcases lt_or_eq_of_le hs with lt | rfl
    · obtain ⟨v, hv, hr, _⟩ := active_only G hb (by omega) s lt m call
      have hs' : s' = s+1 := Option.some.inj (cont.symm.trans hr)
      have hh : s'.val = s.val+1 := by
        rw [hs',Fin.val_add_one_of_lt' (show s.val+1 < 2^G.w from (show s.val+1 ≤ (limit G).val from lt).trans_lt (limit G).isLt)]
      obtain ⟨xs,len,out⟩ := ih (by change s'.val ≤ (limit G).val; rw [hh]; exact lt)
      exact ⟨v::xs,by simp [hh] at len; simp; omega,by simp [hv,out]⟩
    · rw [closed G (by omega) _ le_rfl] at call
      split at call
      · simp [← Option.some.inj call,closing] at cont
      · contradiction

/-- The source reports, before the dispatch read and closing tag transfer. -/
theorem history (hb : width G ≤ G.w) (hT : labels G < 2^G.w) (hf : 5*width G+15 ≤ fuel G)
    (fit : (base G).val + labels G ≤ 2^G.w) (μ : Nom G) (m : Memory G.w) :
    ∃ rs, rs.length = labels G ∧ (∀ r ∈ rs, activeReport G r) ∧
      Completion G.T G.nextStage G.pub G.addr Stage.nominations (fuel G) 0 m
        (LiveNominations.calls μ ++ [[]]) (rs ++ [closing G.w]) (LiveNominations.stored (base G) fit μ m) := by
  have h := emit G hb hT hf fit μ (List.finRange (labels G)) 0 (aligned _) (by simp) m
  simpa only [List.length_finRange,Nat.cast_zero,LiveNominations.calls,List.ofFn_eq_map,LiveNominations.stored] using h

private noncomputable def path (hb : width G ≤ G.w) (hT : labels G < 2^G.w) (hf : 5*width G+15 ≤ fuel G)
    (fit : (base G).val + labels G ≤ 2^G.w) (m : Memory G.w) (μ : Nom G) : G.StagePaths Stage.nominations m :=
  ⟨LiveNominations.calls μ ++ [[]], by
    obtain ⟨rs,_,_,h⟩ := history G hb hT hf fit μ m
    exact ⟨_,h.spec.1,h.spec.2.1,h.spec.2.2.2⟩⟩

/-- Bijection from nomination arrays to complete nomination-stage paths, obtained by encoding
and decoding the guessed words in grammar-label order. -/
noncomputable def equiv (hb : width G ≤ G.w) (hT : labels G < 2^G.w) (hf : 5*width G+15 ≤ fuel G)
    (fit : (base G).val + labels G ≤ 2^G.w) (m : Memory G.w) : Nom G ≃ G.StagePaths Stage.nominations m := by
  apply Equiv.ofBijective (path G hb hT hf fit m)
  constructor
  · intro μ ν h
    have ht : LiveNominations.calls μ ++ [[]] = LiveNominations.calls ν ++ [[]] := congrArg Subtype.val h
    have hw := List.ofFn_inj.mp (List.append_cancel_right ht)
    exact funext fun i => (List.ofFn_injective.comp (RAMSerialization.wordBits _).injective) (congrFun hw i)
  · intro p
    obtain ⟨xs,hlen,hb'⟩ := decode G hb hf
      (completion_of_run (ordinaryRun p) p.property.choose_spec.2.1 p.property.choose_spec.2.2)
      (by exact Fin.zero_le _)
    have len : xs.length = labels G := by rw [limit_val G hT] at hlen; simpa using hlen
    let μ : Nom G := fun i => xs[i.val]'(len.symm ▸ i.isLt)
    refine ⟨μ,Subtype.ext ?_⟩
    change LiveNominations.calls μ ++ [[]] = p.val
    rw [hb']
    congr 1
    apply List.ext_getElem (by simp [LiveNominations.calls,len])
    intro i _ _
    simp [LiveNominations.calls,μ]

/-- Word, clock and memory layout conditions of the nomination stage. -/
structure Fits : Prop where
  width_le : width G ≤ G.w
  labels_lt : labels G < 2^G.w
  clock_le : 5*width G+15 ≤ fuel G
  address : (base G).val + labels G ≤ 2^G.w
  tagOutside : G.addr.val < (base G).val ∨ (base G).val+labels G ≤ G.addr.val

/-- Index the actual tagged nomination-stage histories by their nomination arrays, using the
cursor bound and the word, address, and clock fits. -/
noncomputable def indexed (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) :
    Indexed G Stage.nominations m (Nom G) where
  inv s _ := s ≤ limit G
  frame := frame G F.width_le F.labels_lt F.clock_le F.address F.tagOutside
  ready := Fin.zero_le _
  tag := tag
  traces := equiv G F.width_le F.labels_lt F.clock_le F.address m

theorem indexed_apply (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    ((indexed G F m tag).traces μ).val = LiveNominations.calls μ ++ [[]] := rfl

private theorem reports (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    ∃ rs, rs.length = labels G ∧ (∀ r ∈ rs, activeReport G r) ∧
      ordinaryReports ((indexed G F m tag).traces μ) = rs ++ [closing G.w] ∧
      after m (eventLog (rs ++ [closing G.w])) = LiveNominations.stored (base G) F.address μ m := by
  obtain ⟨rs,hl,hp,hc⟩ := history G F.width_le F.labels_lt F.clock_le F.address μ m
  have hr := ordinaryRun ((indexed G F m tag).traces μ)
  rw [indexed_apply] at hr
  exact ⟨rs,hl,hp,Option.some.inj (hr.symm.trans hc.spec.1),hc.spec.2.2.1⟩

theorem memory_eq (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    (indexed G F m tag).memory μ =
      transferMemory G.addr (some Stage.auxiliaryInit) (LiveNominations.stored (base G) F.address μ m) := by
  obtain ⟨_,_,_,hr,hm⟩ := reports G F m tag μ
  rw [Indexed.memory,hr,hm]
  rfl

theorem logs_length (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    ((indexed G F m tag).logs μ).length = labels G + 1 := by
  obtain ⟨rs,hl,_,hr,_⟩ := reports G F m tag μ
  simp [Indexed.logs,hr,hl]

theorem logs_probes (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    ∀ r ∈ (indexed G F m tag).logs μ, r.probes = 2 := by
  obtain ⟨rs,_,each,hr,_⟩ := reports G F m tag μ
  rw [Indexed.logs,hr]
  intro r h
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
  rw [linkedReport_probes]
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨live,_,one⟩ := each a h
    have hn : a.result ≠ none := by cases v : a.result <;> simp_all
    simp [one,hn]
  · obtain rfl := List.mem_singleton.mp h
    rfl

theorem logs_cost (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    RAMBuckets.cost Report.probes ((indexed G F m tag).logs μ) = (labels G + 1)*3 := by
  have all (xs : List (Report G.w)) (h : ∀ a ∈ xs, a.probes = 2) :
      RAMBuckets.cost Report.probes xs = xs.length*3 := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      obtain ⟨ha, ht⟩ := List.forall_mem_cons.mp h
      rw [RAMBuckets.cost,ha,ih ht,List.length_cons,Nat.succ_mul]
      omega
  rw [all _ (logs_probes G F m tag μ),logs_length]

/-- Linked active calls have one dispatcher read and one store. The last call
instead transfers the stage tag. Its shorter local run has a fixed length. -/
theorem logs_lengths (F : Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : Nom G) :
    ((indexed G F m tag).logs μ).map (fun r => r.events.length) =
      List.replicate (labels G) (5*width G+22) ++ [14] := by
  obtain ⟨rs,hl,each,hr,_⟩ := reports G F m tag μ
  have lengths (a : Report G.w) (h : activeReport G a) :
      (linkedReport G.nextStage G.addr Stage.nominations a).events.length = 5*width G+22 := by
    rcases h with ⟨live,len,_⟩
    cases ha : a.result with
    | none => simp [ha] at live
    | some v =>
      simp only [linkedReport,prependLog,exitReport,ha,List.length_append,len]
      change 8+(5*width G+14) = _
      omega
  have hmap : rs.map (fun a => (linkedReport G.nextStage G.addr Stage.nominations a).events.length) =
      List.replicate rs.length (5*width G+22) := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_replicate]
    exact lengths _ (each _ (List.getElem_mem _))
  rw [Indexed.logs,hr,List.map_append,List.map_append,List.map_map]
  change rs.map (fun a => (linkedReport G.nextStage G.addr Stage.nominations a).events.length) ++ [14] = _
  rw [hmap,hl]

end LiveProgram.PairStages.Group.Nominations

end VPVNP
end Computability
end OAI
