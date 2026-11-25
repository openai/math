import OAI.Computability.MultitapeWeakETH.HistoryKernels
import OAI.Computability.MultitapeWeakETH.HistoryVisitChildren
import OAI.Computability.MultitapeWeakETH.WitnessPushNames

/-! # The complete local visitor on a retained chronological row -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression CompressorRecords NetworkKernel PairSimulation LocalHistory
open NodeArguments TraversalRows TreeDecode WitnessWalk
open scoped Classical Fin.CommRing
noncomputable section

private theorem joinChoices {A : Type} {X : A → Type}
    (ids : List Tally) (bank : A → NamedPackets.Bank) (stage : Tally) (code : ∀ a, X a → Bits.Word)
    (tags : ∀ a, X a → List Tally) (js : A → List Job) (word : ∀ a, X a → Bits.Word)
    (read : Bits.Word → Option ChildResult) (kernel : NamedPackets.Bank → Bits.Word → Option (List Tally × Bits.Word))
    (go : Bits.Word → Option Answer)
    (call : ∀ bits jobs tail labels, go bits = some ((jobs,tail),labels) ↔ ∃ nums mem rest,
      read bits = some ((nums,mem),rest) ∧ kernel mem rest = some (labels,tail) ∧ jobs = childJobs (stage,nums,mem.2))
    (parse : ∀ bits nums mem rest, read bits = some ((nums,mem),rest) ↔ ∃ a,
      nums = ids ∧ mem = bank a ∧ bits = mem.2.flatten ++ rest)
    (check : ∀ a bits labels tail, kernel (bank a) bits = some (labels,tail) ↔ ∃ x,
      bits = code a x ++ tail ∧ labels = tags a x)
    (jobsEq : ∀ a, childJobs (stage,ids,(bank a).2) = js a)
    (bitsEq : ∀ a x, word a x = (bank a).2.flatten ++ code a x) :
    ∀ bits jobs tail labels, go bits = some ((jobs,tail),labels) ↔ ∃ a x,
      jobs = js a ∧ bits = word a x ++ tail ∧ labels = tags a x := by
  intro bits jobs tail labels
  rw [call]
  constructor
  · rintro ⟨nums,mem,rest,found,hit,rfl⟩
    obtain ⟨a,rfl,rfl,rfl⟩ := (parse _ _ _ _).mp found
    obtain ⟨x,rfl,rfl⟩ := (check _ _ _ _).mp hit
    exact ⟨a,x,jobsEq a,by rw [bitsEq,List.append_assoc],rfl⟩
  · rintro ⟨a,x,rfl,rfl,rfl⟩
    rw [bitsEq,List.append_assoc]
    exact ⟨_,_,_,(parse _ _ _ _).mpr ⟨a,rfl,rfl,rfl⟩,(check _ _ _ _).mpr ⟨x,rfl,rfl⟩,(jobsEq a).symm⟩

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist : ℕ} (order : B.Entry ≃ Fin hist) {f : B.Entry → R} {hf : B.IsSolution f}

variable (H : ResidentHistory B f hf) (K : ℕ)
    (children : HistorySite × Bits.Word → Option ChildResult) (sh : Fin S.steps → Kernel)
    (refresh : RefreshQuery → Option (List Tally)) (q : LeafSyntax.Query)

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

set_option maxHeartbeats 1600000 in
theorem resident_node (hq : q.1 = H.volume) (hc : H.Children children) (j : Fin H.passes.length)
    (hk : LevelKernelSpec order f hf H.passes[j.val] (gridWidth B H.volume) (H.point j.val)
      (fun x => dispatch sh (refreshKernel refresh) (tally j.val,x))) :
    let V := H.passes[j.val]
    NodeSpec order (visitor K children sh refresh) (q,writes H.log) (originReader B f hf V.origin V.term)
      (inputJob V.input j.val) (outputJob V j.val) := by
  intro V u
  obtain ⟨id,rfl⟩ := (outputOrder V).entries.surjective u
  intro b
  let r := originReader B f hf V.origin V.term
  let site := outputSite V id
  let w := gridWidth B H.volume
  let bank a := NamedPackets.placedBank V.input _ site (childOrder V id) a w
  let packet := pullBits (V.pass.output_eq V.term) (packed (V.pass.next V.term)) site b
  let point := H.point j.val id.val
  have num : ((outputOrder V).entries.symm site).val = id.val :=
    congrArg Fin.val ((outputOrder V).entries.symm_apply_apply id)
  let kernel (mem : NamedPackets.Bank) (bits : Bits.Word) := dispatch sh (refreshKernel refresh)
    (tally j.val,((point,mem,packet),bits))
  have exactKernel a : KernelSpec order (r.read site a b).encode (r.witness site a b).exponents (kernel (bank a)) := by
    have ok := hk site a b
    dsimp only at ok
    change KernelSpec _ _ _ (fun bits => dispatch _ _ (tally j.val,((H.point j.val _,bank a,packet),bits))) at ok
    rw [num] at ok
    exact ok
  choose names counts checks using exactKernel
  refine ⟨names,counts,?_⟩
  apply joinChoices _ bank (tally j.val) (fun a => (r.read site a b).encode)
    (fun a x => (names a x).map (tally ∘ Fin.val)) _ _ (fun bs => children (point,bs)) kernel
  · intro bits jobs tail labels
    change visitor _ _ _ _ (((q,writes H.log),((tally (j.val+1),tally _),packet)),bits) = _ ↔ _
    rw [Equiv.symm_apply_apply]
    have h := visitor_succ K children sh refresh q (writes H.log) j.val id.val packet bits tail jobs labels
    simpa only [point,ResidentHistory.point,hq,kernel] using h
  · exact hc j id
  · exact checks
  · exact visit_child_jobs V id w j.val
  · exact fun a x => visit_node_bits V id w a b x

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
