import OAI.Hierarchy.ProbeStageHeapAgreement
import OAI.Hierarchy.ProbeStageNativeCorrect
import OAI.Hierarchy.ProbeStagePhysicalOrdinal
import OAI.Hierarchy.ProtocolRAMBelow

namespace OAI
/-! # The subdivision heap is independent of every high private selector -/

noncomputable section
namespace Hierarchy.ProbeStage.Native
open ProtocolRAM ProtocolRAM.Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

private theorem scheduled_low {cut w : ℕ} (ps : List Pass) {left right : Memory w} (old : Below cut left right)
    (fits : ∀p∈ps,p.Fits w) : Below cut (result ps left) (result ps right) := by
  induction ps generalizing left right with
  | nil=>exact old
  | cons p ps ih=>
    apply ih _ (fun q h=>fits q (List.mem_cons_of_mem _ h))
    by_cases lo:p.out≤cut
    · exact old.pass p (fits p (List.mem_cons_self ..)) lo
    · intro a ha
      have away : ¬p.out≤a:=by omega
      simpa only [Pass.apply,image,fillSegment,away,false_and,ite_false] using old a ha

private theorem initial_agree {h d : ℕ} {left right : Memory (wordBits h d copies)}
    (same : Below (heapEnd h d copies) left right) :
    Below (heapEnd h d copies) (result (rootPasses h) left) (result (rootPasses h) right) := by
  apply Below.fill (Below.fill same _ _ _ _ (by intros;rfl)) _ _ _ _ (by intros;rfl)

private theorem prepare_source {h d : ℕ} (j : Fin (rounds d)) (m : Memory (wordBits h d copies))
    (arrays : allArrays h d _ j m) : allArrays h d _ j (result (prepareRows h d j.val) m) := by
  intro k i hi
  have space:=allocator_end h d copies j.val
  have later : bankBase h d copies j.val 14≤region h d j.val k+i := by unfold region bankBase;omega
  refine Eq.trans ?_ (arrays k i hi)
  apply columns_frame
  have off : region h d j.val k+i<allocatorBase h d copies j.val ∨
      allocatorBase h d copies j.val+3*2^h≤region h d j.val k+i:=Or.inr (space.trans later)
  simpa using off

private theorem allocator_agree {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (left right : Memory (wordBits h d copies))
    (arrL : allArrays h d _ j left) (arrR : allArrays h d _ j right)
    (idsL : EndpointWords π j left) (idsR : EndpointWords π j right)
    (same : Below (heapEnd h d copies) left right) :
    ∀i≤2^h,Below (heapEnd h d copies) (records h d j.val left i) (records h d j.val right i) := by
  intro i
  induction i with
  | zero=>intros;exact same
  | succ i ih=>
    intro small
    have hi:i<2^h:=by omega
    let r : Fin (2^h):=⟨i,hi⟩
    let body:=physical_ordinal hd π j
    have vl:=visit_records hd π j left (initial_prefix hd π j left arrL) arrL.immutable idsL body i hi.le
    have vr:=visit_records hd π j right (initial_prefix hd π j right arrR) arrR.immutable idsR body i hi.le
    exact ordinal_agree hd π j r _ _ (vl.rom arrL.immutable) (vr.rom arrR.immutable)
      (vl.ids idsL r) (vr.ids idsR r) vl.counts vr.counts (ih hi.le)

/-- This includes all dead and live scratch, on both actual input tapes.
The same original permutation suffices to identify the genuine per-row
side updates at every earlier ordinal. -/
theorem images_low {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h)))
    (left right : Memory (wordBits h d copies))
    (authL : ∀r : Fin (2^h),left r.val=((π r).val:Word _))
    (authR : ∀r : Fin (2^h),right r.val=((π r).val:Word _))
    (same : Below (heapEnd h d copies) (inputTape h d _ left) (inputTape h d _ right)) :
    ∀n≤rounds d,Below (heapEnd h d copies) (images h d (inputTape h d _ left) n)
      (images h d (inputTape h d _ right) n) := by
  intro n
  induction n with
  | zero=>intros;exact initial_agree same
  | succ n ih=>
    intro small
    have hn:n<rounds d:=by omega
    let j : Fin (rounds d):=⟨n,hn⟩
    let m:=images h d (inputTape h d _ left) n
    let v:=images h d (inputTape h d _ right) n
    have a:=after_levels hd π left authL (physical_ordinal hd π) n hn.le
    have b:=after_levels hd π right authR (physical_ordinal hd π) n hn.le
    obtain ⟨ga,aa⟩:=a.future j le_rfl
    obtain ⟨gb,ab⟩:=b.future j le_rfl
    have prepared:=scheduled_low (prepareRows h d n) (ih hn.le) (prepare_fits hn)
    have done:=allocator_agree hd π j _ _ (prepare_source j m aa) (prepare_source j v ab)
      (prepare_endpoint_words hd π j m ga a.parent) (prepare_endpoint_words hd π j v gb b.parent)
      prepared (2^h) le_rfl
    exact scheduled_low (writeRows h d n) done (write_fits hn)

end Hierarchy.ProbeStage.Native
end

end OAI
