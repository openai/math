import OAI.Hierarchy.ProbeStageChoiceAgreement
import OAI.Hierarchy.ProbeStageEndpointAgreement

namespace OAI
/-! # Original-input causality of one native CT allocator row -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

/-- A row reads its real advised endpoints and preceding color prefix.
Changing private memory outside the allocation has no effect on any scratch
cell, counter, rank, or unused word of the original allocation. -/
theorem ordinal_agree {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (i : Fin (2^h)) (m n : Memory (ramWidth h d))
    (romM : immutable h d _ j m) (romN : immutable h d _ j n)
    (argsM : ∀q,m (argumentAddr j i q)=(Endpoints.words (history h d π j.val).tiles (radix_pos h d)
      (history h d π j.val).encode i q:Word (ramWidth h d)))
    (argsN : ∀q,n (argumentAddr j i q)=(Endpoints.words (history h d π j.val).tiles (radix_pos h d)
      (history h d π j.val).encode i q:Word (ramWidth h d)))
    (preM : PrefixState hd π j i.val m) (preN : PrefixState hd π j i.val n)
    (agree : ∀x,x<heapEnd h d copies→m x=n x) :
    ∀x,x<heapEnd h d copies →
      Record.image (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m x=
        Record.image (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) n x := by
  have start := atCommits_agree hd π j i m n romM romN argsM argsN preM preN agree
  have lm := start_side hd j i π m romM argsM preM true
  have ln := start_side hd j i π n romN argsN preN true
  have previous := endpoint_agree hd j i _ _ _ _ _ _ lm ln start
  have rm := after_left hd j i (endpoint_commit hd j i _ _ _ _ _ lm)
    (start_side hd j i π m romM argsM preM false)
  have rn := after_left hd j i (endpoint_commit hd j i _ _ _ _ _ ln)
    (start_side hd j i π n romN argsN preN false)
  exact endpoint_agree hd j i _ _ _ _ _ _ rm rn previous

end
end Hierarchy.ProbeStage.Native

end OAI
