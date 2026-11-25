import OAI.Hierarchy.ProbeStageCompactFallback

namespace OAI
/-! # Actual compact-row candidate selection agrees with the original execution -/
namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
set_option maxRecDepth 4096
variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => wordBits h d copies
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j
local notation "R" => recordRow h d j i

theorem choice_model (hd : 1≤d) (hh : 4≤h) (π : Equiv.Perm (Fin (2^h))) (m n : Memory W)
    (saved : Fin 8→Word W) (rom : immutable h d W j m)
    (args : ∀ q,m (argumentAddr j i q)=(Endpoints.words (history h d π j.val).tiles (radix_pos h d)
      (history h d π j.val).encode i q:Word W)) (pre : PrefixState hd π j i.val m)
    (rel : Model j i saved m n) (ids : ∀ q : Fin 3,saved ⟨q.val,by omega⟩=m (argumentAddr j i q)) :
    Model j i saved (Record.leftInput A S R m) (Record.leftInput A S (row h) n) ∧
      Record.scans A S (row h) n=Record.scans A S R m := by
  classical
  have ord:=ordinalIDs_of_words j i hd π m args
  have prepared:=prepare_model j i hh hd π m n saved rel args ids
  have fast:=fast_model j i hd hh π m n saved rom ord pre prepared
  have scan:=scan_model j i hd hh π m n saved rom ord pre fast
  have source:=choice_input hd j i π m rom ord pre
  have native:=Record.physical_choice A S R m _ _ _ _ (radix_pos h d) (query_good_nonempty j i π) source
  have cap : Record.scans A S R m ≤ radix h d := by
    rw [native.1]
    split <;> omega
  refine ⟨fallback_model j i hh _ _ saved scan cap ?_,congrArg Fin.val (scan.temp hh 7)⟩
  intro side c
  change Common j i (scanningMemory j i m (scratch h d j (countPtr side):Word W).val + (c.val:Word W)).val
  rw [scanning_count_address j i hd π m rom ord side c]
  let b:=blockNumber hd j π (queryBlock j i π side)
  simpa only [counterLocation,Nat.add_assoc] using
    common_area j i hh (countArea side) ⟨b.val*radix h d+c.val,count_offset hd j.isLt.le b c⟩

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
