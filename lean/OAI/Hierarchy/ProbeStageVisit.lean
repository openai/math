import OAI.Hierarchy.ProbeStageVisitFrame
import OAI.Hierarchy.ProbeStageProgramCost

namespace OAI
/-! # Chronological conservation of the concrete ordinal allocator state -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

abbrev RowCorrect {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) :=
  ∀ (i : Fin (2^h)) (m : Memory (wordBits h d copies)), immutable h d _ j m →
    (∀ k : Fin 3,m ((blockBank h d copies j.val k).base+i.val)=
      (Endpoints.words (history h d π j.val).tiles (radix_pos h d) (history h d π j.val).encode i k : Word _)) →
    PrefixState hd π j i.val m → RowOutput hd π j i m

def rankValue {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (i : Fin (2^h)) : Fin 3 → ℕ :=
  ![((assigned j π).color i).val,((assigned j π).enterRank i).val,((assigned j π).exitRank i).val]

structure Visit {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (input : Memory (wordBits h d copies)) (k : ℕ) : Prop where
  counts : PrefixState hd π j k (records h d j.val input k)
  columns : ∀ (r : Fin (2^h)),r.val<k → ∀ v,records h d j.val input k (rankAddr h d j.val v r)=
    (rankValue π j r v : Word _)
  scans : ∀ (r : Fin (2^h)),r.val<k →
    rowScans h d j.val r.val (records h d j.val input r.val)≤expectedScans h d π j.val r
  clears : ∀ (r : Fin (2^h)),r.val<k →
    rowClears h d j.val r.val (records h d j.val input r.val)≤expectedClears h d π j.val r
  frame : ∀ a, (∀ (i : Fin (2^h)),i.val<k → ¬MayWrite h d j.val i a) →
    records h d j.val input k a=input a

theorem Visit.rom {h d k : ℕ} {hd : 1≤d} {π : Equiv.Perm (Fin (2^h))} {j : Fin (rounds d)}
    {input : Memory (wordBits h d copies)} (v : Visit hd π j input k)
    (saved : immutable h d _ j input) : immutable h d _ j (records h d j.val input k) := by
  intro q a ha
  have stable := v.frame (region h d j.val ⟨q.val,by omega⟩+a) (fun r _ => mayWrite_not_rom r q ⟨a,ha⟩)
  exact stable.trans (saved q a ha)

theorem Visit.ids {h d k : ℕ} {hd : 1≤d} {π : Equiv.Perm (Fin (2^h))} {j : Fin (rounds d)}
    {input : Memory (wordBits h d copies)} (v : Visit hd π j input k)
    (saved : EndpointWords π j input) : EndpointWords π j (records h d j.val input k) := by
  intro r q
  exact (v.frame _ (fun i _ => mayWrite_not_argument i r q)).trans (saved r q)

/-- Every earlier published rank stays in its own cell. The retained tape
and expected scan/clear charges use the actual memory from each ordinal. -/
theorem visit_records {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (input : Memory (wordBits h d copies)) (init : PrefixState hd π j 0 input)
    (rom : immutable h d _ j input) (ids : EndpointWords π j input) (body : RowCorrect hd π j) :
    ∀ k≤2^h, Visit hd π j input k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨init,?_,?_,?_,fun _ _ => rfl⟩
    all_goals intros;omega
  | succ k ih =>
    intro hk
    let i : Fin (2^h) := ⟨k,by omega⟩
    have previous := ih (by omega)
    have row := body i (records h d j.val input k) (previous.rom rom) (previous.ids ids i) previous.counts
    refine ⟨row.next,?_,?_,?_,?_⟩
    · intro r hr c
      by_cases same : r=i
      · subst r
        exact row.columns c
      · have lt : r.val<k := by
          have ne : r.val≠k := fun e => same (Fin.ext e)
          omega
        exact (row.frame _ (mayWrite_not_earlier_rank same c)).trans (previous.columns r lt c)
    · intro r hr
      by_cases same : r=i
      · subst r;exact row.scans
      · have hne : r.val≠k := fun e => same (Fin.ext e)
        exact previous.scans r (by omega)
    · intro r hr
      by_cases same : r=i
      · subst r;exact row.clears
      · have hne : r.val≠k := fun e => same (Fin.ext e)
        exact previous.clears r (by omega)
    · intro a freeze
      exact (row.frame a (freeze i (Nat.lt_succ_self k))).trans
        (previous.frame a (fun r hr => freeze r (Nat.lt_succ_of_lt hr)))

theorem Visit.ranks {h d : ℕ} {hd : 1≤d} {π : Equiv.Perm (Fin (2^h))} {j : Fin (rounds d)}
    {input : Memory (wordBits h d copies)} (v : Visit hd π j input (2^h)) :
    RankStored π j (records h d j.val input (2^h)) := by
  have size := (height_extent h d).trans (extent_word h d copies).le
  have bank (c : Fin 3) : Resident (rankAt h d copies j.val c) (records h d j.val input (2^h))
      (fun r => rankValue π j r c) :=
    Resident.of_cells _ _ _ le_rfl size (fun r => v.columns r r.isLt c)
  exact ⟨bank 0,bank 1,bank 2⟩

end
end Hierarchy.ProbeStage.Native

end OAI
