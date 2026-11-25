import OAI.ThreeFlat.Diagonal.PhysicalNodeStoredPath
import OAI.ThreeFlat.Diagonal.PhysicalNodeWordFits

namespace OAI
/-! # Intermediate true charge and pair values in the chronological publisher's memory -/

noncomputable section
namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalStage
open scoped Fin.CommRing Classical BigOperators
variable {F : Type} [Field F] {W : ℕ}

/-- Between adjacent layer visits the preceding output range is legible
as a native word, even before its natural representative is proved exact. -/
private def Linked (W : ℕ) (b : Banks) (xs : List NodeRow) (read : ℕ→ℕ→Fin 2→ℕ) : Prop :=
  ∀ (i : Fin (records xs).length), i.val+1<(records xs).length →
    ∀ (j : Fin ((records xs).get i).actual.count) (c : Fin 2),
      read (i.val+1) (((records xs).get i).actual.first+j.val) c =
        (((program xs).data i).cost b (read i.val) j c : Word W).val

private theorem linked_head (b : Banks) (q : NodeRow) (qs : List NodeRow)
    (read : ℕ→ℕ→Fin 2→ℕ) (link : Linked W b (q::qs) read)
    (nonempty : 0<(records qs).length) (j : Fin q.layer.count) (c : Fin 2) :
    read 1 (q.layer.first+j.val) c = (q.data.cost b (read 0) j c : Word W).val :=
  link ⟨0,Nat.zero_lt_succ _⟩ (Nat.succ_lt_succ nonempty) j c

private theorem linked_tail (b : Banks) (q : NodeRow) (qs : List NodeRow)
    (read : ℕ→ℕ→Fin 2→ℕ) (link : Linked W b (q::qs) read) :
    Linked W b qs (fun k => read (k+1)) :=
  fun i next j c => link i.succ (Nat.succ_lt_succ next) j c

private theorem archive_nonempty {d l} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    0<(records (r.archiveList h C O p seed)).length := by
  cases r <;> simp only [Run.archiveList,records,List.map_cons,List.length_cons,Nat.zero_lt_succ]

private theorem current_fits {d l} {A : State d l} (O : A.ArchiveSites) (seed : LayerData O.layer)
    (b : Banks) (read : ℕ→Fin 2→ℕ) (start pay : A.Site→ℕ)
    (values : ∀ v c,seed.cost b read (O.ord v) c=if c.val=0 then b.unitWork*start v else pay v)
    (fit : ∀ v,b.unitWork*start v<2^W ∧ pay v<2^W) (j : Fin O.layer.count) (c : Fin 2) :
    seed.cost b read j c<2^W := by
  have h := values (O.ord.symm j) c
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  split
  · exact (fit _).1
  · exact (fit _).2

/-- Induct in the order of the true tensor run. The old row is already
within range before converting its stored Word back into a natural number. -/
private theorem linked_fits {d l} {A : State d l} (b : Banks) (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (start pay : A.Site→ℕ) (read : ℕ→ℕ→Fin 2→ℕ)
    (fit : r.ArchiveFits W b.unitWork h C start pay)
    (values : ∀ v c,seed.cost b (read 0) (O.ord v) c=if c.val=0 then b.unitWork*start v else pay v)
    (link : Linked W b (r.archiveList h C O p seed) read) :
    let xs := r.archiveList h C O p seed
    ∀ (i : Fin (records xs).length) j c, ((program xs).data i).cost b (read i.val) j c<2^W := by
  induction r generalizing read with
  | done A =>
    intro xs i
    change Fin 1 at i
    have only : i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    exact current_fits O seed b (read 0) start pay values fit
  | step R next ih =>
    let t := h.1
    let rest := Run.tailHistory R next h
    let S := p.1
    let tail := (next t).archiveList rest (C.2 t) S.sites p.2 S.data
    have nonempty : 0<(records tail).length := archive_nonempty (next t) rest (C.2 t) S.sites p.2 S.data
    let first : NodeRow :=
      ⟨O.layer,⟨false,S.sites.layer.first,S.ownerPtr⟩,seed,
        fun j => (S.sites.ord (R.parent t (O.ord.symm j))).val⟩
    change Linked W b (first::tail) read at link
    have prev (x) : read 1 (O.id x) 0=b.unitWork*start x ∧ read 1 (O.id x) 1=pay x := by
      have readWork := linked_head b first tail read link nonempty (O.ord x) 0
      have readPay := linked_head b first tail read link nonempty (O.ord x) 1
      change read 1 (O.id x) 0=(seed.cost b (read 0) (O.ord x) 0 : Word W).val at readWork
      change read 1 (O.id x) 1=(seed.cost b (read 0) (O.ord x) 1 : Word W).val at readPay
      rw [values x 0] at readWork
      rw [values x 1] at readPay
      exact ⟨readWork.trans (Fin.val_cast_of_lt (fit.1 x).1),readPay.trans (Fin.val_cast_of_lt (fit.1 x).2)⟩
    let newStart := R.push t (C.1 t) start
    let newPay := fun v => ∑ x : {i // R.parent t i=v}, pay x.val
    have newValues (v) (c : Fin 2) : S.data.cost b (read 1) (S.sites.ord v) c=
        if c.val=0 then b.unitWork*newStart v else newPay v := by
      have eq := S.cost_values b (read 1) start pay prev v
      fin_cases c
      · exact eq.1
      · exact eq.2
    have tailFit := ih t rest (C.2 t) S.sites p.2 S.data newStart newPay
      (fun k => read (k+1)) fit.2 newValues (linked_tail b _ tail read link)
    dsimp only
    change ∀ (i : Fin ((records tail).length+1)) j c, ((program (first::tail)).data i).cost b (read i.val) j c<2^W
    intro i
    induction i using Fin.cases with
    | zero => exact current_fits O seed b (read 0) start pay values fit.1
    | succ i => exact tailFit i

/-- Every pre-scan pair count and every written work word fit on the actual
selected path, including at the physical time before the final memory state. -/
theorem archive_charge_fits {d l} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (a : NodeArchive) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a (records (r.archiveList h C O p seed)) budget)
    (start pay : A.Site→ℕ) (seeds : State.SeedRows O seed a.banks start pay)
    (fit : r.ArchiveFits W a.banks.unitWork h C start pay) :
    let xs := r.archiveList h C O p seed
    ∀ (i : Fin (records xs).length) j c,
      ((program xs).data i).cost a.banks (prior a (decrement a (state a (program xs) m i.val))) j c<2^W := by
  let xs := r.archiveList h C O p seed
  let read k := prior a (decrement a (state a (program xs) m k))
  have order := archive_chronological r h C O p seed
  apply linked_fits a.banks r h C O p seed start pay read fit (seeds (read 0))
  intro i more j c
  let t : Fin (records xs).length := ⟨i.val+1,more⟩
  exact before_charge a (program xs) m room order i t (by change i.val < i.val+1;omega) j c

end ThreeFlat.Diagonal.NavigationPass.NodePublication
end

end OAI
