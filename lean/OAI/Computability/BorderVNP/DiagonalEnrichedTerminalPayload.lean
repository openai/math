import OAI.Computability.BorderVNP.DiagonalEnrichedReplayPayload
import OAI.Computability.BorderVNP.DiagonalEnrichedTerminal
import OAI.Computability.BorderVNP.PackedEnrichedHistoryRecords

/-! # Scalar counts on the record payload of the full enriched physical history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedOuterReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity
open scoped Classical BigOperators BorderVNP.Epoch.Cube
open private move from OAI.Computability.BorderVNP.DiagonalFactoryReplay
attribute [local instance] portFintype

universe u

variable {D m exp start T : ℕ} [NeZero D] {K E Team Param Gadget Hidden P : Type}
  [Field K] [Field E] [Fintype Team] [Fintype Param] [Fintype P] {bits : P → ℕ}
  {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e}
  {shape : ℕ → Shape} {W : ℕ → Type} [∀ j, Fintype (W j)] {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)]
  {w : ℕ → ℕ → ℕ} {good : ∀ j, EnrichedOuter.State S start P bits shape W j → Prop}
  {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{0,u} deep good V w)

/-- Enumerate nested team labels in the actual outer recursion. -/
noncomputable local instance {n : ℕ} : Fintype (Port (fan S) Team n) := Replay.batchFinite (fan S) Team n

omit [∀ j, Fintype (W j)] in
private theorem transported_bound {n : ℕ} {c : Fin (fan S) → Admissible good n}
    {r : ∀ i, RecordData (c i).val.pack.layout} {p q : ProfileSum (Admissible good (n+1))}
    (eq : p = q) (tag : ∀ j : p.Index, Tracked (Port (fan S) Team (n+1)) Param Gadget exp (p.term j).val.pack.layout)
    (recs : ReturnedFields c r p) (h : ∀ j, PayloadBound (tag j).tags (recs.field j).payload) :
    ∀ j : q.Index, PayloadBound
      ((move (V := fun a => Tracked (Port (fan S) Team (n+1)) Param Gadget exp a.val.pack.layout) eq tag j).tags)
      (((congrArg (ReturnedFields c r) eq.symm).mpr recs).field j).payload := by
  subst q
  exact h

variable (y : e.Entry → E)
  (hy : ∀ p : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry p = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom E) y p = 0)
  (pos : e.Entry → Gadget)

/-- One active enriched outer node preserves the scalar count against the actual
payload recorded by this same node's returned-field operation. -/
theorem node_payloadBound (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (tag : ∀ i, Tracked (Port (fan S) Team n) Param Gadget exp (c i).val.pack.layout)
    (r : ∀ i, RecordData (c i).val.pack.layout) (old : ∀ i, PayloadBound (tag i).tags (r i).payload)
    (q : (M.epoch n c).Index) :
    PayloadBound (advance M y hy pos n c tag q).tags ((M.nodeRecords n c r).field q).payload := by
  let : Fintype (Port (fan S) P n) := portFintype
  let epoch := M n hn
  have h (i : (epoch.choice c).Index) :
      PayloadBound (emit epoch y hy pos c tag i).tags ((epoch.returnedFields c r).field i).payload :=
    EnrichedSiteReplay.term_payloadBound epoch.saveNames y hy pos (epoch.run c) tag r old i
  have eq : M.epoch n c = epoch.choice c := dite_eq_left hn
  unfold advance EnrichedOuter.Machine.nodeRecords
  rw [dite_eq_left hn,dite_eq_left hn]
  exact transported_bound eq.symm (emit epoch y hy pos c tag) (epoch.returnedFields c r) h q

variable [Fintype Hidden] (bottom : Admissible good 0)
  (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)
  (fields : RecordData bottom.val.pack.layout)

omit [Fintype Hidden] in
/-- All recursively computed specialized scalar occurrences are covered by the
corresponding original or paid box at the same terminal histogram, even when
several different private bottom assignments share a public transcript. -/
theorem history_payloadBound (leaf : ∀ z, PayloadBound (base z).tags fields.payload)
    (n : ℕ) (hn : n ≤ T) (z : Fin ((fan S)^n) → Hidden) (q : (packHistory bottom M.epoch n).Index) :
    PayloadBound (Outer.term (fun _ (a : Admissible good _) => a.val.pack.layout) bottom M.epoch base
      (advance M y hy pos) n z q).tags (M.historyFields bottom fields n q).payload := by
  induction n with
  | zero => exact leaf (z 0)
  | succ n ih =>
    let c (i : Fin (fan S)) := (packHistory bottom M.epoch n).term (q.1 i)
    let tags (i : Fin (fan S)) := Outer.term (fun _ (a : Admissible good _) => a.val.pack.layout) bottom M.epoch
      base (advance M y hy pos) n (fun j => z (copyIndex (fan S) n (i,j))) (q.1 i)
    let r (i : Fin (fan S)) := M.historyFields bottom fields n (q.1 i)
    exact node_payloadBound M y hy pos n (Nat.lt_of_succ_le hn) c tags r
      (fun i => ih (by omega) (fun j => z (copyIndex (fan S) n (i,j))) (q.1 i)) q.2

omit [Fintype Hidden] in
/-- The flattened row-major terminal tag table uses the same site charge as the
true complete public history's accumulated `RecordData.payload`. -/
theorem terminal_payloadBound (leaf : ∀ z, PayloadBound (base z).tags fields.payload)
    (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden) :
    PayloadBound (terminal M y hy pos bottom base q z).flat.tags (M.historyFields bottom fields T q).payload := by
  have h := history_payloadBound M y hy pos bottom base fields leaf T le_rfl z q
  exact fun v wires _ g => h v wires _ g

end Diagonal.CellEntries.EnrichedOuterReplay

end BorderVNP
end Computability
end OAI
