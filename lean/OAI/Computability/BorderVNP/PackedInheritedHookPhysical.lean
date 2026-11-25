import OAI.Computability.BorderVNP.PackedInheritedHookFrame

/-! # The live immutable hook frame writes the physical terminal row

The stable query reads the selected seed count, the actual successor cable
base, and the old band's clipped ordinal. The word bound includes the full
bin count: an empty clipped band may encode an unused ordinal past the end
of its gathered word. The record remains a zero-span equality in that case.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedHook

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile BankSite BankJoint BankCircuit BankPacket CellSparse Word
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

private theorem ordinal_le_bin {D m : ℕ} [NeZero D] {P : Type*} {A : Type} {bits : P → ℕ} (N : Network D P bits)
    (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (names : A → ℕ) (a : A)
    (z : {z : N.Edge // bin z = some a}) (b : Band D) :
    (descriptor N bin perm m names z b).ordinal ≤ count N bin a := by
  let T := {z : N.Edge // bin z = some a}
  let w (u : T) := N.width u.val
  have total : count N bin a = ∑ u : T, w u := by
    simp only [SeedIntervals.count,BinBits,Fintype.card_sigma,Fintype.card_fin]
    rfl
  have one : (∑ u : T,if u = z then w z else 0) = w z := by
    simpa only [Finset.mem_univ,ite_true] using Finset.sum_ite_eq' (Finset.univ : Finset T) z (fun _ => w z)
  have he : cableOffset N bin a z.val + N.width z.val ≤ count N bin a := by
    rw [total]
    change (∑ u : T,if cableName N u.val < cableName N z.val then w u else 0) + w z ≤ _
    apply (congrArg (fun x => (∑ u : T,if cableName N u.val < cableName N z.val then w u else 0)+x) one.symm).le.trans
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    by_cases h : u = z
    · subst u
      simp
    · by_cases hl : cableName N u.val < cableName N z.val <;> simp [h,hl]
  let d := descriptor N bin perm m names z b
  have hl : d.localStart ≤ N.width z.val := Nat.min_le_left _ _
  change d.start + d.localStart - d.lo ≤ _
  exact (Nat.sub_le _ _).trans ((Nat.add_le_add_left hl d.start).trans he)

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] {n old sites np C d h w : ℕ} (seed : S ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w)) (occupied : Fin (edgeCapacity e old n) → σ)

/-- The fixed native hook program, including its enable and destination columns. -/
noncomputable def native := (exists_frame e seed F counts cut occupied).choose

omit [NeZero D] in
/-- Number of gates in the fixed hook frame, with the dynamic count join, cut pass,
virtual endpoint pass and arithmetic serialization all charged. -/
theorem native_size : (native e seed F counts cut occupied).size ≤ counts.size +
    PackedDeckScore.queryCost (PackedDeckScore.batchBits (S × (Fin D × Bool)) (Row old D)) d w +
    cut.size + (Views.frame F).size + 1 + Fintype.card (Row old D)*(nodes e*(100*(w+1)^2)) := by
  have hf := (exists_frame e seed F counts cut occupied).choose_spec.1
  have hsize := operands_size e seed F counts cut
  have hm := matched_size e seed F counts
  exact hf.trans (by omega)

omit [NeZero D] in
/-- The native program carries the successor's live enable verbatim, including empty live intervals. -/
theorem native_enabled (x : σ → Bool) (r : Row old D) :
    (native e seed F counts cut occupied).eval x (r,.inl ()) = x (occupied (candidate e (n := n) r)) :=
  ((exists_frame e seed F counts cut occupied).choose_spec.2 x r).1

variable {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
variable (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (oldSite : p.layout.Site ↪ Fin sites) (oldEdge : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np)
variable (cell : (G e p bin perm positive first q).Site → Fin C) (aux : (G e p bin perm positive first q).Site → ℕ)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "sID" => siteRows e p oldSite seed
local notation3 "eID" => outputRows e p bin perm positive first q oldEdge seed
variable {x : σ → Bool} (rep : Represents (G e p bin perm positive first q) cell aux (siteRows e p oldSite seed)
  (outputRows e p bin perm positive first q oldEdge seed) portID F x)
variable (room : ∀ v, incoming (G e p bin perm positive first q) v < 2^w)
variable (names : S → ℕ) (a : S) (i : Fin D) (z : {z : p.layout.Edge // bin z = some (perm i a)}) (src : Bool)
local notation3 "r₀" => ((oldEdge z.val,i,src) : Row old D)
local notation3 "j₀" => blocks p.layout bin perm m a
local notation3 "desc₀" => descriptor p.layout bin perm m names z (some (i,true))
local notation3 "u₀" => seedHook e p bin perm a i z src
local notation3 "v₀" => (G₀).dst u₀
local notation3 "wire₀" => wireStart G₀ eID portID v₀ ⟨u₀,.inr rfl⟩
variable (hcount : value (fun j => counts.eval x (a,none,j)) = blocks p.layout bin perm m a)
variable (hcut : ∀ field, value (fun j => cut.eval x ((oldEdge z.val,some (i,true)),field,j)) =
  CutCircuit.Result.read (descriptor p.layout bin perm m names z (some (i,true))) field)

include rep room hcount hcut in
/-- The four source words of the native program are exactly the matched count, physical
span and ordinal, and destination incidence word start. -/
theorem operands_live (arg : Arg) :
    value (fun j => (operands e seed F counts cut).eval x (r₀,arg,j)) = fields j₀ (desc₀).span (desc₀).ordinal wire₀ arg := by
  cases arg with
  | matched =>
    simp only [operands,Frame.select_eval,parallelFrame_eval_inl]
    exact (matched_hook e seed F counts p bin perm positive first q oldSite oldEdge portID cell aux rep a i z src).2.trans hcount
  | span =>
    simp only [operands,Frame.select_eval,parallelFrame_eval_inr,parallelFrame_eval_inl]
    exact hcut .span
  | ordinal =>
    simp only [operands,Frame.select_eval,parallelFrame_eval_inr,parallelFrame_eval_inl]
    exact hcut .ordinal
  | wire =>
    simp only [operands,Frame.select_eval,parallelFrame_eval_inr]
    rw [candidate_hook e seed p bin perm positive first q oldEdge a i z src]
    exact Views.dest_value F G₀ cell aux sID eID portID rep room u₀

include rep room hcount hcut in
/-- Every occupied terminal hook candidate emits the native site address and exact
nine-word equality payload on the immutable branch, for both orientations. -/
theorem native_live (hone : 1 < 2^w)
    (fit : Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*j₀ +
      incoming G₀ v₀ + count p.layout bin (perm i a) < 2^w) :
    value (fun j => (native e seed F counts cut occupied).eval x (r₀,.inr (.inl j))) =
      (F.sites (sID v₀)).val ∧
    ∀ j : Fin 9, value (fun k => (native e seed F counts cut occupied).eval x (r₀,.inr (.inr (j,k)))) =
      (Packet.record (terminalHook e p bin perm positive first q a id (workAt e p bin perm positive first q)
        sID eID portID names i z src))[j.val]?.getD 0 := by
  obtain ⟨_,hp,hw⟩ := (exists_frame e seed F counts cut occupied).choose_spec.2 x r₀
  constructor
  · apply (congrArg value (funext hp)).trans
    rw [candidate_hook e seed p bin perm positive first q oldEdge a i z src]
    exact rep.dst u₀
  · intro j
    let input := fun arg => value (fun l => (operands e seed F counts cut).eval x (r₀,arg,l))
    let data := fields j₀ (desc₀).span (desc₀).ordinal wire₀
    have hd : input = data := funext (operands_live e seed F counts cut p bin perm positive first q
      oldSite oldEdge portID cell aux rep room names a i z src hcount hcut)
    have hdata (arg : Arg) : data arg < 2^w := (congrFun hd arg).symm.trans_lt (value_lt _)
    let cap := Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*j₀
    have hs : originalScale e*j₀ ≤ cap := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Fintype.equivFin (Unit ⊕ Unit ⊕ Fin e.count) (.inr (.inl ()))).isLt.le)
    have ho := ordinal_le_bin (m := m) p.layout bin perm names (perm i a) z (some (i,true))
    have hv : wire₀ ≤ incoming G₀ v₀ := (Nat.le_add_right _ _).trans (wireEnd_le G₀ eID portID _ _)
    have hstage : originalScale e * data .matched + data .ordinal < 2^w :=
      ((Nat.add_le_add hs ho).trans (Nat.add_le_add_right (Nat.le_add_right cap _) _)).trans_lt fit
    have hwire : Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*data .matched + data .wire < 2^w :=
      ((Nat.add_le_add_left hv cap).trans (Nat.le_add_right _ _)).trans_lt fit
    have hw' := hw j
    change (wordExpr e j).Fits w input → _ at hw'
    have safe : (wordExpr e j).Fits w data :=
      words_fit e w data hdata hone hstage hwire _ (List.getElem_mem (j.isLt.trans_eq (code_length e).symm))
    have hout := hw' (hd.symm ▸ safe)
    change value _ = (Packet.record ((code e).read input))[j.val]?.getD 0 at hout
    rw [hd,show (code e).read data = _ from read_record e p bin perm positive first q a sID eID portID names i z src] at hout
    exact hout

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
