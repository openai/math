import OAI.Hierarchy.DescentTerminalPackedEpochBill

namespace OAI
/-! # Authentic chronological count words in the packed validator's fixed directory -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentPackedEpochFold DescentTerminalEpochChart Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
variable {A : Type}

theorem ordinals (r lo j : ℕ) (ss : List (Source A)) :
    (shelves r lo j ss).map Shelf.ordinal=List.range' j ss.length := by
  induction ss generalizing lo j with
  | nil=>rfl
  | cons s ss ih=>simp only [shelves,List.map_cons,List.length_cons,List.range'_succ,ih]

theorem count_addresses (head C r out : ℕ) (count exterior : ℕ→ℕ) (ps : List (Shelf A)) :
    (phases head C r count exterior out ps).map (fun s=>s.banks.count.base)=
      (ps.map Shelf.ordinal).map count := by
  induction ps generalizing out with
  | nil=>rfl
  | cons p ps ih=>
    change count p.ordinal::_=count p.ordinal::_
    rw [ih]

theorem counter_words {w : ℕ} (lo C r : ℕ) (count exterior : ℕ→ℕ) (ss : List (Source A)) (m : Memory w) :
    ((controls lo C r ss count exterior).map fun s=>(m s.banks.count.base).val)=
      (List.range' 0 ss.length).map (fun j=>(m (count j)).val) := by
  have addresses : (controls lo C r ss count exterior).map (fun s => s.banks.count.base) =
      (List.range' 0 ss.length).map count := by
    simp only [controls, count_addresses, ordinals]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (fun i => (m i).val)) addresses

/-- Only the literal word in each reached chronological position is compared
with the genuine inherited pair count. A later malformed continuation cannot
introduce a readback obligation after the first rejected profile. -/
theorem native_prefix {S Z U : Type} {V : Type*} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}
    {w : ℕ} (b : Chart bits ok src) (z : b.Pin→Bool) (lo C r : ℕ) (count exterior : ℕ→ℕ)
    (m : Memory w) (path : List V) (amount : V→ℕ)
    (pre : List.IsPrefix (b.counts z) (path.map amount))
    (physical : ∀i,i < (b.rows z).length→∀v,path[i]?=some v→(m (count i)).val=amount v) :
    List.IsPrefix (b.counts z) ((controls lo C r b.layout count exterior).map fun s=>(m s.banks.count.base).val) := by
  rw [counter_words]
  obtain ⟨rest,shape⟩:=b.archived z
  have sizes:=congrArg List.length shape
  simp only [List.length_map,List.length_append] at sizes
  apply List.prefix_iff_getElem?.mpr
  intro i hi
  have here : i < (b.rows z).length:=by simpa [Chart.counts] using hi
  have old:=List.prefix_iff_getElem?.mp pre i hi
  have fits : i < b.layout.length:=by omega
  have known : i < path.length:=by
    have le:=pre.length_le
    simp only [List.length_map] at le
    omega
  let v:=path[i]
  have row : path[i]?=some v:=List.getElem?_eq_getElem known
  simp only [List.getElem?_map,row,Option.map_some,Option.some.injEq] at old
  have at_ : (List.range' 0 b.layout.length)[i]?=some i := by simp [fits]
  simp only [List.getElem?_map,at_,Option.map_some,Option.some.injEq]
  exact (physical i here v row).trans old

end
end Hierarchy.DescentPackedEpochShelves

namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentPackedEpochShelves Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ow" => normalizedIssuedInputOrders X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→Bool)
local notation "choice_" => (actualRoute G _ _ X S.copies q w fit rs ow).follow z
local notation "path_" => (normalizedIssuedRows X G S ordinary reset branch positive room shorten choice_).path.selections

theorem issued_count_words (lo R : ℕ) (count exterior : ℕ→ℕ) (m : Memory w)
    (physical : ∀i,i < ((ch).rows z).length→∀v,(path_)[i]?=some v→(m (count i)).val=selectionCount G v) :
    List.IsPrefix (((ch).rows z).map Observation.count)
      ((controls lo G.C R (ch).layout count exterior).map fun s=>(m s.banks.count.base).val) :=
  native_prefix ch z lo G.C R count exterior m path_ (selectionCount G)
    (packedChart_prefix X G S ordinary reset branch positive room shorten w fit z) physical

end
end Hierarchy.DescentBundleHistory

end OAI
