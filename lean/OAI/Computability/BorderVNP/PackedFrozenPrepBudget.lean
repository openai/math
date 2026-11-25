import OAI.Computability.BorderVNP.PackedFrozenPrepFreshCost
import OAI.Computability.BorderVNP.PackedFrozenPrepCarryBudget
import OAI.Computability.BorderVNP.PackedFrozenSelectedPre
import OAI.Computability.BorderVNP.PackedInheritedWorkSelectedPreCost

/-! # Cost of the actual batched input to each augmented epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Cover.AddressCircuit BorderVNP.Epoch Shortening Shortening.PublicCapacity Packing
open Inherited FrozenTape ProgramSchemas WorkWords EnrichedOuter Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

private theorem log_for_subdivision {n r np V L : ℕ} (s : Shape) (extra : ℕ)
    (ports : np ≤ s.sites) (volume : s.volume V≤r*n) (hL : 1≤L) (hlog : L=logWidth r n) :
    Nat.clog 2 (8*(extra+1)*(s.sites+s.edges+np+1)) ≤ (60+Nat.clog 2 (8*(extra+1))+1)*L := by
  let c := 8*(extra+1)
  have size : s.sites+s.edges+np+1 ≤ 2*n*r := by dsimp only [Shape.volume] at volume; nlinarith only [ports,volume]
  have hU : 2*n*r ≤ 2^L := by rw [hlog,public_logWidth]; exact Nat.le_pow_clog (by decide) _
  have cfit : c ≤ 2^(Nat.clog 2 c) := Nat.le_pow_clog (by decide) _
  have logfit := Nat.le_mul_of_pos_right (Nat.clog 2 c) hL
  apply Nat.clog_le_of_le_pow
  apply (Nat.mul_le_mul cfit (size.trans hU)).trans
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by change _ ≤ (60+Nat.clog 2 c+1)*L; rw [Nat.add_mul,Nat.add_mul]; omega)

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

set_option maxHeartbeats 1400000 in
/-- All true child tapes, endpoint scans and newly installed records fit a fixed
quartic logarithm per old rectangle. The original geometric subdivision is
charged once for the entire batch. -/
theorem eventually_tape_pre {a x : ℕ} (scales : EpochScales S a x) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let T := epochs scales.τ n
      let V := CoverScale.sites (Cube D) start
      let w := 60*logWidth r n
      ∀ (base : Format), Fintype.card base.Rows ≤ C₀*physicalRows (bottom (D:=D) start) →
      ∀ (deep : S.floor+1+S.drop*T ≤ start) {P : Type} [Fintype P] {bits : P → ℕ}
        {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w)
        (t : ℕ) (ht : t<T) (ports : WorkWords.Ports (portSlots S start t 0))
        (fit : (before S start t 0).sites ≤ 2^w),
        (R.tapePre base t ht ports fit).size ≤ (R.machine t ht).pre.size+
          rowWork C V (logWidth r n) 4 (boundaryShape S start t) := by
  let ext := interiors S
  let Y := 60+Nat.clog 2 (8*(ext+1))+1
  let J := 15000*(8*(ext+1))*2*(Y+1)^3
  let G := 32000*(2*ext+1)*66^3
  obtain ⟨B,carry⟩ := eventually_subdivision_carry S scales C₀
  refine ⟨4+fan S*G+B+fan S*J,?_⟩
  filter_upwards [carry,eventually_boundaries S scales,eventually_ranges S scales (fun _ => 0) (fun _ => 0),
    eventually_ge_atTop 1] with n old rooms ranges hn
  intro r hr start T V w base small deep P fp bits budget cap R t ht ports fit
  let L := logWidth r n
  let s := boundaryShape S start t
  let next := before S start t 0
  let np := portSlots S start t 0
  let fmt := epoch S start w base t
  let leafB := ProductSlots (Fintype.card (Cube D)) (S.level (offset S start t) 0+1) ⊕ ↥(S.source.catalog 0)
  let fee := fun i : Fin (fan S) => PrepBatch.leafCharge (B:=leafB) (s:=s) (extra:=ext) fmt
    (priorEndpoints (S:=S) (start:=start) (w:=w) t) ports fit i
  let paid := s.volume V*L^4
  have hL : 1≤L := by
    change 1 ≤ logWidth r n
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith only [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  have hnp : np ≤ s.sites := by
    simpa only [np,portSlots,pow_zero,one_mul] using (ports_fit S start).1 t
  have hnp' := (ports_fit S start).2 t 0
  have first := (ranges r hr).2 t ht (⟨0,S.rounds_pos⟩ : Fin S.rounds)
  have he : next.edges ≤ 2^w := (Nat.le_mul_of_pos_left _ S.positiveFanIn).trans first.words.2.2.2.2.1
  have width := widthCharge_cubic next.edges hnp' fit he rfl hL
  have hrows : next.sites+next.edges+1 ≤ (2*ext+1)*s.volume V := by
    apply le_trans (b:=next.volume V)
    · dsimp only [Shape.volume]; omega
    · exact s.subdivide_volume ext V
  have pow : L^3 ≤ L^4 := Nat.pow_le_pow_right hL (by decide : 3≤4)
  have wg : Prep.charge next.sites next.edges np w ≤ G*paid := by
    apply width.trans
    calc
      _ ≤ 32000*((2*ext+1)*s.volume V)*66^3*L^4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrows)) pow
      _ = _ := by dsimp only [G,paid]; ring
  let W := Y*L
  have wW : w≤W := by change 60*L ≤ Y*L; exact Nat.mul_le_mul_right _ (by dsimp [Y]; omega)
  have logW := log_for_subdivision (L:=L) s ext hnp ((rooms r hr).1 t ht.le) hL rfl
  have scan (i : Fin (fan S)) := PrepBatch.leafCharge_cubic (s:=s) (extra:=ext) (B:=leafB) fmt
    (priorEndpoints (S:=S) (start:=start) (w:=w) t) ports fit i W wW logW
  have localRows : s.sites+s.edges+np+1 ≤ 2*s.volume V := by dsimp only [Shape.volume]; omega
  have plus : W+1 ≤ (Y+1)*L := by change Y*L+1 ≤ (Y+1)*L; rw [Nat.add_mul Y 1 L,one_mul]; exact Nat.add_le_add_left hL _
  have fresh : 15000*(8*(ext+1)*(s.sites+s.edges+np+1))*(W+1)^3 ≤ J*paid := by
    calc
      _ ≤ 15000*(8*(ext+1)*(2*s.volume V))*((Y+1)*L)^3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ localRows)) (Nat.pow_le_pow_left plus _)
      _ ≤ J*paid := by
        rw [mul_pow]
        apply le_trans (b:=J*s.volume V*L^3)
        · exact (by dsimp only [J]; ring : _ = _).le
        · simpa only [paid,Nat.mul_assoc] using Nat.mul_le_mul_left (J*s.volume V) pow
  let lookup := lookupCost s.sites (Fintype.card fmt.Rows) w w
  have each (i : Fin (fan S)) : fee i ≤ lookup+J*paid := (scan i).trans (Nat.add_le_add_left fresh _)
  have summed : (∑ i, fee i) ≤ fan S*(lookup+J*paid) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.univ) (fun i _ => each i)
  have hlookup : fan S*lookup ≤ B*paid := by
    simpa only [paid,rowWork,Nat.mul_assoc] using old r hr base small deep t ht
  have p0 : 1≤paid := Nat.mul_pos (by dsimp [Shape.volume]; omega) (Nat.pow_pos hL)
  have measured := R.tapePre_size base t ht ports fit
  change (R.tapePre base t ht ports fit).size ≤ (R.machine t ht).pre.size+4+
    fan S*Prep.charge next.sites next.edges np w + ∑ i, fee i at measured
  apply measured.trans
  have cost := Nat.add_le_add (Nat.mul_le_mul_left (fan S) wg) summed
  rw [Nat.mul_add] at cost
  have four := Nat.le_mul_of_pos_right 4 p0
  change _ ≤ (R.machine t ht).pre.size+(4+fan S*G+B+fan S*J)*s.volume V*L^4
  rw [Nat.mul_assoc _ (s.volume V) (L^4)]
  change _ ≤ (R.machine t ht).pre.size+(4+fan S*G+B+fan S*J)*paid
  nlinarith only [cost,hlookup,four]

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
