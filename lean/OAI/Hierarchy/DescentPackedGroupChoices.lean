import OAI.Hierarchy.DescentPackedStageChoices
import OAI.Hierarchy.DescentGroupedMeasuredPaint

namespace OAI
/-! # Native packed choice of the two parameters in an actual grouped stage -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies DescentPacking DescentGL DescentBinaryField DescentAffineColors StarKeys DescentHostDirectory
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM.PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {C L k ℓ Δ d b w M : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k)
variable (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
local notation "fee" => A.wire*(A.z*G.b)
local notation "D" => DescentHostDegree.gap A.degree
local notation "cap" => 2^(DescentHostDegree.packExponent 20 A.degree)*(fee*A.cap)
local notation "full" => W.siteUnits (fun v => A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "outgoing" => fun v : W.graph.Site => Finset.card (Finset.filter (fun edge => W.graph.src edge = v) W.core)
local notation "wt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev full g))
local notation "amt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev outgoing g))

/-- Every outgoing edge of a cell is funded at that edge's actual scaled
width. Thus a small occurrence counter needs only the bits of the stage cap. -/
theorem grouped_outgoing_cap (g v x) : amt g v x≤A.cap := by
  have pos : 0<fee := Nat.mul_pos A.wirePos (Nat.mul_pos A.unitPos (by have := G.paid;omega))
  have one (u : W.graph.Site) : fee*(outgoing u)≤full u := by
    have «rec» := W.siteUnits_outgoing (fun u=>A.hub (A.pos u).2) A.records A.wire 256 A.hist
      (fun _=>()) (fee) (fun e he=>by rw [A.widths e he]) (by decide) u
    simpa only [outgoing_count] using «rec»
  dsimp only [Padded.table]
  split
  · rename_i live
    let owner : J × V := (ej.symm g, ev.symm ⟨v.val, live⟩)
    apply Nat.le_of_mul_le_mul_left _ pos
    change fee * blockMass W.graph A.pos A.block outgoing owner x ≤ fee * A.cap
    calc
      _ ≤ blockMass W.graph A.pos A.block full owner x := by
        unfold blockMass
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro u _
        by_cases hit : A.pos u = owner ∧ A.block u = x
        · simpa only [ite_eq_left hit] using one u
        · simp only [ite_eq_right hit, Nat.mul_zero, Nat.le_refl]
      _ ≤ _ := A.small owner x
  · exact Nat.zero_le _

include h in
theorem grouped_outgoing_total : (∑g,∑v,∑x,amt g v x)=W.core.card := by
  let f (gv:J×V) := ∑x,blockMass W.graph A.pos A.block outgoing gv x
  have front (g : Fin C) : (∑v,∑x,amt g v x)=∑v:Fin L,f (ej.symm g,ev.symm v) := by
    let val (v:Fin L) := f (ej.symm g,ev.symm v)
    have term (v:Fin (2^ℓ)) : (∑x,amt g v x)=if ok : v.val<L then val ⟨v.val,ok⟩ else 0 := by
      by_cases live : v.val<L <;> simp [Padded.table,live,val,f,groupedCounts]
    simp only [term]
    let e : Fin L↪Fin (2^ℓ) := ⟨Fin.castLE h,Fin.castLE_injective h⟩
    rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (by
      intro v _ missing
      have gone : ¬v.val<L := fun hi=>missing (Finset.mem_map.mpr ⟨⟨v.val,hi⟩,Finset.mem_univ _,Fin.ext rfl⟩)
      simp [gone]),Finset.sum_map]
    exact Finset.sum_congr rfl (fun v _=>by simp [e,val,v.isLt])
  rw [Finset.sum_congr rfl (fun g _=>front g)]
  calc
    _ = ∑g:J,∑v:V,f (g,v) := by
      rw [←ej.sum_comp]
      simp only [Equiv.symm_apply_apply]
      exact Finset.sum_congr rfl (fun g _=>ev.symm.sum_comp (fun v=>f (g,v)))
    _ = ∑z:J×V,f z := Fintype.sum_prod_type _ |>.symm
    _ = ∑u,outgoing u := total_blockMass _ _ _ _
    _ = W.core.card := by
      calc
        _ = ∑ u : W.graph.Site, live (nativeTraffic W.graph W.core (fun _ => ())) u :=
          Finset.sum_congr rfl fun u _ => (outgoing_count W.graph W.core (fun _ => ()) u).symm
        _ = W.core.card := live_is_core W.graph W.core (fun _ => ())

/-- The packed multiplier scan on the immutable stage geometry. -/
theorem packed_seed (rs : DynamicSplit.Roster ℓ Δ)
    (L₁ : DescentPackedMinimum.Layout (2^k-1)) (fit : DescentPackedMinimum.Fits L₁ w (1+k*2^k) M (2^ℓ) C)
    (lanes : 0<M) (room : C*2^ℓ*2^k<2^w) (m : Memory w)
    (stored : ∀i,DescentPackedScore.Input (M:=M) (L₁.source i) (L₁.dictionary i) PackedSplit.value
      (PackedSplit.state (DynamicSplit.incoming rs) wt D cap (modulus A.fieldBits) (seedAt k i)) m) :
    let Q := uniformColonyScore (DynamicSplit.incoming rs) wt D cap (modulus A.fieldBits)
    ∃out : Memory w,∃i : Fin (2^k-1),
      (DescentPackedMinimum.search L₁ w (2^ℓ) C M).Exec m out (PackedChoices.ticks L₁ (2^ℓ) C M) ∧
      out (L₁.result+(2^k-1-1))=(i.val:Word w) ∧
      (scanMinimum Q (nonzeroWords k)).1=some (seedAt k i,Q (seedAt k i)) ∧
      MultiplierMinimumRAM.key (seedAt k i)=i.val+1 ∧ ∀z<L₁.work,out z=m z :=
  by
    obtain ⟨out,i,run,key,seed,word,low,_⟩:=PackedChoices.seed _ _ D cap A.fieldBits L₁ fit lanes room m stored
    exact ⟨out,i,run,key,seed,word,low⟩

/-- On the retained banks of the multiplier issued by the first scan,
the second packed scan yields the actual measured history. -/
theorem packed_paint (he : 0≤ε) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (i : Fin (2^k-1)) (seed : let Q := uniformColonyScore (DynamicSplit.incoming rs) wt D cap (modulus A.fieldBits)
      (scanMinimum Q (nonzeroWords k)).1=some (seedAt k i,Q (seedAt k i)))
    (L₂ : DescentPackedMinimum.Layout (2^(k+1))) (fit : DescentPackedMinimum.Fits L₂ w (PackedContribution.width k b) M (2^ℓ) C)
    (lanes : 0<M) (room : W.core.card<2^w) (short : A.cap<2^b) (m : Memory w)
    (stored : ∀j,DescentPackedScore.Input (M:=M) (L₂.source j) (L₂.dictionary j) (PackedContribution.value j)
      (fun v g=>PackedContribution.actual b (DynamicSplit.incoming rs) wt amt D cap (modulus A.fieldBits) (seedAt k i) g v) m) :
    ∃out : Memory w,∃j : Candidate k,
      (DescentPackedMinimum.search L₂ w (2^ℓ) C M).Exec m out (PackedChoices.ticks L₂ (2^ℓ) C M) ∧
      out (L₂.result+(2^(k+1)-1))=(j.val:Word w) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      ∀z<L₂.work,out z=m z := by
  obtain ⟨out,j,run,word,paint,low,_⟩:=PackedChoices.affine (DynamicSplit.incoming rs) wt amt D cap A.fieldBits (seedAt k i)
    L₂ fit lanes (by rw [A.grouped_outgoing_total ej ev h];exact room)
    (fun g v x=>(A.grouped_outgoing_cap (ℓ:=ℓ) ej ev g v x).trans_lt short) m stored
  exact ⟨out,j,run,word,A.grouped_scanned he ej ev h rs members _ j seed paint,low⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
