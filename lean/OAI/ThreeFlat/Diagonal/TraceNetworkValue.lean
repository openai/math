import OAI.ThreeFlat.Diagonal.TraceBinaryMass
import OAI.ThreeFlat.Diagonal.TraceNetwork
import OAI.ThreeFlat.Diagonal.TraceClockGuards
import OAI.ThreeFlat.Diagonal.TraceFactorProduct
import OAI.ThreeFlat.Diagonal.TraceMemoryPacket

namespace OAI
/-! # The contraction of the paired-row trace computes the weighted native RAM value -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory RAMSerialization BooleanTranscript
open Computability.VPVNP.VerifierNetwork (Frame)
open TraceBanks TraceWords TraceRows TraceCompose

variable {F : Type*} [Fintype F] [CommRing F] {w p r k f S d : ℕ}
private abbrev R w p r := Row (w+1) (Snapshot w p r)

private noncomputable def terminal (hF : Fintype.card F ≤ 2^w) (x : R w p r) : F :=
  match x with
  | .halt _ out => (wideCode (RAM.FieldCode.ofCardLe hF)).terminal out
  | _ => 1

theorem terminalBits (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (xs : Fin f → R w p r) (z : SortBits d (w+1)) (fit : S+f ≤ 2^(1+d)) :
    (∏ v : Fin (2^d), ∏ s : Fin 2, ∏ i : Option F, TraceTerminal.unary i
      (rowBits hF hw hp M st hs hf header (writeCpu hw hp xs) z v (.inr (s,.inr i)))) =
      terminalProduct (wideCode (RAM.FieldCode.ofCardLe hF)) (List.ofFn xs) := by
  classical
  have hr : terminalProduct (wideCode (RAM.FieldCode.ofCardLe hF)) (List.ofFn xs) = ∏ t, terminal hF (xs t) := by
    simp only [terminalProduct, ← List.ofFn_comp', List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro i _
    cases xs i <;> rfl
  rw [hr, ← prod_clock_sites S d fit]
  apply Finset.prod_congr rfl; intro v _
  apply Finset.prod_congr rfl; intro s _
  by_cases h : S ≤ slotAddress d v s ∧ slotAddress d v s-S < f
  · obtain ⟨ha,ht⟩ := h
    have val : (fun j => (read (cpuPin s.castSucc j)).2.eval
        (TracePhysical.valuation (by omega) v header (writeCpu hw hp xs) z)) =
        (rowFormat hw hp).encode (clockAt xs (slotAddress d v s-S)) :=
      funext (cpuPin_clock hw hp v s.castSucc header xs z ha)
    simp only [rowBits,guardTerm,packetIf_eval,ha,ht,and_self,decide_true,ite_true,substituteFintype_eval,
      val,Frame.circuit_eval,atClock,dite_true]
    have term (row : R w p r) : (∏ i : Option F, TraceTerminal.unary i
        ((TraceTerminal.rowFrame hF hw r).eval ((rowFormat hw hp).encode row) i)) = terminal hF row := by
      have test := TraceTerminal.rowFrame_eval hF hw hp row
      cases row <;> exact test
    simpa only [clockAt,dite_eq_left ht,dite_true] using term (clockAt xs (slotAddress d v s-S))
  · have hn (i : Option F) : TraceTerminal.unary i (Option.isNone i) = (1 : F) := by cases i <;> rfl
    simp only [rowBits,guardTerm,packetIf_eval,h,decide_false,Bool.false_eq_true,ite_false]
    have hone : (∏ i : Option F, TraceTerminal.unary i ((literal i.isNone).2.eval
        (TracePhysical.valuation (by omega) v header (writeCpu hw hp xs) z))) = 1 := by
      simp only [show ∀ i : Option F, ((literal i.isNone).2.eval (TracePhysical.valuation (by omega) v header (writeCpu hw hp xs) z)) = i.isNone from fun _ => rfl,hn,Finset.prod_const_one]
    rw [hone]
    by_cases ha : S ≤ slotAddress d v s
    · simp [atClock,ha,show ¬ slotAddress d v s-S < f from fun ht => h ⟨ha,ht⟩]
    · simp [atClock,ha]

theorem product_binaryWeight (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : ℕ → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1)) (fit : S+f ≤ 2^(1+d)) :
    (∏ v : Fin (2^d), ∏ a : Factor F, scalar a
      (rowBits hF hw hp M st hs hf (fun i : Fin S => header i.val) cpu z v a)) =
      binaryWeight (RAM.FieldCode.ofCardLe hF) M hw hp st S d f header cpu z := by
  classical
  let h := fun i : Fin S => header i.val
  let xs := readCpu hw hp cpu
  let rs := List.ofFn xs
  let b := fun v a => rowBits hF hw hp M st hs hf h cpu z v a
  let P := exposed M
  let c := P.start (wide st)
  let valid := writeCpu hw hp xs = cpu ∧ before (rs.headD .pad) = some c ∧ pairs P rs ∧
    memoryPass (by omega) S d (wide ∘ header) (report rs).events z
  have guards : (∀ v j, b v (guardFactor F j) = true) ↔ valid := by
    rw [guards_iff]
    let checkC := all_canonical hF hw hp M st hs hf h cpu z fit
    have checkP := all_pairs hF hw hp M st hs hf h xs z fit
    have checkF := all_first hF hw hp M st hs hf h xs z fit
    constructor
    · rintro ⟨hm,hc,hp',hf'⟩
      have he := checkC.mp hc
      have hpairs : pairs P rs := checkP.mp (by rw [he]; exact hp')
      have hfirst : before (rs.headD .pad) = some c := checkF.mp (by rw [he]; exact hf')
      have hl := (local_iff_pairs P c rs).mpr ⟨hfirst,hpairs⟩
      refine ⟨he,hfirst,hpairs,(all_memoryPacket_iff hw hp hs hf header xs z hl fit).mp ?_⟩
      rw [he]
      exact hm
    · rintro ⟨he,hfirst,hpairs,hmem⟩
      have hl := (local_iff_pairs P c rs).mpr ⟨hfirst,hpairs⟩
      refine ⟨?_,checkC.mpr he,?_,?_⟩
      · have hm := (all_memoryPacket_iff hw hp hs hf header xs z hl fit).mpr hmem
        rw [he] at hm
        exact hm
      · have ht := checkP.mpr hpairs
        rw [he] at ht
        exact ht
      · have ht := checkF.mpr hfirst
        rw [he] at ht
        exact ht
  change (∏ v, ∏ a, scalar a (b v a)) = _
  rw [factorProduct]
  by_cases good : valid
  · rw [ite_eq_left (guards.mpr good)]
    have he := good.1
    have term := terminalBits hF hw hp M st hs hf h xs z fit
    rw [he] at term
    rw [term]
    unfold binaryWeight
    exact (ite_eq_left good).symm
  · rw [ite_eq_right (fun h => good (guards.mp h))]
    unfold binaryWeight
    exact (ite_eq_right good).symm

end ThreeFlat.Diagonal.TraceRowPackets

namespace ThreeFlat.Diagonal.TracePhysical

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory TraceRows TraceRowPackets

theorem network_eval_native {F : Type*} [Fintype F] [CommRing F] {w p r k f S d : ℕ}
    (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : ℕ → Word w) (fit : S+f ≤ 2^(1+d)) :
    (network hF hw hp M st hs hf d).eval (headerPins (fun i : Fin S => header i.val)) =
      RAM.value (RAM.FieldCode.ofCardLe hF) M f st (initialMemory S header) := by
  rw [network_eval_packets, value_eq_sum_binary (RAM.FieldCode.ofCardLe hF) M hw hp st S d f header hs hf fit]
  apply Finset.sum_congr rfl; intro cpu _
  apply Finset.sum_congr rfl; intro z _
  exact product_binaryWeight hF hw hp M st hs hf header cpu z fit

end ThreeFlat.Diagonal.TracePhysical

end OAI
