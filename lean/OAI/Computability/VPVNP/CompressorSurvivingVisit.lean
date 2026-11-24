import OAI.Computability.VPVNP.CompressorSurvivingArithmetic
import OAI.Computability.VPVNP.CompressorSurvivingGeometry
import OAI.Computability.VPVNP.CompressorSurvivingEvents
import OAI.Computability.VPVNP.CompressorSurvivingPass
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# A physical surviving subdivision call

The same table reads the four physical inputs on every ordinal. Its thirteen
stores write the width, the interval fields and the two compact references at
their exact addresses. All other external words retain their previous values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingNative

open BurstRAM Allocation
open scoped Fin.CommRing
variable {w n A : ℕ}

/-- Instantiate the surviving-piece table with the selected role and the allocation's actual
array heads. -/
abbrev program (T : Allocation w n A) (t : Fin 4) (abs layout : Word w) :=
  (pass.table.instantiate w (params T t abs layout)).program

/-- Addresses of the common layout word, the absolute-ID table, and the ten fields of each
motif term. -/
def readRegion (T : Allocation w n A) (abs layout : Word w) (x : ℕ) : Prop :=
  x = layout.val ∨ (abs.val ≤ x ∧ x < abs.val+n) ∨ ∃ i : Fin n, T.termStart i ≤ x ∧ x < T.termStart i+10

/-- Union of the writable row regions for this role over the dense motifs. -/
def writeRegion (T : Allocation w n A) (t : Fin 4) (x : ℕ) := ∃ i : Fin n, ¬(T.row (i,t)).Outside x

/-- Per-call report specification with seventeen probes, fixed instruction count, empty branch
tape, and read and write regions. -/
structure Site (T : Allocation w n A) (t : Fin 4) (abs layout : Word w) (r : Report w) : Prop where
  probes : r.probes = 17
  length : r.events.length = ops.length
  bits : choiceBits r.events = []
  reads : SourceTransport.Reads (readRegion T abs layout) r.events
  writes : SourceTransport.Writes (writeRegion T t) r.events

theorem one (T : Allocation w n A) (fit : T.Fits) (abs layout : Word w) (absFit : abs.val+n ≤ 2^w)
    (width : Id n → ℕ) (t : Fin 4) (cap : ℕ) (hc : ops.length < cap) :
    SurvivingPass.One T width (Inputs T abs layout width) t (program T t abs layout) cap (Site T t abs layout) := by
  intro i j m input
  let k := i.val*T.subdiv t + j.val
  let st : Word w := Fin.ofNat _ k
  let p := params T t abs layout
  let out := report p st m
  let d := read p st m
  let r := T.row (i,t)
  let b := width (i,t)
  let f := SurvivingCells.address r j.val
  let v := SurvivingCells.value b (T.subdiv t) j.val
  have ge := read_geometry T fit abs layout width m absFit input i t j
  change d = ⟨(j.val : Word w),r.count,(b : Word w),r.total,r.dst⟩ at ge
  obtain ⟨_,htotal,hbank,_,hcount⟩ := T.row_vals fit (i,t)
  change r.count.val = T.subdiv t at hcount
  have bank : r.bank = r.total+1 := by
    change (Fin.ofNat (2^w) (T.recordStart (i,t)+1)) = (Fin.ofNat (2^w) (T.recordStart (i,t))) + 1
    exact Nat.cast_add_one _
  have hpos : j.val < r.count.val := by rw [hcount]; exact j.isLt
  have hb : b < 2^w := by
    change width (i,t) < 2^w
    rw [← input.width i t]; exact Fin.isLt _
  have addr (e : Fin 13) : (d.addresses e).val = f e := by
    rw [ge,addresses_exact r b j.val bank,Fin.val_natCast]
    exact Nat.mod_eq_of_lt (SurvivingCells.address_fit (T.space fit (i,t)) hpos e)
  have val (e : Fin 13) : (d.values e).val = v e := by
    rw [ge,values_exact r b j.val hb hpos,Fin.val_natCast,hcount]
    exact Nat.mod_eq_of_lt (SurvivingCells.value_fit hb (hcount ▸ r.count.isLt) j.isLt e)
  obtain ⟨he,ret,afterCall,probes,len,bits⟩ := native p st m
  change execute (program T t abs layout) (1+ops.length) ((program T t abs layout).start st) m [] = some out at he
  have inc : out.result = some (Fin.ofNat (2^w) (k+1)) := ret.trans (congrArg some (Nat.cast_add_one k).symm)
  have reportEq : out = ⟨out.events,some (Fin.ofNat _ (k+1))⟩ := congrArg (Report.mk out.events) inc
  refine ⟨out.events,?_,?_,?_,?_⟩
  · rw [← reportEq]
    have run := execute_extend he (cap-(1+ops.length))
    rwa [show 1+ops.length+(cap-(1+ops.length)) = cap by omega] at run
  · change Site T t abs layout ⟨out.events,some (Fin.ofNat _ (k+1))⟩
    rw [← reportEq]
    obtain ⟨hr,hw⟩ := footprint p st m
    refine ⟨probes,len,bits,fun a z h => ?_,fun a z h => ?_⟩
    · obtain ⟨e,readEq⟩ := hr a z h
      have hread := congrFun (read_addresses T fit abs layout width m absFit input i t j) e
      change (readAddresses p st m e).val = _ at hread
      rw [← readEq,hread]
      have side : T.layout.toNat ≤ 1 := by cases T.layout <;> decide
      have hrole := t.isLt
      have hi := i.isLt
      fin_cases e
      · exact Or.inr (Or.inl ⟨by simp,by simp [hi]⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨i,by simp,by simp⟩)
      · refine Or.inr (Or.inr ⟨i,?_,?_⟩)
        · change T.termStart i ≤ T.termStart i+2+(T.layout.toNat*4+t.val); omega
        · change T.termStart i+2+(T.layout.toNat*4+t.val) < T.termStart i+10; omega
    · obtain ⟨e,ea⟩ := hw a z h
      exact ⟨i,ea ▸ addr e ▸ SurvivingCells.inside hpos e⟩
  · intro e
    change (after m out.events (f e)).val = _
    rw [afterCall]
    let xs := stores d
    have live : ∃ av ∈ xs, av.1.val = f e :=
      ⟨(d.addresses e,d.values e),(by unfold xs stores; exact List.mem_ofFn.mpr ⟨e,rfl⟩),addr e⟩
    have agree (av) (hav : av ∈ xs) (hh : av.1.val = f e) : av.2 = d.values e := by
      obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hav
      have eq : f g = f e := (addr g).symm.trans hh
      exact congrArg d.values (SurvivingCells.address_injective (T.space fit _) (T.apart fit _) hpos eq)
    change (ScatterCall.applyStores m xs (f e)).val = _
    rw [ScatterCall.stored xs m live agree]
    exact val e
  · intro x hx
    rw [afterCall]
    apply ScatterCall.outside
    intro av hav
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hav
    exact (addr e ▸ (hx e).symm)

end CompressorRecords.ShrinkSliceSweep.SurvivingNative

end VPVNP
end Computability
end OAI
