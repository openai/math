import OAI.Hierarchy.GridHonestController
import OAI.Hierarchy.GridProgrammed
import OAI.Hierarchy.GridNativeEvaluator
import OAI.ThreeFlat.RAM.AdmissionPost

namespace OAI
/-! # The full selector and the physical image of the typed controller

The true flag retains the exact bitstring admitted by the history reader.
Erasing the fixed-direction proof of a setting preserves both the admission
test and every word of its contraction image.
-/

namespace Hierarchy.GridDispatchFlag
open ThreeFlat RAM Diagonal.HistoryContraction
open Computability.VPVNP.BurstRAM UniversalGrid GridThrough
open scoped Classical
noncomputable section
set_option quotPrecheck false

section Flag
variable {F : Type*} [CommSemiring F] {S : Shape} (P : Plan F S) (C : P.Codes)
variable (bits : P.History→ℕ) (cap : ℕ)

/-- A successful parse of the suffix of a true-flag selector is precisely
a successful simulation branch of the full decoder. -/
theorem true_decode (s : Bits (cap+1)) {z : GridSelector.Trace P bits} (flag : s 0=true)
    (read : GridSelector.read P C bits cap (List.ofFn (Fin.tail s))=some z) :
    GridSelector.decode P C bits cap s=some (some z) := by
  simp only [GridSelector.decode,flag,ite_true,read,Option.map_some]

/-- The accepted complete selector equals the actual simulation's canonical
encoding, including its terminal bits and zero padding. -/
theorem true_encode (room : GridSelector.Room P C bits cap) (s : Bits (cap+1))
    {z : GridSelector.Trace P bits} (flag : s 0=true)
    (read : GridSelector.read P C bits cap (List.ofFn (Fin.tail s))=some z) :
    GridSelector.encode P C bits cap room (some z)=s :=
  GridSelector.encode_decode P C bits cap room s (some z) (true_decode P C bits cap s flag read)
end Flag

section Write
variable {F : Type} [Field F] [Fintype F] {S : Shape} {k q p n e a W : ℕ}
variable (P : Plan F S) (C : P.Codes) (bits : P.History→ℕ) (cap : ℕ)
variable (X : Catalyst.Approximation F k (q*p)) (dir : Fin e→Fin k)
variable (setting : Option (GridSelector.Trace P bits) → Setting X n e dir)
variable (bytes : Bits a) (s : Bits (cap+1))

local notation "selected" => honestController P C bits setting bytes bytes s
local notation "raw" => (GridSelector.decode P C bits cap s).map (fun z=>(setting z).1)

omit [Fintype F] in
/-- Forgetting the fixed direction of the actual selected program is the
erasure computed by the native compiler. -/
theorem erase : raw=(selected).map Subtype.val := by
  simp [honestController,Option.map_map,Function.comp_def]

/-- The writer compiled from erased programs discharges the entire native
distribution write clause on the genuine fixed-direction settings. -/
theorem typed_write (field : FieldCode F W) (emit : PhysicalProcedure.Procedure W)
    (pre : Memory W→Prop) (pins : Fin (e*2)→Bool) (budget : ℕ)
    (run : TickStageSpec.Admission field emit.block emit.publicData pre (fun _=>(raw).isSome)
      (fun _ out=>∀ v,raw=some v → ∀ i<BitLayout.footprint (GridNativeEvaluator.net X v),
        out i=BitLayout.memory (GridNativeEvaluator.net X v) field pins (fun _=>false) i) budget) :
    TickStageSpec.Admission field emit.block emit.publicData pre (fun _=>(selected).isSome)
      (fun _ out=>∀ v,selected=some v → ∀ i<BitLayout.footprint (GridNativeEvaluator.net X v.1),
        out i=BitLayout.memory (GridNativeEvaluator.net X v.1) field pins (fun _=>false) i) budget := by
  have erasure := erase P C bits cap X dir setting bytes s
  intro p' r' k' machine pc reg pub exit installed values cfg mem begin_ valid
  obtain ⟨accept,reject⟩:=run machine pc reg pub exit installed values cfg mem begin_ valid
  have agrees : (selected).isSome=(raw).isSome:=by simp [erasure]
  constructor
  · intro good
    obtain ⟨ticks,bound,last,out,done,written,ran⟩:=accept (agrees ▸ good)
    refine ⟨ticks,bound,last,out,done,?_,ran⟩
    intro v receives
    apply written v.1
    rw [erasure,receives]; rfl
  · intro bad;exact reject (fun yes=>bad (agrees.symm ▸ yes))

end Write
end
end Hierarchy.GridDispatchFlag

end OAI
