import OAI.Computability.BorderVNP.TransmissionJointLiteral
import OAI.Computability.BorderVNP.FiniteWideBootScale

/-! # The free literal field at a field-valued processor

The literal address uses the encoded size of the program that actually runs.
After that program, the public decoder, role and handoff fields, and the first
advice bit, every following free position reads exactly its assigned bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine TeamTapeHandoff RoutingISA.Pins

variable {pc reg k routines R r w a d : ℕ}

/-- Absolute offset of the first free bit, using the actual field-program length. -/
abbrev freeStartWith (physical : Program) (r k reg w n : ℕ) :=
  FiniteBoot.offset physical k reg r w n

/-- The free literal follows the distributed reference bit of this same physical program. -/
theorem freeStartWith_eq_adviceOffsetWith_succ (physical : Program) (r k reg w n : ℕ) :
    freeStartWith physical r k reg w n = adviceOffsetWith physical r k reg w n + 1 := by
  simp only [freeStartWith,FiniteBoot.offset,adviceOffsetWith,entryLiteral,Nat.add_assoc]

/-- The whole free suffix on the true literal, in its original order. -/
theorem literal_splitWith (physical : Program) (P : TeamOpcode.Program pc reg k routines)
    (S : SiteData R r reg k w a) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    ∃ pref : List Bool, pref.length = freeStartWith physical r k reg w n ∧ F.literal j = pref ++ List.ofFn (S.free u j) := by
  intro G F
  let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
  let interior := Wires.innerWidth r reg w e (w+1)
  let control := sitePrefix (S.publicWords u) S.block S.limit S.burst (S.start P u) j e n
  let first := programPrefix physical ++ TeamTapeInput.parameters (TeamTapeInput.digits n stride)
    (TeamTapeInput.digits n interior) ++ TeamTapeInput.Entry.setupBits (w+1) n (j.val*stride) (2^e)
  let cap := prefixCapacity r k reg w n
  refine ⟨first ++ control ++ List.replicate (cap-control.length) false ++ [S.advice u j],?_,?_⟩
  · have hc : control.length ≤ cap := sitePrefix_length_le ..
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,first,
      TeamTapeInput.length_parameters,length_setupBits,freeStartWith,FiniteBoot.offset,entryLiteral]
    dsimp only [cap] at *
    unfold cutWidth
    omega
  · change programPrefix physical ++ List.ofFn (cutTail n stride interior
      (entryTail (w+1) n (j.val*stride) (2^e) (S.siteBits P n e u j))) = _
    rw [ofFn_cutTail,ofFn_entryTail,SiteData.siteBits,ofFn_payloadBits]
    simp only [first,control,cap,payload,List.append_assoc]

/-- Read a supplied free bit on the same raw input that reaches the field
accumulator and its native row checker. -/
theorem literal_free_getWith (physical : Program) (P : TeamOpcode.Program pc reg k routines)
    (S : SiteData R r reg k w a) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (ibase hbase starbase : ℕ) (z : Fin a) :
    let G := wiringWith physical P S d link n e fit
    ((G.processorFields u pin ext ibase hbase starbase).literal j)[freeStartWith physical r k reg w n+z.val]? =
      some (S.free u j z) := by
  intro G
  obtain ⟨pref,hl,eq⟩ := literal_splitWith physical P S link n e fit u j pin ext ibase hbase starbase
  rw [eq,←hl,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  simp

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
