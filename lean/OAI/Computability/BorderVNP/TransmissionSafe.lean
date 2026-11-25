import OAI.Computability.BorderVNP.TransmissionLegRoom
import OAI.Computability.BorderVNP.TransmissionSafeTables
import OAI.Computability.BorderVNP.TransmissionProgram
import OAI.Computability.BorderVNP.TransmissionInverseBit

/-!
# Address safety for the transmitted bits of a range

The peer and the ordinal are the ones loaded from the directory. The actual address
program reads the frame and offset arrays in the current memory. Destination separation
preserves these arrays throughout the scan. A data sender still performs its explicit
bit comparison on the real source and the computed physical endpoint.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The initial physical routing arrays and their publicly allocated address bounds. -/
structure Schedule (f : BroadcastFrame) (width : Fin f.teams → Fin f.teams → ℕ)
    (pub : Arg → Word w) (m : Memory w) : Prop where
  /-- Values at the actual addresses of the seven frame fields. -/
  frame : f.At (readings pub) (readings m)
  /-- Physical input, frame and header-copy allocations fit the word width. -/
  fit : f.Fits w (readings pub 0)
  /-- The ordered prefix and oriented load tables encode the round-robin schedule. -/
  table : AddressTables fit.three width (readings pub) (readings m)
  /-- Allocated end of the cubic prefix array. -/
  triple : frameField (readings pub) (readings m) 17 + f.teams^3 ≤ 2^w
  /-- Allocated end of the square oriented-load array. -/
  pair : frameField (readings pub) (readings m) 18 + f.teams^2 ≤ 2^w
  /-- Both oriented lists and the broadcast fit into each incident physical block. -/
  capacity : ∀ v : Fin f.teams, v.val ≠ f.team → f.usedPrefix fit width v ≤ f.capacity

/-- Retaining the addressed routing cells preserves every numerical and table fact. -/
theorem Schedule.of_keeps {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    {pub : Arg → Word w} {m m' : Memory w} (a : Schedule f width pub m)
    (keep : KeepsSchedule (readings pub) f.teams (readings m) (readings m')) :
    Schedule f width pub m' :=
  ⟨keep.broadcast a.frame, a.fit, keep.addressTables a.table,
    (keep.field (by decide : 17 ≤ 25)) ▸ a.triple, (keep.field (by decide : 18 ≤ 25)) ▸ a.pair, a.capacity⟩

/-- The finite directory range occupies consecutive in-range ordinals in the appropriate
unordered demand list. -/
structure ScheduledRange (f : BroadcastFrame) (width : Fin f.teams → Fin f.teams → ℕ)
    (r : Range w) : Prop where
  /-- First team is within the physical cluster. -/
  first : r.teamA.val < f.teams
  /-- Second team is within the physical cluster. -/
  second : r.teamB.val < f.teams
  /-- Nonlocal ordinals fit in the endpoint pair's whole demand list. -/
  demand : r.teamA ≠ r.teamB → r.ordinal.val+r.width.val ≤
    Routing.demand width ⟨r.teamA.val, first⟩ ⟨r.teamB.val, second⟩
  /-- Forming an ordinal for any transmitted bit fits in its native word. -/
  word : r.teamA ≠ r.teamB → r.ordinal.val+r.width.val ≤ 2^w

/-- Forming the peer and ordinal registers and then running the complete endpoint-address
routine is safe for any actual bit in the mathematical demand list. -/
theorem endpoint_safe_of_schedule {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    {pub : Arg → Word w} {m : Memory w} (a : Schedule f width pub m) (s : Bank w)
    (peer : Reg) (v : Fin f.teams) (hv : (s peer).val = v.val)
    (hd : f.team ≠ v.val) (hword : (s 15).val+(s 16).val < 2^w)
    (hj : (s 15).val+(s 16).val < Routing.demand width ⟨f.team,a.fit.own⟩ v) :
    (endpoint peer).safeReadOnly w (readings pub) (readings m) (readings s) := by
  let state := Function.update (Function.update (readings s) (30 : Reg) (readings s peer))
    (31 : Reg) (readings s 15+readings s 16)
  have hs30 : state 30 = v.val := by simpa only [state, Function.update_of_ne (by decide : (30 : Reg) ≠ 31),
    Function.update_self] using (show readings s peer = v.val from hv)
  have hs31 : state 31 = (s 15).val+(s 16).val := Function.update_self ..
  have room := endpointLegRoom f a.frame a.fit a.table a.triple a.pair a.capacity v hd _ hj
  have teams := a.frame.2.1
  have endSafe := endpointAddress_safe (readings pub) (readings m) state
    (teams ▸ a.fit.three) ((m ((pub 0).val+1)).isLt) (by rw [hs30,hs31]; exact room)
  change True ∧ addressOpFits w .add (readings s 15) (readings s 16) ∧ _
  exact ⟨trivial, hword, endSafe⟩

private def remote : Role → Prop
  | .sendData | .receiveA | .receiveB => True
  | _ => False

private def peerReg : Role → Reg
  | .receiveB => 9
  | _ => 10

private def peerWord (r : Range w) : Role → Word w
  | .receiveB => r.teamA
  | _ => r.teamB

/-- The real decision tree chooses the opposite endpoint whenever it dispatches a
nonlocal role, including on the data sender and on both orientations of a shared bit. -/
private theorem selected_remote {r : Range w} {self : Word w} {mode : Role}
    (sel : r.selected self = some (some mode)) (hr : remote mode) :
    r.teamA ≠ r.teamB ∧
      ((self = r.teamA ∧ peerWord r mode = r.teamB) ∨ (self = r.teamB ∧ peerWord r mode = r.teamA)) := by
  change (if r.kind = 0 then
    (if self = r.teamA then (if r.teamA = r.teamB then some (some .sharedHere) else some (some .receiveA))
     else (if self = r.teamB then some (some .receiveB) else some none))
    else if r.kind = 1 then
      (if self = r.teamA then (if r.teamA = r.teamB then some (some .dataHere) else some (some .sendData))
       else (if self = r.teamB then some (some .receiveB) else some none))
    else none) = some (some mode) at sel
  split_ifs at sel <;> simp_all [peerWord, remote]
  all_goals (subst mode; simp_all <;> grind)

private theorem peerReg_eq (r : Range w) (mode : Role) (t : Bank w) (hr : rangeBank t = r) :
    t (peerReg mode) = peerWord r mode := by
  cases mode <;> first | exact congrArg Range.teamA hr | exact congrArg Range.teamB hr

/-- Address safety for the bit in register 16 after loading a well-formed descriptor.
No arithmetic or endpoint acceptance premise appears here. -/
theorem Role.addressSafe_of_schedule {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    {pub : Arg → Word w} {m : Memory w} (a : Schedule f width pub m) {r : Range w}
    (span : ScheduledRange f width r) (self : Word w) (hs : self.val = f.team) (mode : Role)
    (sel : r.selected self = some (some mode)) (t : Bank w) (hrow : rangeBank t = r)
    (hj : (t 16).val < r.width.val) : mode.addressSafe pub t m := by
  by_cases rem : remote mode
  · obtain ⟨hne, hends⟩ := selected_remote sel rem
    have hp := peerReg_eq r mode t hrow
    have ho : (t 15).val = r.ordinal.val := congrArg (fun (q : Range w) => q.ordinal.val) hrow
    have hw : (t 15).val+(t 16).val < 2^w := by have := span.word hne; omega
    have sd := span.demand hne
    have ep : (endpoint (peerReg mode)).safeReadOnly w (readings pub) (readings m) (readings t) := by
      rcases hends with ⟨rfl,e⟩ | ⟨rfl,e⟩
      · have hf : (⟨f.team, a.fit.own⟩ : Fin f.teams) = ⟨r.teamA.val, span.first⟩ := Fin.ext hs.symm
        apply endpoint_safe_of_schedule a t (peerReg mode) ⟨r.teamB.val, span.second⟩
          (congrArg Fin.val (hp.trans e)) (hs ▸ Fin.val_ne_of_ne hne) hw
        rw [hf, ho]
        omega
      · have hf : (⟨f.team, a.fit.own⟩ : Fin f.teams) = ⟨r.teamB.val, span.second⟩ := Fin.ext hs.symm
        apply endpoint_safe_of_schedule a t (peerReg mode) ⟨r.teamA.val, span.first⟩
          (congrArg Fin.val (hp.trans e)) (hs ▸ Fin.val_ne_of_ne hne.symm) hw
        rw [hf, ho]
        have symm (u v : Fin f.teams) : Routing.demand width u v = Routing.demand width v u := by
          by_cases he : u = v
          · subst v; rfl
          · simp [Routing.demand, he, Ne.symm he, min_comm u v, max_comm u v]
        rw [symm]
        omega
    cases mode <;> first | exact ep | trivial
  · cases mode <;> simp_all [remote,Role.addressSafe]

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
