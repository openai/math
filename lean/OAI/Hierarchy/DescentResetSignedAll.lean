import OAI.Hierarchy.DescentNextSignedAll
import OAI.Hierarchy.DescentResetNativeWindows
import OAI.Hierarchy.DescentResetWindowFieldRoom

namespace OAI
/-! Publish all successor sockets from the actual two-sided mixed reset parent stencil. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentNextSignedWindow
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
variable {H lanes b bitsW : ℕ}
local notation "gg" => S.groupCount (i+1)
local notation "slots" => 2*(A).cap
local notation "item" => Fin (2*totalLocal B)
local notation "X" => 2^k

def rackOf (entry : B.next.V ↪ Fin H) (v : Fin H) : Option B.next.V :=
  if occupied : ∃h,entry h=v then some occupied.choose else none

theorem rack_present (entry : B.next.V ↪ Fin H) (h:B.next.V) : rackOf B entry (entry h)=some h := by
  have yes : ∃u,entry u=entry h:=⟨h,rfl⟩
  rw [rackOf,dite_eq_left yes,entry.injective yes.choose_spec]

theorem rack_missing (entry : B.next.V ↪ Fin H) (v : Fin H) (missing : ∀h,entry h≠v) :
    rackOf B entry v=none := by simp [rackOf,not_exists.mpr missing]

theorem rack_named (entry : B.next.V ↪ Fin H) (h : Fin H) (v : B.next.V)
    (seen : rackOf B entry h=some v) : entry v=h := by
  unfold rackOf at seen
  split at seen
  next hit=>
    exact (Option.some.inj seen) ▸ hit.choose_spec
  next=>simp at seen

theorem candidate_room (names : Host ↪ ℕ) (rack : Option B.next.V)
    (u : Fin gg) (x : Fin X) (a : item) (j : Fin 8) :
    Native.fields (rack.bind (fun r=>candidateRows B names ((u,r),x) a)) j≤ max ((A).degree+1) ((A).cap+1) :=by
  cases rack with
  | none=>exact Nat.zero_le _
  | some r=>
    change Native.fields (candidateRows B names ((u,r),x) a) j≤_
    unfold candidateRows Roster.rows
    split
    · exact DescentResetWindowFields.record_fields_le ..
    · exact Nat.zero_le _

private theorem bind_scope {V R T I : Type} (rack : Option V) (rows : V → I → Option R)
    (target : V → Option T) (readRow : R → Option T)
    (scope : ∀v, (target v = none → ∀i, (rows v i).bind readRow = none) ∧
      (∀t, target v = some t → ∃i, (rows v i).bind readRow = some t ∧
        ∀l, l ≠ i → (rows v l).bind readRow = none)) :
    ((rack.bind target = none → ∀i, (rack.bind (fun v => rows v i)).bind readRow = none) ∧
      (∀t, rack.bind target = some t → ∃i, (rack.bind (fun v => rows v i)).bind readRow = some t ∧
        ∀l, l ≠ i → (rack.bind (fun v => rows v l)).bind readRow = none)) := by
  cases rack with
  | none => simp
  | some v => exact scope v

theorem native_all (names : Host ↪ ℕ) (rack : Fin H→Option B.next.V) (base : ℕ) (m : Memory bitsW)
    (field : Fin X→item→Fin 8→Expr)
    (early : ∀x a j,(field x a j).Fits bitsW base)
    (authentic : ∀x a j,Source (field x a j) (fun v u=>
      (Native.fields ((rack v).bind (fun r=>candidateRows B names ((u,r),x) a)) j:Cell b)) lanes m)
    (digits : max ((A).degree+1) ((A).cap+1)<2^b)
    (space : Native.All.endAddress base X (A).cap b lanes H gg<2^bitsW) :
    let fields_:=fun x (_ : Fin slots)=>field x
    let done:=Native.All.memory base X (A).degree (A).cap b lanes H gg fields_ m
    (Native.All.program base X (A).degree (A).cap b lanes H gg bitsW fields_).Exec m done
      (Native.All.time base X (A).degree (A).cap b lanes H gg fields_) ∧
    (∀x j,Reads (Native.All.page base X (A).cap b lanes H gg x j) (fun v u=>DescentSignedCableCodec.encode
        ((rack v).bind (fun r=>Stage.signedPanel A ord S B.next.valid names ((u,r),x) j))) lanes done) ∧
    (∀a,a<base ∨ Native.All.endAddress base X (A).cap b lanes H gg≤a→done a=m a) ∧
      CheapCode (Native.All.program base X (A).degree (A).cap b lanes H gg bitsW fields_) := by
  let mounted (x : Fin X) (j : Fin slots) (v : Fin H) (u : Fin gg) :=
    bind_scope (rack v) (fun r => candidateRows B names ((u,r),x))
      (fun r => Stage.signedPanel A ord S B.next.valid names ((u,r),x) j)
      (fun row => read row j) (fun r => candidate_scope B names ((u,r),x) j)
  exact Native.All.run base (fun x _=>field x) m
    (fun x v u a=>(rack v).bind (fun r=>candidateRows B names ((u,r),x) a))
    (fun x j v u=>(rack v).bind (fun r=>Stage.signedPanel A ord S B.next.valid names ((u,r),x) j))
    (fun x _=>early x) (fun x _=>authentic x)
    (fun x v u a j=>(candidate_room B names (rack v) u x a j).trans_lt digits)
    (fun x j v u => (mounted x j v u).1) (fun x j v u => (mounted x j v u).2) space

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
