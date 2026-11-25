import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedMatchInstalled
import OAI.Hierarchy.DescentPackedMatchPrepareROM
import OAI.Hierarchy.DescentPackedMatchPrepareIssued

namespace OAI
/-! # Program labels, registers and slots for the complete packed matcher -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn
open scoped Classical Fin.CommRing
noncomputable section

private theorem columns_names (w n L : ℕ) (es : List Expr) (bound : ∀ e ∈ es, e.work ≤ L)
    (base : ℕ) :
    names (ProtocolRAM.program w (ProbeStage.Native.columns n base es)) ≤
      15 + es.length*(11+4*L) := by
  induction es generalizing base with
  | nil =>
    simp [ProbeStage.Native.columns, ProtocolRAM.program, names_scan, Expr.work]
  | cons e es ih =>
    have head := bound e (List.mem_cons_self ..)
    have tail := ih (fun t ht => bound t (List.mem_cons_of_mem _ ht)) (base+n)
    simp only [ProbeStage.Native.columns, ProtocolRAM.program, Pass.procedure, names_seq,
      names_scan, List.length_cons, Nat.succ_mul] at *
    omega

namespace Local.Gather
variable {N K r D p : ℕ}

theorem all_names (tables : Fin N → DescentPackedZip.Tables) (field : Fin N → Expr)
    (dict : Fin K → Bank) (mask : Bank) (w base H G M : ℕ)
    (bound : ∀ i, (field i).work ≤ 45) :
    names (all w tables field dict mask base H G M) ≤ 15+K*(11+4*(14+N*56)) := by
  have gather := collect_work tables field (List.finRange N) 45 bound
  rw [List.length_finRange] at gather
  have columns := columns_names w (H*chunks G M) (14+N*56) (allExprs tables field dict mask)
    (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      simp only [lookup,Expr.work,assembly]
      omega) base
  simpa only [all,passes,allExprs,List.length_ofFn] using columns

private theorem full_names (w R H G M : ℕ) (g : Banks) (l : ProfileTable.Layout) :
    names (full w R H G M g l) ≤ 472+411*(H*chunks G M+1) := by
  obtain ⟨label,reg,slot⟩ := PackedProfileCursor.size w R l.counts l.cursor.base (H*chunks G M)
  have cursor : names (PackedProfileCursor.program w R l.counts l.cursor.base (H*chunks G M)) ≤
      15+411*(H*chunks G M+1) := by
    unfold names
    omega
  have sumWork : (sumLookup l.countROM l.topology).work=12 := rfl
  simp only [full,physical,DescentSIMDLookup.program,ProfileTable.issue,names_seq,names_scan,
    DescentSIMDLookup.lookup_work,ProfileTable.work,sumWork]
  omega

theorem ROM.machine_names (s : Shape) (d r D p B K H G M unit base seats w : ℕ)
    (field : Fin («fields» r D p) → Expr) (bound : ∀ i, (field i).work ≤ 45) :
    names (ROM.machine s d r D p B K H G M unit base seats w field) ≤
      15*(ROM.size («fields» r D p) K H G M unit+1)+15+
      K*(11+4*(14+«fields» r D p*56))+472+411*((K*H)*chunks G M+1) := by
  let P := ROM.place s d r D p K H G M unit base seats
  let m := ROM.chart s d r D p K H G M (M*s.pairs) unit base P.source
  have gc := all_names m.joins field m.desc m.mask w m.lookup.source.base H G M bound
  have fc := full_names w (M*s.pairs) (K*H) G M m.lookup P.layout
  change names ((ROM.program s d r D p B K H G M (M*s.pairs) unit w base).seq
    ((all w m.joins field m.desc m.mask m.lookup.source.base H G M).seq
     (full w (M*s.pairs) (K*H) G M m.lookup P.layout))) ≤ _
  simp only [names_seq,ROM.program,names_mount]
  omega

end Local.Gather

namespace Local.Stage.Prepared
open DescentPackedColony
variable {k D cap : ℕ}
local notation "r" => 2^k
local notation "p" => 2*cap

/-- The three consecutive pieces of text used by `Prepared.run`. The chart covers
the old inputs; the final texture reads the resulting winner and signed-cable banks. -/
def machine (s : Shape) (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart)
    (ports : Ports D) (wins : Fin r → Bank) (marked : Fin r → Fin p → Bank)
    (romBase base nextBase seats short a K H G M unit w : ℕ) :=
  ((Prepare.ROM.program w romBase k D cap a short M H G).seq
    (ProtocolRAM.program w (Prepare.passes C Z base H G M D))).seq
    (Gather.ROM.machine s short r D p cap K H G M unit nextBase seats w
      (Gather.expr wins marked ports H))

def hardware (k D cap a K H G M unit : ℕ) :=
  15*(Prepare.staticWords k D cap a M H G+1) +
  (26+400*(D+1)^3+(2^k+2^k*(2*cap))*111) +
  (15*(Gather.ROM.size («fields» (2^k) D (2*cap)) K H G M unit+1)+15+
    K*(11+4*(14+«fields» (2^k) D (2*cap)*56))+472+411*((K*H)*chunks G M+1))

/-- The two physically populated dictionaries, all column-gather passes, the nonlinear
matching lookup and the quotient/remainder profile cursor are included. -/
theorem machine_names (s : Shape) (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart)
    (ports : Ports D) (wins : Fin r → Bank) (marked : Fin r → Fin p → Bank)
    (romBase base nextBase seats short a K H G M unit w : ℕ) :
    names (machine s C Z ports wins marked romBase base nextBase seats short a K H G M unit w) ≤
      hardware k D cap a K H G M unit := by
  have prep := Prepare.code_names (D:=D) C Z base H G M w
  have matcher := Gather.ROM.machine_names s short r D p cap K H G M unit nextBase seats w
    (Gather.expr wins marked ports H) (Gather.terrain_work wins marked ports H)
  simpa only [machine,hardware,names_seq,Prepare.ROM.code_names] using
    Nat.add_le_add (Nat.add_le_add_left prep (15*(Prepare.staticWords k D cap a M H G+1))) matcher

/-- The volume contains the fixed half-word address space, the host roster and
the sold packed rows. The inequality also holds when the row bank is empty. -/
theorem hardware_le (k D cap a K H G M unit dataWidth volume : ℕ)
    (oldFlags : ((1*2^k)+a)*M ≤ dataWidth/2)
    (oldWire : DescentSignedCableCodec.width D cap*M ≤ dataWidth/2)
    (keys : unit*M ≤ dataWidth/2)
    (page : 2^(dataWidth/2) ≤ volume) (hosts : H ≤ volume)
    (packed : H*chunks G M ≤ volume) :
    hardware k D cap a K H G M unit ≤ namesPerWord k D cap K*volume := by
  let n := «fields» (2^k) D (2*cap)
  have one : 1 ≤ volume := Nat.one_le_two_pow.trans page
  have flag : 2^((1*2^k)*M) ≤ volume := by
    exact (Nat.pow_le_pow_right (by decide : 0 < 2)
      ((Nat.mul_le_mul_right M (Nat.le_add_right _ a)).trans oldFlags)).trans page
  have truth : 2^((1*2^k+a)*M) ≤ volume :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) oldFlags).trans page
  have chip : 2^(DescentSignedCableCodec.width D cap*M) ≤ volume :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) oldWire).trans page
  have dict : Gather.ROM.pitch unit M ≤ volume :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) keys).trans page
  have prep : Prepare.staticWords k D cap a M H G+1 ≤ (4+2^k+2*D)*volume := by
    unfold Prepare.staticWords
    calc
      _ ≤ volume+2^k*volume+volume+volume+2*volume*D+volume := by gcongr
      _ = _ := by ring
  have number : (K*H)*chunks G M ≤ K*volume := by rw [Nat.mul_assoc]; gcongr
  have mount : Gather.ROM.size n K H G M unit+1 ≤ (((1+n)+(K+6))+1+K+1)*volume := by
    unfold Gather.ROM.size
    calc
      _ ≤ ((1+n)+(K+6))*volume+volume+K*volume+volume := by gcongr
      _ = _ := by ring
  have cursor : (K*H)*chunks G M+1 ≤ (K+1)*volume := by
    calc
      _ ≤ K*volume+volume := Nat.add_le_add number one
      _ = _ := by ring
  have scaled (b : ℕ) : b ≤ b*volume := Nat.le_mul_of_pos_right b one
  change 15*(Prepare.staticWords k D cap a M H G+1)+
    (26+400*(D+1)^3+(2^k+2^k*(2*cap))*111)+
    (15*(Gather.ROM.size n K H G M unit+1)+15+
    K*(11+4*(14+n*56))+472+411*((K*H)*chunks G M+1)) ≤ _
  calc
    _ ≤ 15*((4+2^k+2*D)*volume)+(26+400*(D+1)^3+(2^k+2^k*(2*cap))*111)*volume+
      (15*((((1+n)+(K+6))+1+K+1)*volume)+15*volume+
       (K*(11+4*(14+n*56)))*volume+472*volume+411*((K+1)*volume)) := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 15 prep) (scaled _))
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_left 15 mount) (scaled _)) (scaled _)) (scaled _))
          (Nat.mul_le_mul_left 411 cursor))
    _ = _ := by dsimp only [namesPerWord,n]; ring

end Local.Stage.Prepared

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
