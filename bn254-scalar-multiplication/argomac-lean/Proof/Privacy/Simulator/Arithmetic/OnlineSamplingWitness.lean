import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingMemory
import Proof.Privacy.Simulator.Arithmetic.DrawMemory
import Proof.Privacy.Simulator.Arithmetic.WordsAt

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling

/-- Every actual sampler return has one supported typed private coin and its exact stored words. -/
theorem onlineSamplingMemory_witness [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support) :
    ∃ sample ∈ (online.total attempts).law.support,
      final.ram = storeDrawWords (memory.registers 10) 0 memory.ram (onlineWords sample) := by
  have reached : final.ram ∈ ((onlineSamplingMemory attempts memory).map fun result => result.1.ram).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, rfl⟩
  rw [onlineSamplingMemory_source] at reached
  obtain ⟨sample, member, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  exact ⟨sample, member, equality.symm⟩

/-- Every typed private sample occupies exactly the complete online word region. -/
theorem onlineSamplingMemory_words [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support) :
    ∃ sample ∈ (online.total attempts).law.support,
      WordsAt final.ram (memory.registers 10) 0 (onlineWords sample) := by
  obtain ⟨sample, member, equality⟩ := onlineSamplingMemory_witness attempts memory final cost supported
  refine ⟨sample, member, ?_⟩
  intro index inside
  rw [equality]
  exact storeDrawWords_get (memory.registers 10) 0 memory.ram (onlineWords sample)
    index inside (by rw [onlineWords_length]; decide)

end Kriterion.ArgoMAC.ArithmeticSimulator
