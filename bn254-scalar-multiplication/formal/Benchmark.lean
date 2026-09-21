import Solution

namespace Kriterion.Benchmark

/-- The obligation proves this byte count for every scalar and random tape. -/
def ciphertextBytes (solution : Kriterion.Solution) : Nat := solution.ciphertextBytes

/-- The program type bounds every garbling path. -/
def garbleQueries (solution : Kriterion.Solution) : Nat := solution.garbleQueries

/-- The program type bounds every evaluation path. -/
def evaluateQueries (solution : Kriterion.Solution) : Nat := solution.evaluateQueries

end Kriterion.Benchmark
