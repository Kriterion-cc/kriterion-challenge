import Init.System.IO

def main : IO UInt32 := do
  let tests ← IO.Process.spawn { cmd := "lake", args := #["build", "Kriterion", "Tests"] }
  let status ← tests.wait
  if status != 0 then return status
  let process ← IO.Process.spawn { cmd := "python3", args := #["tests/check_baseline.py"] }
  process.wait
