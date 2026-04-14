import Cyclic

def main : IO Unit := do
  IO.println s!"swapAdd 3 5 = {swapAdd 3 5}"
  IO.println s!"SCT check: {swapAddGraph.checkSCT}"
