import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph

#check SimpleGraph.residueAux
#print SimpleGraph.residueAux
#check SimpleGraph.havelHakimiStep

example : SimpleGraph.havelHakimiStep [5, 1, 1, 1, 1, 1] = [0, 0, 0, 0, 0] := by
  native_decide

example : SimpleGraph.residueAux [5, 1, 1, 1, 1, 1] = 5 := by
  native_decide
