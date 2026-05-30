import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

example : residue Star5 = 5 := by
  unfold residue
  norm_num [Star5, residueAux, havelHakimiStep, Fintype.card_sum]
  decide +kernel

#eval residueAux [5, 1]

end WrittenOnTheWallII.Test
