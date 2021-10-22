module Diag

import Data.Nat

%default total

public export
record Diagram (l : Type) (s : Type) where
  constructor TD
  trel : (l, s) -> List (l, s)
  init : l

stepDia : Diagram l s -> s -> List (l, s)
stepDia (TD trel init) st = trel (init, st)

public export
parDia : Diagram l1 s -> Diagram l2 s -> Diagram (l1, l2) s
parDia (TD tr1 i1) (TD tr2 i2) = TD tr (i1,i2)
  where
  tr : ((l1, l2), s) -> List ((l1, l2), s)
  tr ((lb1, lb2), st) = map (\(lb1',st')=>((lb1',lb2 ),st')) (tr1 (lb1,st)) ++
                        map (\(lb2',st')=>((lb1 ,lb2'),st')) (tr2 (lb2,st))

export
hiHorse : Diagram () Nat
hiHorse = TD (\(lb,st)=>[(lb, S st)]) ()

export
loRoad : Diagram () Nat
loRoad = TD (\(lb,st)=>[(lb, pred st)]) ()