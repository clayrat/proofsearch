module GCL

import Data.Maybe
import Data.List
import Diag

%default total

mutual
  public export
  data GCL : Type -> Type where
    If     : List (Guard s) -> GCL s
    Seq    : GCL s -> GCL s -> GCL s
    Do     : List (Guard s) -> GCL s
    Update : (s -> s) -> GCL s
    Skip   : GCL s

  public export
  Pred : Type -> Type
  Pred s = (st : s) -> Bool

  public export
  data Guard : Type -> Type where
    MkGuard : Pred s -> GCL s -> Guard s

Uninhabited (If gs = Skip) where
  uninhabited Refl impossible

Uninhabited (Seq c1 c2 = Skip) where
  uninhabited Refl impossible

Uninhabited (Do gs = Skip) where
  uninhabited Refl impossible

Uninhabited (Update f = Skip) where
  uninhabited Refl impossible

isSkip : (c : GCL s) -> Dec (c = Skip)
isSkip (If _)     = No absurd
isSkip (Seq _ _)  = No absurd
isSkip (Do _)     = No absurd
isSkip (Update _) = No absurd
isSkip  Skip      = Yes Refl

ops : (GCL s, s) -> List (GCL s, s)
ops (Skip      , st) = []
ops (Update u  , st) = [(Skip, u st)]
ops (Seq Skip y, st) = [(y, st)]
-- TODO termination checker for pairs?
ops (Seq x y   , st) = (\(x,st) => (Seq x y, st)) <$> (assert_total $ ops (x, st))
ops (If xs     , st) = mapMaybe (\(MkGuard g x) => toMaybe (g st) (x, st)) xs
ops (Do xs     , st) = case mapMaybe (\(MkGuard g x) => toMaybe (g st) (Seq x (Do xs), st)) xs of
                         [] => [(Skip, st)]
                         ys => ys

public export
toDiag : GCL s -> Diagram (GCL s) s
toDiag p = TD ops p

public export
await : Pred s -> GCL s
await g = If [MkGuard g Skip]

while : Pred s -> GCL s -> GCL s
while g x = Do [MkGuard g x]

ifThenElse : Pred s -> GCL s -> GCL s -> GCL s
ifThenElse g x y = If [MkGuard g x, MkGuard (not . g) y]
